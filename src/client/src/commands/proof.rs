use anyhow::{Context, Result};
use colored::Colorize;
use std::path::{Path, PathBuf};

use crate::config::Config;
use crate::proof_tree;
use crate::server_client::api::ServerClient;
use crate::strategy_store::loader::{self, ParseStrategyVars};

pub async fn cmd_list(contribution_id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let proofs = client.fetch_proofs(contribution_id).await?;

    if proofs.is_empty() {
        println!("No proofs found for contribution {}.", contribution_id);
        return Ok(());
    }

    println!(
        "{:<40} {:<20} {:<10} {:<10} {:<10}",
        "Conjecture ID", "Username", "Success", "Attempts", "Cost"
    );
    println!("{}", "-".repeat(90));

    for p in &proofs {
        let display_id = if p.conjecture_id.len() > 36 {
            &p.conjecture_id[..36]
        } else {
            &p.conjecture_id
        };
        let success_str = if p.success {
            "✓".green().to_string()
        } else {
            "✗".red().to_string()
        };
        println!(
            "{:<40} {:<20} {:<10} {:<10} ${:<9.4}",
            display_id, p.username, success_str, p.attempts, p.cost_usd
        );
    }

    println!("\nTotal: {}", proofs.len());
    Ok(())
}

/// Infer prover name from file extension.
pub fn infer_prover_from_extension(path: &str) -> &str {
    if path.ends_with(".lean") {
        "lean4"
    } else if path.ends_with(".v") {
        "rocq"
    } else {
        "unknown"
    }
}

/// Parse a proof file and produce a human-readable explanation.
pub async fn cmd_parse(
    proof_file: Option<&str>,
    contribution_id: Option<&str>,
    conjecture_id: Option<&str>,
    strategy_name: Option<&str>,
    format: &str,
    output: Option<&str>,
) -> Result<()> {
    let cfg = Config::load_or_default();

    // 1. Resolve proof script
    let (proof_script, prover, conj_title, lemma_stmt) = if let Some(file_path) = proof_file {
        // Local file mode
        let script = std::fs::read_to_string(file_path)
            .with_context(|| format!("Failed to read proof file: {}", file_path))?;
        let prover = infer_prover_from_extension(file_path).to_string();
        let filename = Path::new(file_path)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");
        (script, prover, filename.to_string(), String::new())
    } else if let (Some(contrib_id), Some(conj_id)) = (contribution_id, conjecture_id) {
        // Server mode — fetch proof from contribution
        cfg.require_login()?;
        let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
        let proofs = client.fetch_proofs(contrib_id).await?;
        let proof = proofs
            .into_iter()
            .find(|p| p.conjecture_id == conj_id)
            .with_context(|| {
                format!(
                    "No proof found for conjecture {} in contribution {}",
                    conj_id, contrib_id
                )
            })?;

        // Try to fetch conjecture metadata for context
        let (title, lemma) = match client.fetch_conjecture(conj_id).await {
            Ok(c) => (c.title, c.lemma_statement),
            Err(_) => (conj_id.to_string(), String::new()),
        };

        (proof.proof_script, "unknown".to_string(), title, lemma)
    } else {
        anyhow::bail!(
            "Provide either a proof file path or both --contribution and --conjecture flags.\n\
             Usage:\n  pah proof parse <proof_file>\n  pah proof parse --contribution <id> --conjecture <id>"
        );
    };

    // 2. Load strategy (auto-select based on format)
    let strategy = if let Some(name) = strategy_name {
        loader::load_strategy(name)?
    } else {
        let kind = match format {
            "tree" => "parse-tree",
            _ => "parse",
        };
        loader::auto_select_by_kind(kind).with_context(|| {
            format!(
                "No strategy found for kind '{}'. Ensure builtins are available.",
                kind
            )
        })?
    };

    // 3. Render prompt
    let vars = ParseStrategyVars {
        proof_script: proof_script.clone(),
        conjecture_title: conj_title.clone(),
        lemma_statement: lemma_stmt,
        prover: prover.clone(),
    };
    let prompt = loader::render_parse_strategy(&strategy, &vars);

    // 4. Call AI provider
    let progress_msg = match format {
        "tree" => "Generating proof tree...",
        _ => "Generating exposition...",
    };
    println!("{}", progress_msg.cyan());
    let provider = crate::ai::create_provider(&cfg)?;
    let model = cfg.model();
    let max_tokens: u32 = if format == "tree" { 8192 } else { 4096 };
    let ai_response = provider.complete(&prompt, &model, max_tokens).await?;
    let cost = ai_response.cost_usd;
    let response_text = ai_response.text.trim().to_string();

    // 5. Output based on format
    match format {
        "tree" => {
            let default_name = format!("{}-proof-tree.html", sanitize_filename(&conj_title));
            let output_path = PathBuf::from(output.unwrap_or(&default_name));

            proof_tree::build_from_response(&response_text, &output_path)?;

            println!();
            println!("{}", "═".repeat(60).dimmed());
            println!("{}", " Proof Tree Generated".bold());
            println!("{}", "═".repeat(60).dimmed());
            println!();
            println!("  Output: {}", output_path.display().to_string().green());
            println!("  Open in browser to view the interactive proof tree.");
            println!();
            println!("{}", "─".repeat(60).dimmed());
            println!(
                "  Strategy: {}  |  Cost: ${:.4}  |  Prover: {}",
                strategy.meta.name.cyan(),
                cost,
                prover.yellow()
            );
            println!("{}", "─".repeat(60).dimmed());
        }
        _ => {
            // Default text format
            println!();
            println!("{}", "═".repeat(60).dimmed());
            println!("{}", " Proof Exposition".bold());
            println!("{}", "═".repeat(60).dimmed());
            println!();
            println!("{}", response_text);
            println!();
            println!("{}", "─".repeat(60).dimmed());
            println!(
                "  Strategy: {}  |  Cost: ${:.4}  |  Prover: {}",
                strategy.meta.name.cyan(),
                cost,
                prover.yellow()
            );
            println!("{}", "─".repeat(60).dimmed());
        }
    }

    Ok(())
}

/// Sanitize a string for use as a filename.
fn sanitize_filename(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect::<String>()
        .to_lowercase()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_prover_from_extension() {
        assert_eq!(infer_prover_from_extension("proof.v"), "rocq");
        assert_eq!(infer_prover_from_extension("proof.lean"), "lean4");
        assert_eq!(infer_prover_from_extension("/path/to/my_proof.v"), "rocq");
        assert_eq!(
            infer_prover_from_extension("/path/to/my_proof.lean"),
            "lean4"
        );
        assert_eq!(infer_prover_from_extension("proof.txt"), "unknown");
        assert_eq!(infer_prover_from_extension("noext"), "unknown");
    }
}
