use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

use crate::config::Config;
use crate::prover::claude;
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

    // 2. Load strategy
    let strategy = if let Some(name) = strategy_name {
        loader::load_strategy(name)?
    } else {
        loader::auto_select_by_kind("parse")
            .context("No parse strategy found. Ensure the parse-proof builtin is available.")?
    };

    // 3. Render prompt
    let vars = ParseStrategyVars {
        proof_script: proof_script.clone(),
        conjecture_title: conj_title,
        lemma_statement: lemma_stmt,
        prover: prover.clone(),
    };
    let prompt = loader::render_parse_strategy(&strategy, &vars);

    // 4. Call Claude
    println!("{}", "Generating exposition...".cyan());
    let claude_tool = crate::tools::registry::require_tool("claude").ok();

    let (response, cost) = if claude_tool.is_some() {
        match claude::try_claude_cli(&prompt, &cfg.api.model) {
            Ok(r) => r,
            Err(_) => {
                claude::try_api_fallback(&prompt, &cfg.api.anthropic_api_key, &cfg.api.model)
                    .await?
            }
        }
    } else {
        claude::try_api_fallback(&prompt, &cfg.api.anthropic_api_key, &cfg.api.model).await?
    };

    let explanation = response.trim().to_string();

    // 5. Print colored explanation
    println!();
    println!("{}", "═".repeat(60).dimmed());
    println!("{}", " Proof Exposition".bold());
    println!("{}", "═".repeat(60).dimmed());
    println!();
    println!("{}", explanation);
    println!();
    println!("{}", "─".repeat(60).dimmed());
    println!(
        "  Strategy: {}  |  Cost: ${:.4}  |  Prover: {}",
        strategy.meta.name.cyan(),
        cost,
        prover.yellow()
    );
    println!("{}", "─".repeat(60).dimmed());

    Ok(())
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
