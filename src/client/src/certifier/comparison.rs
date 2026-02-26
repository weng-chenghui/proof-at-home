use anyhow::{Context, Result};
use chrono::Utc;
use serde::Deserialize;
use std::collections::HashMap;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::certifier::types::*;
use crate::config::Config;
use crate::strategy_store::loader::{self, CertifyCommandVars};

/// Build the comparison prompt for a single conjecture.
/// Loads from command files if available, falls back to inline prompt.
pub fn build_comparison_prompt(
    conjecture_title: &str,
    prover: &str,
    proofs: &[(String, String, String)], // (contributor_contribution_id, contributor_username, proof_script)
    command_name: Option<&str>,
) -> String {
    let proofs_block = build_proofs_block(proofs);

    // Try loading from command file
    let command_result = if let Some(name) = command_name {
        loader::load_command(name)
    } else {
        loader::auto_select_by_kind("certify-compare")
    };

    if let Ok(command) = command_result {
        let vars = CertifyCommandVars {
            prover: prover.to_string(),
            conjecture_title: conjecture_title.to_string(),
            proofs: proofs_block.clone(),
            package_rankings: String::new(),
        };
        return loader::render_certify_command(&command, &vars);
    }

    // Fallback: inline prompt
    build_inline_comparison_prompt(conjecture_title, prover, &proofs_block)
}

/// Format proof scripts into a block for template substitution.
fn build_proofs_block(proofs: &[(String, String, String)]) -> String {
    let mut block = String::new();
    for (contribution_id, username, script) in proofs {
        block.push_str(&format!(
            "\n### Contributor: {} (contribution: {})\n```\n{}\n```\n",
            username, contribution_id, script
        ));
    }
    block
}

/// Fallback inline comparison prompt.
fn build_inline_comparison_prompt(
    conjecture_title: &str,
    prover: &str,
    proofs_block: &str,
) -> String {
    format!(
        "You are a {} proof certifier. Compare the following proofs of \"{}\" \
         from different contributors.\n\n## Proofs\n{}\n\
## Scoring Criteria (1-10 each)\n\n\
1. **Succinctness**: Shorter, cleaner proofs score higher. Avoid unnecessary steps.\n\
2. **Library reuse**: Good use of existing library lemmas (e.g., mathlib, mathcomp) rather than reinventing.\n\
3. **Generality**: A general result usable elsewhere scores higher than an overly specific one.\n\
4. **Modularity**: Decomposition into reusable lemmas, HB.mixin, structures, or typeclasses.\n\
5. **Math strategy**: Elegance and superiority of the mathematical approach (e.g., choosing induction vs case analysis vs contradiction).\n\
6. **Overall**: Weighted combination reflecting overall proof quality.\n\n\
## Output format\n\n\
Return valid JSON and nothing else (no markdown fences):\n\
{{\n  \"rankings\": [\n    {{\n      \"contributor_contribution_id\": \"...\",\n      \
\"contributor_username\": \"...\",\n      \"scores\": {{ \"succinctness\": N, \"library_reuse\": N, \
\"generality\": N, \"modularity\": N, \"math_strategy\": N, \"overall\": N }},\n      \
\"reasoning\": \"1-2 sentence explanation\"\n    }}\n  ],\n  \
\"analysis\": \"2-3 sentence overall comparison\"\n}}\n",
        prover, conjecture_title, proofs_block
    )
}

/// Build a rollup summary prompt given per-conjecture results.
/// Loads from command files if available, falls back to inline prompt.
pub fn build_rollup_prompt(
    package_rankings: &[PackageRanking],
    command_name: Option<&str>,
) -> String {
    let rankings_block = build_rankings_block(package_rankings);

    // Try loading from command file
    let command_result = if let Some(name) = command_name {
        loader::load_command(name)
    } else {
        loader::auto_select_by_kind("certify-rollup")
    };

    if let Ok(command) = command_result {
        let vars = CertifyCommandVars {
            prover: String::new(),
            conjecture_title: String::new(),
            proofs: String::new(),
            package_rankings: rankings_block.clone(),
        };
        return loader::render_certify_command(&command, &vars);
    }

    // Fallback: inline prompt
    build_inline_rollup_prompt(&rankings_block)
}

/// Format package rankings into a block for template substitution.
fn build_rankings_block(package_rankings: &[PackageRanking]) -> String {
    let mut block = String::new();
    for pr in package_rankings {
        block.push_str(&format!(
            "### {} (contribution: {}) — Rank #{}\n\
             - Succinctness: {}, Library Reuse: {}, Generality: {}, Modularity: {}, Math Strategy: {}, Overall: {}\n\
             - Conjectures compared: {}\n\n",
            pr.contributor_username,
            pr.contributor_contribution_id,
            pr.rank,
            pr.avg_scores.succinctness,
            pr.avg_scores.library_reuse,
            pr.avg_scores.generality,
            pr.avg_scores.modularity,
            pr.avg_scores.math_strategy,
            pr.avg_scores.overall,
            pr.conjectures_compared,
        ));
    }
    block
}

/// Fallback inline rollup prompt.
fn build_inline_rollup_prompt(rankings_block: &str) -> String {
    format!(
        "You are a proof certifier. Given the following package-level score averages across \
         all compared conjectures, write a brief narrative summary (2-3 sentences) for each contributor \
         and a final overall ranking explanation.\n\n## Package Rankings\n\n{}\
         Return valid JSON and nothing else (no markdown fences):\n\
         {{\n  \"summaries\": [\n    {{ \"contributor_contribution_id\": \"...\", \"summary\": \"...\" }}\n  ]\n}}\n",
        rankings_block
    )
}

// ── Claude API calling (duplicated from prover/claude.rs to keep scope small) ──

const PRICING: &[(&str, f64, f64)] = &[
    ("claude-opus-4", 15.0, 75.0),
    ("claude-sonnet-4", 3.0, 15.0),
    ("claude-haiku-4", 0.80, 4.0),
    ("claude-3-5-sonnet", 3.0, 15.0),
    ("claude-3-5-haiku", 0.80, 4.0),
];

fn estimate_cost_from_tokens(model: &str, input_tokens: u64, output_tokens: u64) -> f64 {
    let (input_rate, output_rate) = PRICING
        .iter()
        .find(|(prefix, _, _)| model.starts_with(prefix))
        .map(|(_, i, o)| (*i, *o))
        .unwrap_or((3.0, 15.0));
    (input_tokens as f64 * input_rate + output_tokens as f64 * output_rate) / 1_000_000.0
}

#[derive(Deserialize, Default)]
struct ClaudeCliResponse {
    #[serde(default)]
    result: String,
    #[serde(default)]
    cost_usd: Option<f64>,
    #[serde(default)]
    usage: Option<ClaudeUsage>,
    #[serde(default)]
    model: Option<String>,
}

#[derive(Deserialize, Default)]
struct ClaudeUsage {
    #[serde(default)]
    input_tokens: u64,
    #[serde(default)]
    output_tokens: u64,
}

#[derive(Deserialize)]
struct ApiResponse {
    content: Vec<ApiContentBlock>,
    usage: ApiUsage,
    model: String,
}

#[derive(Deserialize)]
struct ApiContentBlock {
    #[serde(default)]
    text: String,
}

#[derive(Deserialize)]
struct ApiUsage {
    input_tokens: u64,
    output_tokens: u64,
}

fn try_claude_cli(prompt: &str, model: &str) -> Result<(String, f64)> {
    let output = Command::new("claude")
        .args([
            "-p",
            prompt,
            "--output-format",
            "json",
            "--max-turns",
            "1",
            "--model",
            model,
        ])
        .output()
        .context("Failed to invoke claude CLI")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("claude CLI failed: {}", stderr);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let resp: ClaudeCliResponse =
        serde_json::from_str(&stdout).context("Failed to parse claude CLI JSON output")?;

    let cost = resp.cost_usd.unwrap_or_else(|| {
        if let Some(usage) = &resp.usage {
            let m = resp.model.as_deref().unwrap_or(model);
            estimate_cost_from_tokens(m, usage.input_tokens, usage.output_tokens)
        } else {
            0.0
        }
    });

    Ok((resp.result, cost))
}

async fn try_api_fallback(prompt: &str, api_key: &str, model: &str) -> Result<(String, f64)> {
    let client = reqwest::Client::new();
    let body = serde_json::json!({
        "model": model,
        "max_tokens": 4096,
        "messages": [
            {"role": "user", "content": prompt}
        ]
    });

    let resp = client
        .post("https://api.anthropic.com/v1/messages")
        .header("x-api-key", api_key)
        .header("anthropic-version", "2023-06-01")
        .header("content-type", "application/json")
        .json(&body)
        .send()
        .await
        .context("Failed to call Anthropic API")?;

    if !resp.status().is_success() {
        let status = resp.status();
        let body = resp.text().await.unwrap_or_default();
        anyhow::bail!("Anthropic API error ({}): {}", status, body);
    }

    let api_resp: ApiResponse = resp.json().await.context("Failed to parse API response")?;
    let text = api_resp
        .content
        .first()
        .map(|b| b.text.clone())
        .unwrap_or_default();

    let cost = estimate_cost_from_tokens(
        &api_resp.model,
        api_resp.usage.input_tokens,
        api_resp.usage.output_tokens,
    );

    Ok((text, cost))
}

/// Call Claude (CLI first, API fallback) and return (response_text, cost)
pub async fn call_claude(config: &Config, prompt: &str) -> Result<(String, f64)> {
    let cli_available = Command::new("claude")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);

    if cli_available {
        match try_claude_cli(prompt, &config.api.model) {
            Ok(r) => Ok(r),
            Err(_) => {
                try_api_fallback(prompt, &config.api.anthropic_api_key, &config.api.model).await
            }
        }
    } else {
        try_api_fallback(prompt, &config.api.anthropic_api_key, &config.api.model).await
    }
}

// ── Audit logger for certification comparisons ──

pub struct CertificationAuditLogger {
    path: PathBuf,
}

impl CertificationAuditLogger {
    pub fn new(certification_dir: &Path) -> Self {
        Self {
            path: certification_dir.join("certification_audit.jsonl"),
        }
    }

    pub fn log(&self, entry: &CertificationAuditEntry) {
        if let Ok(line) = serde_json::to_string(entry) {
            if let Ok(mut f) = OpenOptions::new()
                .create(true)
                .append(true)
                .open(&self.path)
            {
                let _ = writeln!(f, "{}", line);
            }
        }
    }
}

#[derive(serde::Serialize)]
pub struct CertificationAuditEntry {
    pub timestamp: String,
    pub action: String,
    pub conjecture_id: String,
    pub model: String,
    pub cost_usd: f64,
    pub provers_compared: u32,
}

// ── AI comparison response parsing ──

#[derive(Deserialize)]
struct ComparisonResponse {
    rankings: Vec<ComparisonRanking>,
    analysis: String,
}

#[derive(Deserialize)]
struct ComparisonRanking {
    contributor_contribution_id: String,
    contributor_username: String,
    scores: ComparisonScores,
    reasoning: String,
}

#[derive(Deserialize)]
struct ComparisonScores {
    succinctness: u8,
    library_reuse: u8,
    generality: u8,
    modularity: u8,
    math_strategy: u8,
    overall: u8,
}

#[derive(Deserialize)]
struct RollupResponse {
    summaries: Vec<RollupSummary>,
}

#[derive(Deserialize)]
struct RollupSummary {
    contributor_contribution_id: String,
    summary: String,
}

/// Extract JSON from a response that may have markdown fences
fn extract_json(response: &str) -> &str {
    let trimmed = response.trim();
    if let Some(start) = trimmed.find("```") {
        let after_fence = &trimmed[start + 3..];
        let code_start = after_fence.find('\n').map(|i| i + 1).unwrap_or(0);
        let code_body = &after_fence[code_start..];
        if let Some(end) = code_body.find("```") {
            return code_body[..end].trim();
        }
    }
    trimmed
}

/// Run the full AI comparison pipeline.
/// `command_name` selects a specific comparison command; None auto-selects.
pub async fn run_comparison(
    config: &Config,
    state: &CertificationState,
    certification_dir: &Path,
    command_name: Option<&str>,
) -> Result<ComparisonResult> {
    let audit = CertificationAuditLogger::new(certification_dir);
    let packages_dir = certification_dir.join("packages");
    let mut total_cost = 0.0;

    // Collect all proof files per conjecture per prover
    // Map: conjecture_id -> Vec<(contribution_id, username, script)>
    let mut conjecture_proofs: HashMap<String, Vec<(String, String, String)>> = HashMap::new();
    // Track conjecture titles: conjecture_id -> title (use filename as fallback)
    let mut conjecture_titles: HashMap<String, String> = HashMap::new();
    // Detect prover from file extensions
    let mut prover = String::from("Rocq");

    for pkg in &state.packages {
        let pkg_dir = packages_dir.join(&pkg.contributor_contribution_id);
        if !pkg_dir.exists() {
            continue;
        }

        if pkg.prover.to_lowercase().contains("lean") {
            prover = String::from("Lean 4");
        }

        for pid in &pkg.conjecture_ids {
            // Try to find the proof file: {pid}.v or {pid}.lean
            let v_file = pkg_dir.join(format!("{}.v", pid));
            let lean_file = pkg_dir.join(format!("{}.lean", pid));
            let proof_path = if v_file.exists() {
                v_file
            } else if lean_file.exists() {
                lean_file
            } else {
                continue;
            };

            let script = std::fs::read_to_string(&proof_path)
                .with_context(|| format!("Failed to read {}", proof_path.display()))?;

            conjecture_proofs.entry(pid.clone()).or_default().push((
                pkg.contributor_contribution_id.clone(),
                pkg.contributor_username.clone(),
                script,
            ));

            conjecture_titles
                .entry(pid.clone())
                .or_insert_with(|| pid.clone());
        }
    }

    // Filter to conjectures with 2+ provers
    let comparable: Vec<_> = conjecture_proofs
        .iter()
        .filter(|(_, proofs)| proofs.len() >= 2)
        .collect();

    if comparable.is_empty() {
        anyhow::bail!(
            "No conjectures have proofs from 2+ provers. Import more packages to enable comparison."
        );
    }

    println!(
        "Comparing {} conjectures across provers...",
        comparable.len()
    );

    let mut conjecture_comparisons = Vec::new();

    for (conjecture_id, proofs) in &comparable {
        let title = conjecture_titles
            .get(*conjecture_id)
            .cloned()
            .unwrap_or_else(|| (*conjecture_id).clone());

        let prompt = build_comparison_prompt(&title, &prover, proofs, command_name);
        println!(
            "  Comparing conjecture: {} ({} provers)",
            title,
            proofs.len()
        );

        let (response, cost) = call_claude(config, &prompt).await?;
        total_cost += cost;

        audit.log(&CertificationAuditEntry {
            timestamp: Utc::now().to_rfc3339(),
            action: "conjecture_comparison".into(),
            conjecture_id: (*conjecture_id).clone(),
            model: config.api.model.clone(),
            cost_usd: cost,
            provers_compared: proofs.len() as u32,
        });

        let json_str = extract_json(&response);
        let parsed: ComparisonResponse =
            serde_json::from_str(json_str).context("Failed to parse AI comparison JSON")?;

        let rankings: Vec<CertificateRanking> = parsed
            .rankings
            .into_iter()
            .map(|r| CertificateRanking {
                contributor_contribution_id: r.contributor_contribution_id,
                contributor_username: r.contributor_username,
                scores: CertificateScores {
                    succinctness: r.scores.succinctness,
                    library_reuse: r.scores.library_reuse,
                    generality: r.scores.generality,
                    modularity: r.scores.modularity,
                    math_strategy: r.scores.math_strategy,
                    overall: r.scores.overall,
                },
                reasoning: r.reasoning,
            })
            .collect();

        conjecture_comparisons.push(ConjectureComparison {
            conjecture_id: (*conjecture_id).clone(),
            conjecture_title: title,
            rankings,
            analysis: parsed.analysis,
        });
    }

    // Compute package-level averages programmatically
    let mut prover_scores: HashMap<String, (String, Vec<&CertificateScores>)> = HashMap::new();
    for pc in &conjecture_comparisons {
        for ranking in &pc.rankings {
            prover_scores
                .entry(ranking.contributor_contribution_id.clone())
                .or_insert_with(|| (ranking.contributor_username.clone(), Vec::new()))
                .1
                .push(&ranking.scores);
        }
    }

    let mut package_rankings: Vec<PackageRanking> = prover_scores
        .into_iter()
        .map(|(contribution_id, (username, scores))| {
            let n = scores.len() as u32;
            let avg = CertificateScores::average_with(&scores);
            PackageRanking {
                contributor_contribution_id: contribution_id,
                contributor_username: username,
                avg_scores: avg,
                conjectures_compared: n,
                rank: 0,                // filled below
                summary: String::new(), // filled by AI rollup
            }
        })
        .collect();

    // Sort by overall desc, assign ranks
    package_rankings.sort_by(|a, b| b.avg_scores.overall.cmp(&a.avg_scores.overall));
    for (i, pr) in package_rankings.iter_mut().enumerate() {
        pr.rank = (i + 1) as u32;
    }

    // Ask AI for narrative summaries
    if !package_rankings.is_empty() {
        let rollup_prompt = build_rollup_prompt(&package_rankings, command_name);
        let (rollup_response, rollup_cost) = call_claude(config, &rollup_prompt).await?;
        total_cost += rollup_cost;

        audit.log(&CertificationAuditEntry {
            timestamp: Utc::now().to_rfc3339(),
            action: "rollup_summary".into(),
            conjecture_id: String::new(),
            model: config.api.model.clone(),
            cost_usd: rollup_cost,
            provers_compared: package_rankings.len() as u32,
        });

        let json_str = extract_json(&rollup_response);
        if let Ok(rollup) = serde_json::from_str::<RollupResponse>(json_str) {
            for s in rollup.summaries {
                if let Some(pr) = package_rankings
                    .iter_mut()
                    .find(|p| p.contributor_contribution_id == s.contributor_contribution_id)
                {
                    pr.summary = s.summary;
                }
            }
        }
    }

    let result = ComparisonResult {
        timestamp: Utc::now().to_rfc3339(),
        model: config.api.model.clone(),
        cost_usd: total_cost,
        conjecture_comparisons,
        package_rankings,
    };

    Ok(result)
}
