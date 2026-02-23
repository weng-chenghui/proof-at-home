use anyhow::{Context, Result};
use chrono::Utc;
use serde::{Deserialize, Serialize};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::config::Config;
use crate::prover::env_manager::ResolvedEnv;
use crate::prover::verifier;
use crate::server_client::api::Conjecture;

pub struct AuditLogger {
    path: PathBuf,
}

impl AuditLogger {
    pub fn new(session_dir: &Path) -> Self {
        Self {
            path: session_dir.join("proof_audit.jsonl"),
        }
    }

    pub fn log_attempt(&self, entry: &AuditEntry) {
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

#[derive(Serialize)]
pub struct AuditEntry {
    pub timestamp: String,
    pub conjecture_id: String,
    pub conjecture_title: String,
    pub attempt: u32,
    pub max_attempts: u32,
    pub model: String,
    pub cost_usd: f64,
    pub success: bool,
    pub error_snippet: String,
}

/// Result of a proof attempt
#[derive(Debug)]
pub struct ProofAttemptResult {
    pub success: bool,
    pub proof_script: String,
    pub cost_usd: f64,
    pub attempts: u32,
    pub error_output: String,
}

/// Token-to-USD pricing table (per million tokens)
const PRICING: &[(&str, f64, f64)] = &[
    // (model_prefix, input_per_M, output_per_M)
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
        .unwrap_or((3.0, 15.0)); // default to sonnet pricing

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

/// Build the prompt for proving a lemma
fn build_proof_prompt(conjecture: &Conjecture) -> String {
    let assistant_name = match conjecture.prover.to_lowercase().as_str() {
        "lean" | "lean4" => "Lean 4",
        _ => "Rocq",
    };

    let hints_text = if conjecture.hints.is_empty() {
        String::new()
    } else {
        format!(
            "\n\nHints:\n{}",
            conjecture
                .hints
                .iter()
                .map(|h| format!("- {}", h))
                .collect::<Vec<_>>()
                .join("\n")
        )
    };

    format!(
        r#"You are a {assistant} theorem prover. Your task is to produce a complete, \
self-contained proof script that compiles successfully.

## Problem: {title}

### Preamble (imports/setup):
```
{preamble}
```

### Lemma to prove:
```
{statement}
```
{hints}

### Skeleton (if provided):
```
{skeleton}
```

## Instructions

1. Output ONLY the complete proof script (preamble + lemma + proof), nothing else.
2. The script must compile with `{compiler}` without errors.
3. Do not use `sorry`, `Admitted`, or `admit`.
4. Start with the preamble, then the lemma statement, then your proof.
5. Include comments in your proof explaining:
   - Your overall proof strategy (e.g., induction on n, case split, contradiction)
   - Key mathematical insights or lemma applications
   - Why non-obvious tactic choices work
   Use {comment_syntax} comments.

Output the proof script now:"#,
        assistant = assistant_name,
        title = conjecture.title,
        preamble = conjecture.preamble,
        statement = conjecture.lemma_statement,
        hints = hints_text,
        skeleton = conjecture.skeleton,
        compiler = if assistant_name == "Lean 4" {
            "lean"
        } else {
            "rocq c"
        },
        comment_syntax = if assistant_name == "Lean 4" {
            "`/- ... -/` or `-- ...`"
        } else {
            "`(* ... *)`"
        },
    )
}

/// Try to prove via the `claude` CLI (primary path)
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

/// Fallback: call Anthropic API directly
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

/// Extract just the code block from a response (strip markdown fences if present)
fn extract_code(response: &str) -> String {
    let trimmed = response.trim();

    // Try to extract from code fence
    if let Some(start) = trimmed.find("```") {
        let after_fence = &trimmed[start + 3..];
        // Skip the language tag line
        let code_start = after_fence.find('\n').map(|i| i + 1).unwrap_or(0);
        let code_body = &after_fence[code_start..];
        if let Some(end) = code_body.find("```") {
            return code_body[..end].trim().to_string();
        }
    }

    // No fences — return as-is
    trimmed.to_string()
}

/// Main entry point: attempt to prove a conjecture with retries.
/// If `resolved_env` is provided, uses the virtual project environment.
/// Otherwise falls back to writing to scratch_dir (legacy mode).
pub async fn prove_conjecture(
    config: &Config,
    conjecture: &Conjecture,
    resolved_env: Option<&ResolvedEnv>,
    audit_logger: &AuditLogger,
) -> Result<ProofAttemptResult> {
    let scratch_dir = Path::new(&config.prover.scratch_dir);
    std::fs::create_dir_all(scratch_dir)?;

    let is_lean = matches!(conjecture.prover.to_lowercase().as_str(), "lean" | "lean4");
    let extension = if is_lean { "lean" } else { "v" };
    let proof_file = scratch_dir.join(format!("{}.{}", conjecture.id, extension));

    let mut total_cost = 0.0;
    let mut last_error = String::new();
    let mut last_script = String::new();
    let max_attempts = 5;

    // Check if claude CLI is available
    let cli_available = Command::new("claude")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);

    for attempt in 1..=max_attempts {
        let prompt = if attempt == 1 {
            build_proof_prompt(conjecture)
        } else {
            format!(
                "{}\n\n## Previous attempt failed (attempt {}/{}).\nError output:\n```\n{}\n```\n\n\
                 Fix the proof and output the complete corrected script:",
                build_proof_prompt(conjecture),
                attempt,
                max_attempts,
                last_error,
            )
        };

        // Try CLI first, fall back to API
        let (response, cost) = if cli_available {
            match try_claude_cli(&prompt, &config.api.model) {
                Ok(r) => r,
                Err(_) => {
                    try_api_fallback(&prompt, &config.api.anthropic_api_key, &config.api.model)
                        .await?
                }
            }
        } else {
            try_api_fallback(&prompt, &config.api.anthropic_api_key, &config.api.model).await?
        };

        total_cost += cost;
        let script = extract_code(&response);
        last_script = script.clone();

        // Write to scratch file
        std::fs::write(&proof_file, &script)?;

        // Verify using resolved environment or legacy mode
        let verify_result = if let Some(env) = resolved_env {
            verifier::verify_with_env(env, &proof_file, is_lean)?
        } else {
            // Legacy fallback: no env available, just try direct build
            // This shouldn't normally happen with the new flow
            anyhow::bail!(
                "No resolved environment available for conjecture {}. \
                 Ensure dependencies are set.",
                conjecture.id
            );
        };

        if verify_result.success {
            audit_logger.log_attempt(&AuditEntry {
                timestamp: Utc::now().to_rfc3339(),
                conjecture_id: conjecture.id.clone(),
                conjecture_title: conjecture.title.clone(),
                attempt,
                max_attempts,
                model: config.api.model.clone(),
                cost_usd: cost,
                success: true,
                error_snippet: String::new(),
            });
            return Ok(ProofAttemptResult {
                success: true,
                proof_script: script,
                cost_usd: total_cost,
                attempts: attempt,
                error_output: String::new(),
            });
        }

        last_error = verify_result.output;
        audit_logger.log_attempt(&AuditEntry {
            timestamp: Utc::now().to_rfc3339(),
            conjecture_id: conjecture.id.clone(),
            conjecture_title: conjecture.title.clone(),
            attempt,
            max_attempts,
            model: config.api.model.clone(),
            cost_usd: cost,
            success: false,
            error_snippet: last_error.chars().take(500).collect(),
        });
        eprintln!(
            "  Attempt {}/{} failed for {}",
            attempt, max_attempts, conjecture.id
        );
    }

    Ok(ProofAttemptResult {
        success: false,
        proof_script: last_script,
        cost_usd: total_cost,
        attempts: max_attempts,
        error_output: last_error,
    })
}
