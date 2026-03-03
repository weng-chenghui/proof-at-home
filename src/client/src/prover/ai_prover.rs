use anyhow::Result;
use chrono::Utc;
use serde::Serialize;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::ai::AiProvider;
use crate::config::Config;
use crate::prover::env_manager::ResolvedEnv;
use crate::prover::verifier;
use crate::server_client::api::Conjecture;
use crate::strategy_store::loader::{self, LoadedStrategy, StrategyVars};

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
    pub provider: String,
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

/// Build the prompt for proving a lemma.
/// If `strategy_name` is provided, loads that specific strategy file.
/// Otherwise auto-selects based on the conjecture's prover type.
/// Falls back to an inline prompt if strategy file loading fails.
fn build_proof_prompt(
    conjecture: &Conjecture,
    strategy_name: Option<&str>,
    config: &Config,
) -> String {
    let strategy_result = if let Some(name) = strategy_name {
        loader::load_strategy(name)
    } else {
        loader::auto_select_strategy(&conjecture.prover)
    };

    if let Ok(strategy) = strategy_result {
        return build_prompt_from_strategy(&strategy, conjecture, config);
    }

    // Fallback: inline prompt
    build_inline_prompt(conjecture)
}

/// Build prompt from a loaded strategy file with variable substitution.
fn build_prompt_from_strategy(
    strategy: &LoadedStrategy,
    conjecture: &Conjecture,
    config: &Config,
) -> String {
    let is_lean = matches!(conjecture.prover.to_lowercase().as_str(), "lean" | "lean4");
    let extension = if is_lean { "lean" } else { "v" };
    let scratch = &config.prover.scratch_dir;
    let lemma_file = format!("{}/{}.{}", scratch, conjecture.id, extension);

    let vars = StrategyVars {
        lean_path: std::env::var("LEAN_PATH").unwrap_or_else(|_| "lean".into()),
        lake_path: std::env::var("LAKE_PATH").unwrap_or_else(|_| "lake".into()),
        rocq: std::env::var("ROCQ").unwrap_or_else(|_| "rocq c".into()),
        coq_include: std::env::var("COQ_INCLUDE").unwrap_or_default(),
        scratch_dir: scratch.clone(),
        lemma_file,
    };

    loader::render_strategy(strategy, conjecture, &vars)
}

/// Fallback inline prompt (original implementation).
fn build_inline_prompt(conjecture: &Conjecture) -> String {
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

## Conjecture: {title}

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

/// Extract just the code block from a response (strip markdown fences if present)
pub fn extract_code(response: &str) -> String {
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
/// Uses the given `AiProvider` for AI completions.
pub async fn prove_conjecture(
    config: &Config,
    provider: &dyn AiProvider,
    conjecture: &Conjecture,
    resolved_env: Option<&ResolvedEnv>,
    audit_logger: &AuditLogger,
    strategy_name: Option<&str>,
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
    let model = config.model();

    for attempt in 1..=max_attempts {
        let prompt = if attempt == 1 {
            build_proof_prompt(conjecture, strategy_name, config)
        } else {
            format!(
                "{}\n\n## Previous attempt failed (attempt {}/{}).\nError output:\n```\n{}\n```\n\n\
                 Fix the proof and output the complete corrected script:",
                build_proof_prompt(conjecture, strategy_name, config),
                attempt,
                max_attempts,
                last_error,
            )
        };

        let ai_response = provider.complete(&prompt, &model, 4096).await?;
        let cost = ai_response.cost_usd;

        total_cost += cost;
        let script = extract_code(&ai_response.text);
        last_script = script.clone();

        // Write to scratch file
        std::fs::write(&proof_file, &script)?;

        // Verify using resolved environment or legacy mode
        let verify_result = if let Some(env) = resolved_env {
            verifier::verify_with_env(env, &proof_file, is_lean)?
        } else {
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
                provider: provider.name().to_string(),
                model: model.clone(),
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
            provider: provider.name().to_string(),
            model: model.clone(),
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
