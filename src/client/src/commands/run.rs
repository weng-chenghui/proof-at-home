use anyhow::{bail, Result};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use std::collections::HashMap;
use std::path::PathBuf;
use uuid::Uuid;

use crate::archive::pack;
use crate::budget::BudgetTracker;
use crate::config::Config;
use crate::nft::metadata::{generate_nft_metadata, SessionInfo};
use crate::prover::claude;
use crate::prover::env_manager::{EnvManager, ResolvedEnv};
use crate::server_client::api::{Dependencies, Problem, ProofResult, ServerClient, SessionSummary};
use crate::signing;

/// Compute a dep-group key for grouping problems by identical dependencies.
fn dep_group_key(problem: &Problem) -> String {
    match &problem.dependencies {
        Some(Dependencies::Rocq(deps)) => {
            let mut pkgs = deps.opam_packages.clone();
            pkgs.sort();
            format!("rocq:{}:{}", deps.rocq_version, pkgs.join(","))
        }
        Some(Dependencies::Lean(deps)) => {
            let mut pkgs = deps.lake_packages.clone();
            pkgs.sort();
            format!("lean:{}:{}", deps.lean_toolchain, pkgs.join(","))
        }
        None => format!("none:{}", problem.proof_assistant),
    }
}

pub async fn run_session() -> Result<()> {
    if !Config::exists() {
        bail!("No config found. Run `proof-at-home init` first.");
    }

    let mut config = Config::load()?;

    if config.budget.donated_usd <= 0.0 {
        bail!("No budget set. Run `proof-at-home donate` first.");
    }

    let session_id = Uuid::new_v4().to_string();
    let session_dir = Config::sessions_dir()?.join(&session_id);
    std::fs::create_dir_all(&session_dir)?;
    std::fs::create_dir_all(&config.proof_assistant.scratch_dir)?;

    let audit_logger = claude::AuditLogger::new(&session_dir);

    println!("{}", "=== Proof@Home Session ===".bold().cyan());
    println!("Session: {}", session_id.dimmed());
    println!(
        "Budget:  {}",
        format!("${:.2}", config.budget.donated_usd).green()
    );
    println!();

    // Health check
    let server = ServerClient::new(&config.api.server_url, &config.api.auth_token);
    print!("Connecting to server... ");
    match server.health_check().await {
        Ok(true) => println!("{}", "OK".green()),
        _ => {
            println!("{}", "FAILED".red());
            bail!(
                "Cannot reach server at {}. Is it running?",
                config.api.server_url
            );
        }
    }

    // Fetch problems
    let problem_summaries = server.fetch_problems().await?;
    if problem_summaries.is_empty() {
        bail!("No problems available from server.");
    }
    println!("Found {} problems to attempt.", problem_summaries.len());

    // Fetch full problem details for all problems
    let mut problems: Vec<Problem> = Vec::new();
    for ps in &problem_summaries {
        let problem = server.fetch_problem(&ps.id).await?;
        problems.push(problem);
    }

    // Pre-flight: group problems by dep hash, setup unique envs
    println!();
    println!("{}", "Setting up proof environments...".bold());
    let env_manager = EnvManager::new(&config.proof_assistant.envs_dir);
    let mut env_cache: HashMap<String, ResolvedEnv> = HashMap::new();

    // Collect unique dep groups
    let mut dep_groups: HashMap<String, &Problem> = HashMap::new();
    for problem in &problems {
        let key = dep_group_key(problem);
        dep_groups.entry(key).or_insert(problem);
    }

    for (key, representative) in &dep_groups {
        if representative.dependencies.is_none() {
            eprintln!(
                "  {} Skipping '{}' (no dependencies declared)",
                "!".yellow(),
                key
            );
            continue;
        }

        let spinner = ProgressBar::new_spinner();
        spinner.set_style(
            ProgressStyle::default_spinner()
                .template("{spinner:.cyan} {msg}")
                .unwrap(),
        );
        spinner.set_message(format!("Preparing env: {}", key));
        spinner.enable_steady_tick(std::time::Duration::from_millis(100));

        match env_manager.ensure_env(representative) {
            Ok(env) => {
                spinner.finish_with_message(format!("{} Env ready: {}", "✓".green(), key));
                env_cache.insert(key.clone(), env);
            }
            Err(e) => {
                spinner.finish_with_message(format!(
                    "{} Env setup failed for {}: {}",
                    "✗".red(),
                    key,
                    e
                ));
            }
        }
    }

    println!();

    // Set up budget tracker
    let tracker = BudgetTracker::new(config.budget.donated_usd);
    let mut problems_proved = 0u32;
    let mut problems_attempted = 0u32;
    let mut proof_assistants_used: Vec<String> = Vec::new();
    let mut proof_assistant_versions: Vec<String> = Vec::new();

    for problem in &problems {
        if tracker.is_exhausted() {
            println!("\n{} Budget exhausted! Wrapping up session.", "⚠".yellow());
            break;
        }

        let key = dep_group_key(problem);
        let resolved_env = env_cache.get(&key);

        if resolved_env.is_none() {
            eprintln!(
                "  {} Skipping {} (environment not available)",
                "!".yellow(),
                problem.id
            );
            continue;
        }

        problems_attempted += 1;

        let spinner = ProgressBar::new_spinner();
        spinner.set_style(
            ProgressStyle::default_spinner()
                .template("{spinner:.cyan} {msg}")
                .unwrap(),
        );
        spinner.set_message(format!(
            "Proving: {} [{}]",
            problem.title, problem.difficulty
        ));
        spinner.enable_steady_tick(std::time::Duration::from_millis(100));

        let result = claude::prove_problem(&config, problem, resolved_env, &audit_logger).await?;
        tracker.add_cost(result.cost_usd);

        spinner.finish_and_clear();

        if result.success {
            problems_proved += 1;
            println!(
                "  {} {} (${:.4}, {} attempts)",
                "✓".green().bold(),
                problem.title,
                result.cost_usd,
                result.attempts
            );
        } else {
            println!(
                "  {} {} (${:.4}, {} attempts)",
                "✗".red(),
                problem.title,
                result.cost_usd,
                result.attempts
            );
        }

        if !proof_assistants_used.contains(&problem.proof_assistant) {
            proof_assistants_used.push(problem.proof_assistant.clone());
        }

        let version = match &problem.dependencies {
            Some(Dependencies::Rocq(deps)) => deps.rocq_version.clone(),
            Some(Dependencies::Lean(deps)) => deps.lean_toolchain.clone(),
            None => String::new(),
        };
        if !version.is_empty() && !proof_assistant_versions.contains(&version) {
            proof_assistant_versions.push(version);
        }

        // Submit individual result
        let _ = server
            .submit_result(&ProofResult {
                problem_id: problem.id.clone(),
                username: config.identity.username.clone(),
                success: result.success,
                proof_script: result.proof_script,
                cost_usd: result.cost_usd,
                attempts: result.attempts,
                error_output: result.error_output,
            })
            .await;
    }

    // Archive proofs
    println!();
    print!("Archiving proofs... ");
    let scratch_dir = PathBuf::from(&config.proof_assistant.scratch_dir);
    let (archive_path, sha256) = pack::create_archive(&scratch_dir, &session_dir)?;
    println!("{}", "OK".green());

    // Sign archive hash
    let (public_key, archive_signature) = match Config::signing_key_path()
        .ok()
        .filter(|p| p.exists())
        .and_then(|p| std::fs::read_to_string(&p).ok())
    {
        Some(key_hex) => match signing::load_signing_key(&key_hex) {
            Ok(key) => {
                let sig = signing::sign_hash(&key, &sha256).unwrap_or_default();
                (config.identity.public_key.clone(), sig)
            }
            Err(e) => {
                eprintln!("{}: Could not load signing key: {}", "Warning".yellow(), e);
                (String::new(), String::new())
            }
        },
        None => {
            eprintln!(
                "{}: No signing key found. Run `proof-at-home init` to generate one.",
                "Warning".yellow()
            );
            (String::new(), String::new())
        }
    };

    // Generate NFT metadata
    let pa_label = proof_assistants_used.join("/");
    let total_cost = tracker.session_spent();
    let proof_status = if problems_attempted == 0 || problems_proved == 0 {
        "unproved"
    } else if problems_proved == problems_attempted {
        "proved"
    } else {
        "incomplete"
    }
    .to_string();

    let nft_meta = generate_nft_metadata(&SessionInfo {
        username: config.identity.username.clone(),
        problems_proved,
        problems_attempted,
        cost_donated_usd: total_cost,
        proof_assistant: pa_label,
        proof_assistant_version: proof_assistant_versions.join("/"),
        archive_sha256: sha256.clone(),
        proof_status: proof_status.clone(),
        public_key,
        archive_signature,
    });

    let nft_path = session_dir.join("nft_metadata.json");
    std::fs::write(&nft_path, serde_json::to_string_pretty(&nft_meta)?)?;

    // Submit session summary
    let _ = server
        .submit_session(&SessionSummary {
            username: config.identity.username.clone(),
            session_id: session_id.clone(),
            problems_attempted,
            problems_proved,
            total_cost_usd: total_cost,
            archive_sha256: sha256.clone(),
            nft_metadata: nft_meta,
            proof_status,
        })
        .await;

    // Update config with lifetime stats
    config.budget.session_spent = total_cost;
    config.budget.total_spent += total_cost;
    config.save()?;

    // Print summary
    println!();
    println!("{}", "=== Session Summary ===".bold().cyan());
    println!("Problems attempted: {}", problems_attempted);
    println!(
        "Problems proved:    {}",
        format!("{}", problems_proved).green()
    );
    println!("Session cost:       ${:.4}", total_cost);
    println!("Budget remaining:   ${:.4}", tracker.remaining());
    println!();
    println!("Archive:  {}", archive_path.display());
    println!("SHA-256:  {}", sha256.dimmed());
    println!("NFT meta: {}", nft_path.display());

    Ok(())
}
