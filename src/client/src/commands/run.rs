use anyhow::{bail, Result};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use std::collections::HashMap;
use std::path::PathBuf;
use uuid::Uuid;

use crate::archive::pack;
use crate::budget::BudgetTracker;
use crate::config::Config;
use crate::nft::metadata::{generate_nft_metadata, ContributionInfo};
use crate::prover::claude;
use crate::prover::env_manager::{EnvManager, ResolvedEnv};
use crate::server_client::api::{
    Certificate, Conjecture, ContributionSummary, Dependencies, ServerClient,
};
use crate::signing;

/// Compute a dep-group key for grouping conjectures by identical dependencies.
fn dep_group_key(conjecture: &Conjecture) -> String {
    match &conjecture.dependencies {
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
        None => format!("none:{}", conjecture.prover),
    }
}

pub async fn run_prove() -> Result<()> {
    if !Config::exists() {
        bail!("No config found. Run `proof-at-home init` first.");
    }

    let mut config = Config::load()?;

    if config.budget.donated_usd <= 0.0 {
        bail!("No budget set. Run `proof-at-home donate` first.");
    }

    let contribution_id = Uuid::new_v4().to_string();
    let contribution_dir = Config::contributions_dir()?.join(&contribution_id);
    std::fs::create_dir_all(&contribution_dir)?;
    std::fs::create_dir_all(&config.prover.scratch_dir)?;

    let audit_logger = claude::AuditLogger::new(&contribution_dir);

    println!("{}", "=== Proof@Home Contribution ===".bold().cyan());
    println!("Contribution: {}", contribution_id.dimmed());
    println!(
        "Budget:       {}",
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

    // Fetch conjectures
    let conjecture_summaries = server.fetch_conjectures().await?;
    if conjecture_summaries.is_empty() {
        bail!("No conjectures available from server.");
    }
    println!(
        "Found {} conjectures to attempt.",
        conjecture_summaries.len()
    );

    // Fetch full conjecture details for all conjectures
    let mut conjectures: Vec<Conjecture> = Vec::new();
    for ps in &conjecture_summaries {
        let conjecture = server.fetch_conjecture(&ps.id).await?;
        conjectures.push(conjecture);
    }

    // Pre-flight: group conjectures by dep hash, setup unique envs
    println!();
    println!("{}", "Setting up proof environments...".bold());
    let env_manager = EnvManager::new(&config.prover.envs_dir);
    let mut env_cache: HashMap<String, ResolvedEnv> = HashMap::new();

    // Collect unique dep groups
    let mut dep_groups: HashMap<String, &Conjecture> = HashMap::new();
    for conjecture in &conjectures {
        let key = dep_group_key(conjecture);
        dep_groups.entry(key).or_insert(conjecture);
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
    let mut conjectures_proved = 0u32;
    let mut conjectures_attempted = 0u32;
    let mut provers_used: Vec<String> = Vec::new();
    let mut prover_versions: Vec<String> = Vec::new();

    for conjecture in &conjectures {
        if tracker.is_exhausted() {
            println!("\n{} Budget exhausted! Wrapping up.", "⚠".yellow());
            break;
        }

        let key = dep_group_key(conjecture);
        let resolved_env = env_cache.get(&key);

        if resolved_env.is_none() {
            eprintln!(
                "  {} Skipping {} (environment not available)",
                "!".yellow(),
                conjecture.id
            );
            continue;
        }

        conjectures_attempted += 1;

        let spinner = ProgressBar::new_spinner();
        spinner.set_style(
            ProgressStyle::default_spinner()
                .template("{spinner:.cyan} {msg}")
                .unwrap(),
        );
        spinner.set_message(format!(
            "Proving: {} [{}]",
            conjecture.title, conjecture.difficulty
        ));
        spinner.enable_steady_tick(std::time::Duration::from_millis(100));

        let result =
            claude::prove_conjecture(&config, conjecture, resolved_env, &audit_logger).await?;
        tracker.add_cost(result.cost_usd);

        spinner.finish_and_clear();

        if result.success {
            conjectures_proved += 1;
            println!(
                "  {} {} (${:.4}, {} attempts)",
                "✓".green().bold(),
                conjecture.title,
                result.cost_usd,
                result.attempts
            );
        } else {
            println!(
                "  {} {} (${:.4}, {} attempts)",
                "✗".red(),
                conjecture.title,
                result.cost_usd,
                result.attempts
            );
        }

        if !provers_used.contains(&conjecture.prover) {
            provers_used.push(conjecture.prover.clone());
        }

        let version = match &conjecture.dependencies {
            Some(Dependencies::Rocq(deps)) => deps.rocq_version.clone(),
            Some(Dependencies::Lean(deps)) => deps.lean_toolchain.clone(),
            None => String::new(),
        };
        if !version.is_empty() && !prover_versions.contains(&version) {
            prover_versions.push(version);
        }

        // Submit individual result
        let _ = server
            .submit_certificate(&Certificate {
                conjecture_id: conjecture.id.clone(),
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
    let scratch_dir = PathBuf::from(&config.prover.scratch_dir);
    let (archive_path, sha256) = pack::create_archive(&scratch_dir, &contribution_dir)?;
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
    let pa_label = provers_used.join("/");
    let total_cost = tracker.run_spent();
    let proof_status = if conjectures_attempted == 0 || conjectures_proved == 0 {
        "unproved"
    } else if conjectures_proved == conjectures_attempted {
        "proved"
    } else {
        "incomplete"
    }
    .to_string();

    let nft_meta = generate_nft_metadata(&ContributionInfo {
        username: config.identity.username.clone(),
        conjectures_proved,
        conjectures_attempted,
        cost_donated_usd: total_cost,
        prover: pa_label,
        prover_version: prover_versions.join("/"),
        archive_sha256: sha256.clone(),
        proof_status: proof_status.clone(),
        public_key,
        archive_signature,
    });

    let nft_path = contribution_dir.join("nft_metadata.json");
    std::fs::write(&nft_path, serde_json::to_string_pretty(&nft_meta)?)?;

    // Submit contribution summary
    let _ = server
        .submit_contribution(&ContributionSummary {
            username: config.identity.username.clone(),
            contribution_id: contribution_id.clone(),
            conjectures_attempted,
            conjectures_proved,
            total_cost_usd: total_cost,
            archive_sha256: sha256.clone(),
            nft_metadata: nft_meta,
            proof_status,
        })
        .await;

    // Update config with lifetime stats
    config.budget.run_spent = total_cost;
    config.budget.total_spent += total_cost;
    config.save()?;

    // Print summary
    println!();
    println!("{}", "=== Contribution Summary ===".bold().cyan());
    println!("Conjectures attempted: {}", conjectures_attempted);
    println!(
        "Conjectures proved:    {}",
        format!("{}", conjectures_proved).green()
    );
    println!("Cost:               ${:.4}", total_cost);
    println!("Budget remaining:   ${:.4}", tracker.remaining());
    println!();
    println!("Archive:  {}", archive_path.display());
    println!("SHA-256:  {}", sha256.dimmed());
    println!("NFT meta: {}", nft_path.display());

    Ok(())
}
