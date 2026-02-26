use anyhow::{bail, Context, Result};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use uuid::Uuid;

use crate::archive::pack;
use crate::budget::BudgetTracker;
use crate::commands_store::loader;
use crate::config::Config;
use crate::nft::metadata::{generate_nft_metadata, ContributionInfo};
use crate::prover::claude;
use crate::prover::env_manager::{EnvManager, ResolvedEnv};
use crate::prover::verifier;
use crate::server_client::api::{
    Conjecture, ContributionResult, ContributionSummary, Dependencies, ServerClient,
};
use crate::signing;

/// Saved contribution state for re-sealing.
#[derive(Debug, Serialize, Deserialize)]
struct ContributionState {
    contribution_id: String,
    conjectures_proved: u32,
    conjectures_attempted: u32,
    total_cost_usd: f64,
    provers_used: Vec<String>,
    prover_versions: Vec<String>,
}

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

/// Seal a contribution: finalize on server (get commit SHA), sign it,
/// generate NFT metadata, and seal via the /seal endpoint.
/// Returns (archive_path, commit_sha, nft_path).
#[allow(clippy::too_many_arguments)]
async fn seal_contribution(
    config: &Config,
    contribution_id: &str,
    contribution_dir: &Path,
    conjectures_proved: u32,
    conjectures_attempted: u32,
    total_cost: f64,
    provers_used: &[String],
    _prover_versions: &[String],
    server: &ServerClient,
    proof_mode: &str,
) -> Result<(PathBuf, String, PathBuf)> {
    // Archive proofs (for local convenience + IPFS publish, no longer authoritative)
    print!("Archiving proofs... ");
    let scratch_dir = PathBuf::from(&config.prover.scratch_dir);
    let (archive_path, _archive_sha256) = pack::create_archive(&scratch_dir, contribution_dir)?;
    println!("{}", "OK".green());

    // Finalize contribution on server — get commit SHA
    print!("Finalizing contribution... ");
    let pa_label = provers_used.join("/");
    let proof_status = if conjectures_attempted == 0 || conjectures_proved == 0 {
        "unproved"
    } else if conjectures_proved == conjectures_attempted {
        "proved"
    } else {
        "incomplete"
    }
    .to_string();

    let finalize_resp = server
        .update_contribution(
            contribution_id,
            &ContributionSummary {
                username: config.identity.username.clone(),
                contribution_id: contribution_id.to_string(),
                conjectures_attempted,
                conjectures_proved,
                total_cost_usd: total_cost,
                archive_sha256: String::new(),
                nft_metadata: serde_json::Value::Null,
                proof_status: proof_status.clone(),
            },
        )
        .await?;
    let commit_sha = finalize_resp.commit_sha;
    println!("{} ({})", "OK".green(), &commit_sha[..8]);

    // Sign the git commit SHA
    let (public_key, commit_signature) = match Config::signing_key_path()
        .ok()
        .filter(|p| p.exists())
        .and_then(|p| std::fs::read_to_string(&p).ok())
    {
        Some(key_hex) => match signing::load_signing_key(&key_hex) {
            Ok(key) => {
                let sig = signing::sign_commit(&key, &commit_sha).unwrap_or_default();
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

    // Generate NFT metadata with git commit attributes
    let nft_meta = generate_nft_metadata(&ContributionInfo {
        username: config.identity.username.clone(),
        conjectures_proved,
        conjectures_attempted,
        cost_donated_usd: total_cost,
        prover: pa_label,
        proof_status,
        git_commit: commit_sha.clone(),
        git_repository: config.api.server_url.clone(), // server will provide repo URL
        public_key,
        commit_signature,
        proof_mode: proof_mode.to_string(),
    });

    let nft_path = contribution_dir.join("nft_metadata.json");
    std::fs::write(&nft_path, serde_json::to_string_pretty(&nft_meta)?)?;

    // Seal: send NFT metadata to server, which creates a PR
    print!("Sealing contribution (creating PR)... ");
    match server.seal_contribution(contribution_id, &nft_meta).await {
        Ok(seal_resp) => {
            println!("{}", "OK".green());
            println!("  PR: {}", seal_resp.pr_url.cyan());
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not seal on server: {}", "Warning".yellow(), e);
        }
    }

    Ok((archive_path, commit_sha, nft_path))
}

pub async fn run_prove(command_name: Option<&str>) -> Result<()> {
    if !Config::exists() {
        bail!("No config found. Run `proof-at-home init` first.");
    }

    let mut config = Config::load()?;

    if config.budget.donated_usd <= 0.0 {
        bail!("No budget set. Run `proof-at-home donate` first.");
    }

    // Ensure builtin commands are available
    let _ = loader::ensure_builtins();

    let contribution_id = Uuid::new_v4().to_string();
    let contribution_dir = Config::contributions_dir()?.join(&contribution_id);
    std::fs::create_dir_all(&contribution_dir)?;
    std::fs::create_dir_all(&config.prover.scratch_dir)?;

    let audit_logger = claude::AuditLogger::new(&contribution_dir);

    println!("{}", "=== Proof@Home Contribution ===".bold().cyan());
    println!("Mode:         {}", "AI-assisted".cyan());
    println!("Contribution: {}", contribution_id.dimmed());
    println!(
        "Budget:       {}",
        format!("${:.2}", config.budget.donated_usd).green()
    );
    if let Some(name) = command_name {
        println!("Strategy:     {}", name.cyan());
    }
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

    // Register draft contribution
    let _ = server
        .create_contribution(&contribution_id, &config.identity.username, "")
        .await;

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

        let result = claude::prove_conjecture(
            &config,
            conjecture,
            resolved_env,
            &audit_logger,
            command_name,
        )
        .await?;
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
            .submit_contribution_result(
                &contribution_id,
                &ContributionResult {
                    conjecture_id: conjecture.id.clone(),
                    username: config.identity.username.clone(),
                    success: result.success,
                    proof_script: result.proof_script,
                    cost_usd: result.cost_usd,
                    attempts: result.attempts,
                    error_output: result.error_output,
                },
            )
            .await;
    }

    let total_cost = tracker.run_spent();

    // Save contribution state for re-sealing
    let state = ContributionState {
        contribution_id: contribution_id.clone(),
        conjectures_proved,
        conjectures_attempted,
        total_cost_usd: total_cost,
        provers_used: provers_used.clone(),
        prover_versions: prover_versions.clone(),
    };
    let state_path = contribution_dir.join("contribution_state.json");
    std::fs::write(&state_path, serde_json::to_string_pretty(&state)?)?;

    // Seal: finalize, sign commit SHA, generate NFT, create PR
    println!();
    let (archive_path, commit_sha, nft_path) = seal_contribution(
        &config,
        &contribution_id,
        &contribution_dir,
        conjectures_proved,
        conjectures_attempted,
        total_cost,
        &provers_used,
        &prover_versions,
        &server,
        "ai-assisted",
    )
    .await?;

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
    println!("Archive:    {}", archive_path.display());
    println!("Git Commit: {}", commit_sha.dimmed());
    println!("NFT meta:   {}", nft_path.display());

    Ok(())
}

/// Re-seal an existing contribution: regenerate archive, signature, and NFT metadata.
pub async fn run_prove_seal(contribution_id: &str) -> Result<()> {
    let config = Config::load()?;
    let contribution_dir = Config::contributions_dir()?.join(contribution_id);

    if !contribution_dir.exists() {
        bail!(
            "Contribution directory not found: {}",
            contribution_dir.display()
        );
    }

    // Load saved contribution state
    let state_path = contribution_dir.join("contribution_state.json");
    let state: ContributionState = serde_json::from_str(
        &std::fs::read_to_string(&state_path)
            .with_context(|| format!(
                "contribution_state.json not found in {}. Only contributions created after this update can be re-sealed.",
                contribution_dir.display()
            ))?,
    )
    .context("Failed to parse contribution_state.json")?;

    // Check for existing NFT metadata (re-seal warning)
    let nft_path = contribution_dir.join("nft_metadata.json");
    if nft_path.exists() {
        println!(
            "{}: Re-sealing will overwrite existing NFT metadata. If you already published, re-publish after re-sealing.",
            "Note".yellow()
        );
    }

    println!("{}", "=== Re-sealing Contribution ===".bold().cyan());
    println!("Contribution: {}", contribution_id.dimmed());
    println!();

    let server = ServerClient::new(&config.api.server_url, &config.api.auth_token);

    let proof_mode = if state.total_cost_usd == 0.0 {
        "manual"
    } else {
        "ai-assisted"
    };
    let (archive_path, commit_sha, nft_path) = seal_contribution(
        &config,
        contribution_id,
        &contribution_dir,
        state.conjectures_proved,
        state.conjectures_attempted,
        state.total_cost_usd,
        &state.provers_used,
        &state.prover_versions,
        &server,
        proof_mode,
    )
    .await?;

    println!();
    println!("{}", "=== Re-seal Complete ===".bold().cyan());
    println!("Archive:    {}", archive_path.display());
    println!("Git Commit: {}", commit_sha.dimmed());
    println!("NFT meta:   {}", nft_path.display());

    Ok(())
}

/// Submit hand-written proofs for verification and sealing.
pub async fn run_prove_submit(
    conjecture_id: Option<&str>,
    proof_file: Option<&str>,
    dir: Option<&str>,
) -> Result<()> {
    if !Config::exists() {
        bail!("No config found. Run `proof-at-home init` first.");
    }

    let config = Config::load()?;

    // Resolve input: single file or directory of proof files
    let mut proof_inputs: Vec<(String, PathBuf)> = Vec::new();

    match (conjecture_id, proof_file, dir) {
        (Some(id), Some(file), None) => {
            let path = PathBuf::from(file);
            if !path.exists() {
                bail!("Proof file not found: {}", path.display());
            }
            proof_inputs.push((id.to_string(), path));
        }
        (None, None, Some(dir_path)) => {
            let dir = PathBuf::from(dir_path);
            if !dir.is_dir() {
                bail!("Not a directory: {}", dir.display());
            }
            for entry in std::fs::read_dir(&dir)? {
                let entry = entry?;
                let path = entry.path();
                let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
                if ext == "v" || ext == "lean" {
                    let stem = path
                        .file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or("")
                        .to_string();
                    if stem.is_empty() {
                        continue;
                    }
                    proof_inputs.push((stem, path));
                }
            }
            if proof_inputs.is_empty() {
                bail!("No .v or .lean files found in {}", dir_path);
            }
            proof_inputs.sort_by(|a, b| a.0.cmp(&b.0));
        }
        _ => {
            bail!(
                "Usage: prove submit <conjecture-id> <proof-file>\n       prove submit --dir <directory>"
            );
        }
    }

    let contribution_id = Uuid::new_v4().to_string();
    let contribution_dir = Config::contributions_dir()?.join(&contribution_id);
    std::fs::create_dir_all(&contribution_dir)?;
    std::fs::create_dir_all(&config.prover.scratch_dir)?;

    println!("{}", "=== Proof@Home Contribution ===".bold().cyan());
    println!("Mode:         {}", "Manual".cyan());
    println!("Contribution: {}", contribution_id.dimmed());
    println!(
        "Proof files:  {}",
        format!("{}", proof_inputs.len()).green()
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

    // Register draft contribution
    let _ = server
        .create_contribution(&contribution_id, &config.identity.username, "")
        .await;

    // Fetch conjecture metadata and set up environments
    println!("{}", "Setting up proof environments...".bold());
    let env_manager = EnvManager::new(&config.prover.envs_dir);
    let mut env_cache: HashMap<String, ResolvedEnv> = HashMap::new();
    let mut conjectures_map: HashMap<String, Conjecture> = HashMap::new();

    for (cid, _) in &proof_inputs {
        if conjectures_map.contains_key(cid) {
            continue;
        }
        let conjecture = server
            .fetch_conjecture(cid)
            .await
            .with_context(|| format!("Failed to fetch conjecture '{}'", cid))?;
        conjectures_map.insert(cid.clone(), conjecture);
    }

    // Set up unique environments
    let mut dep_groups: HashMap<String, &Conjecture> = HashMap::new();
    for conjecture in conjectures_map.values() {
        let key = dep_group_key(conjecture);
        dep_groups.entry(key).or_insert(conjecture);
    }

    for (key, representative) in &dep_groups {
        if representative.dependencies.is_none() {
            eprintln!(
                "  {} Skipping env '{}' (no dependencies declared)",
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

    // Verify and submit each proof
    let mut conjectures_proved = 0u32;
    let mut conjectures_attempted = 0u32;
    let mut provers_used: Vec<String> = Vec::new();
    let mut prover_versions: Vec<String> = Vec::new();

    for (cid, proof_path) in &proof_inputs {
        let conjecture = match conjectures_map.get(cid) {
            Some(c) => c,
            None => {
                eprintln!("  {} Skipping {} (conjecture not found)", "!".yellow(), cid);
                continue;
            }
        };

        let key = dep_group_key(conjecture);
        let resolved_env = match env_cache.get(&key) {
            Some(env) => env,
            None => {
                eprintln!(
                    "  {} Skipping {} (environment not available)",
                    "!".yellow(),
                    cid
                );
                continue;
            }
        };

        conjectures_attempted += 1;

        let spinner = ProgressBar::new_spinner();
        spinner.set_style(
            ProgressStyle::default_spinner()
                .template("{spinner:.cyan} {msg}")
                .unwrap(),
        );
        spinner.set_message(format!("Verifying: {} [{}]", conjecture.title, cid));
        spinner.enable_steady_tick(std::time::Duration::from_millis(100));

        // Copy proof file to scratch and verify
        let is_lean = conjecture.prover == "lean4";
        let ext = if is_lean { "lean" } else { "v" };
        let scratch_file =
            PathBuf::from(&config.prover.scratch_dir).join(format!("{}.{}", cid, ext));
        std::fs::copy(proof_path, &scratch_file)
            .with_context(|| format!("Failed to copy proof file {}", proof_path.display()))?;

        let verify_result = verifier::verify_with_env(resolved_env, &scratch_file, is_lean)?;
        let proof_script = std::fs::read_to_string(proof_path)
            .with_context(|| format!("Failed to read proof file {}", proof_path.display()))?;

        spinner.finish_and_clear();

        if verify_result.success {
            conjectures_proved += 1;
            println!("  {} {} ({})", "✓".green().bold(), conjecture.title, cid);
        } else {
            println!("  {} {} ({})", "✗".red(), conjecture.title, cid);
            let truncated = if verify_result.output.len() > 500 {
                format!("{}...", &verify_result.output[..500])
            } else {
                verify_result.output.clone()
            };
            eprintln!("    Error: {}", truncated.dimmed());
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

        // Submit result to server
        let _ = server
            .submit_contribution_result(
                &contribution_id,
                &ContributionResult {
                    conjecture_id: cid.clone(),
                    username: config.identity.username.clone(),
                    success: verify_result.success,
                    proof_script,
                    cost_usd: 0.0,
                    attempts: 1,
                    error_output: if verify_result.success {
                        String::new()
                    } else {
                        verify_result.output
                    },
                },
            )
            .await;
    }

    // Save contribution state
    let state = ContributionState {
        contribution_id: contribution_id.clone(),
        conjectures_proved,
        conjectures_attempted,
        total_cost_usd: 0.0,
        provers_used: provers_used.clone(),
        prover_versions: prover_versions.clone(),
    };
    let state_path = contribution_dir.join("contribution_state.json");
    std::fs::write(&state_path, serde_json::to_string_pretty(&state)?)?;

    // Seal
    println!();
    let (archive_path, commit_sha, nft_path) = seal_contribution(
        &config,
        &contribution_id,
        &contribution_dir,
        conjectures_proved,
        conjectures_attempted,
        0.0,
        &provers_used,
        &prover_versions,
        &server,
        "manual",
    )
    .await?;

    // Print summary
    println!();
    println!("{}", "=== Contribution Summary ===".bold().cyan());
    println!("Mode:                  {}", "Manual".cyan());
    println!("Conjectures attempted: {}", conjectures_attempted);
    println!(
        "Conjectures proved:    {}",
        format!("{}", conjectures_proved).green()
    );
    println!("Cost:                  $0.00");
    println!();
    println!("Archive:    {}", archive_path.display());
    println!("Git Commit: {}", commit_sha.dimmed());
    println!("NFT meta:   {}", nft_path.display());

    Ok(())
}
