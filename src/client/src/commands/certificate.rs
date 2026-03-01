use anyhow::{Context, Result};
use chrono::Utc;
use colored::Colorize;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

use crate::certifier::comparison;
use crate::certifier::templates;
use crate::certifier::types::*;
use crate::config::Config;
use crate::nft::metadata::generate_certificate_nft_metadata;
use crate::nft::metadata::CertificateInfo;
use crate::server_client::api::ServerClient;
use crate::signing;

/// Resolve the certifications base directory: ~/.proof-at-home/certifications/
fn certifications_dir() -> Result<PathBuf> {
    let dir = Config::config_dir()?.join("certifications");
    std::fs::create_dir_all(&dir)?;
    Ok(dir)
}

/// Path to the active certification pointer file
fn active_certification_path() -> Result<PathBuf> {
    Ok(Config::config_dir()?.join("active_certification"))
}

/// Get the active certification session ID (if any)
fn get_active_certification_id() -> Result<Option<String>> {
    let path = active_certification_path()?;
    if path.exists() {
        let id = std::fs::read_to_string(&path)?.trim().to_string();
        if id.is_empty() {
            Ok(None)
        } else {
            Ok(Some(id))
        }
    } else {
        Ok(None)
    }
}

/// Set the active certification session ID
fn set_active_certification_id(id: &str) -> Result<()> {
    let path = active_certification_path()?;
    std::fs::write(&path, id)?;
    Ok(())
}

/// Load a certification state from its directory
fn load_certification_state(certification_dir: &Path) -> Result<CertificationState> {
    let state_path = certification_dir.join("certification_state.json");
    let content = std::fs::read_to_string(&state_path)
        .with_context(|| format!("Failed to read {}", state_path.display()))?;
    let state: CertificationState =
        serde_json::from_str(&content).context("Failed to parse certification_state.json")?;
    Ok(state)
}

/// Save a certification state to its directory
fn save_certification_state(certification_dir: &Path, state: &CertificationState) -> Result<()> {
    let state_path = certification_dir.join("certification_state.json");
    let content = serde_json::to_string_pretty(state)?;
    std::fs::write(&state_path, content)?;
    Ok(())
}

/// Get the active certification directory and loaded state
fn get_active_certification() -> Result<(PathBuf, CertificationState)> {
    let certification_id = get_active_certification_id()?
        .context("No active certification. Run `pah certificate create` first.")?;
    let certification_dir = certifications_dir()?.join(&certification_id);
    if !certification_dir.exists() {
        anyhow::bail!(
            "Certification directory not found: {}. Run `pah certificate create`.",
            certification_dir.display()
        );
    }
    let state = load_certification_state(&certification_dir)?;
    Ok((certification_dir, state))
}

// ── certificate list (NEW: fetch from server) ──

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let certificates = client.fetch_certificates().await?;

    if certificates.is_empty() {
        println!("No certificates found.");
        return Ok(());
    }

    println!(
        "{:<40} {:<20} {:<10} {:<10} Recommendation",
        "ID", "Certifier", "Packages", "Compared"
    );
    println!("{}", "-".repeat(100));

    for c in &certificates {
        let display_id = if c.certificate_id.len() > 36 {
            &c.certificate_id[..36]
        } else {
            &c.certificate_id
        };
        println!(
            "{:<40} {:<20} {:<10} {:<10} {}",
            display_id,
            c.certifier_username,
            c.packages_certified,
            c.conjectures_compared,
            c.recommendation
        );
    }

    println!("\nTotal: {}", certificates.len());
    Ok(())
}

// ── certificate create (was certify start) ──

pub async fn cmd_create() -> Result<()> {
    let config = Config::load_or_default();
    config.require_login()?;
    let certification_id = uuid::Uuid::new_v4().to_string();
    let certification_dir = certifications_dir()?.join(&certification_id);
    let packages_dir = certification_dir.join("packages");
    std::fs::create_dir_all(&packages_dir)?;

    let mut state = CertificationState {
        certification_id: certification_id.clone(),
        certifier_username: config.identity.username.clone(),
        created_at: Utc::now().to_rfc3339(),
        packages: Vec::new(),
        status: CertificationStatus::Open,
    };

    let server = ServerClient::new(&config.server_url(), &config.api.auth_token);
    let available = match server.fetch_contribution_reviews().await {
        Ok(pkgs) => pkgs,
        Err(e) => {
            eprintln!(
                "{}: Could not fetch packages from server: {}",
                "Warning".yellow(),
                e
            );
            eprintln!("You can import local archives with `pah certificate import <path>`.");
            Vec::new()
        }
    };

    if !available.is_empty() {
        println!("Available proof packages from server:\n");
        let items: Vec<String> = available
            .iter()
            .map(|p| {
                format!(
                    "{} ({}) — {} conjectures [{}]",
                    p.contributor_username,
                    &p.contributor_contribution_id[..8],
                    p.conjecture_ids.len(),
                    p.prover,
                )
            })
            .collect();

        let selections = dialoguer::MultiSelect::new()
            .with_prompt("Select packages to include (space to toggle, enter to confirm)")
            .items(&items)
            .interact()?;

        for idx in selections {
            let pkg_info = &available[idx];
            let dest_dir = packages_dir.join(&pkg_info.contributor_contribution_id);
            std::fs::create_dir_all(&dest_dir)?;

            print!(
                "  Downloading {} ({})...",
                pkg_info.contributor_username,
                &pkg_info.contributor_contribution_id[..8]
            );
            let archive_dest = dest_dir.join("proofs.tar.gz");
            match server
                .download_package(&pkg_info.contributor_contribution_id, &archive_dest)
                .await
            {
                Ok(()) => {
                    println!(" {}", "done".green());
                    extract_archive(&archive_dest, &dest_dir)?;

                    let sha = compute_sha256(&archive_dest)?;

                    state.packages.push(CertificatePackage {
                        contributor_contribution_id: pkg_info.contributor_contribution_id.clone(),
                        contributor_username: pkg_info.contributor_username.clone(),
                        prover: pkg_info.prover.clone(),
                        conjecture_ids: pkg_info.conjecture_ids.clone(),
                        archive_sha256: sha,
                        import_source: "server".into(),
                    });
                }
                Err(e) => {
                    println!(" {}: {}", "failed".red(), e);
                }
            }
        }
    }

    save_certification_state(&certification_dir, &state)?;
    set_active_certification_id(&certification_id)?;

    println!(
        "\n{} Certification created: {}",
        "✓".green(),
        certification_id
    );
    println!("  Directory: {}", certification_dir.display());
    println!("  Packages loaded: {}", state.packages.len());
    if state.packages.is_empty() {
        println!(
            "\n  Import local archives with: {}",
            "pah certificate import <path>".cyan()
        );
    }

    Ok(())
}

// ── certificate import ──

pub async fn cmd_import(path: &Path) -> Result<()> {
    let (certification_dir, mut state) = get_active_certification()?;

    if state.status == CertificationStatus::Sealed {
        eprintln!(
            "{}: Importing into a sealed certification. You will need to re-seal after importing.",
            "Warning".yellow()
        );
    }

    if !path.exists() {
        anyhow::bail!("Archive not found: {}", path.display());
    }

    let packages_dir = certification_dir.join("packages");

    let archive_stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");
    let contribution_id = archive_stem.strip_suffix(".tar").unwrap_or(archive_stem);
    let dest_dir = packages_dir.join(contribution_id);
    std::fs::create_dir_all(&dest_dir)?;

    let archive_dest = dest_dir.join("proofs.tar.gz");
    std::fs::copy(path, &archive_dest)
        .with_context(|| format!("Failed to copy archive to {}", archive_dest.display()))?;

    extract_archive(&archive_dest, &dest_dir)?;

    let sha = compute_sha256(&archive_dest)?;

    let conjecture_ids = scan_proof_files(&dest_dir)?;

    let prover = if conjecture_ids
        .iter()
        .any(|p| dest_dir.join(format!("{}.lean", p)).exists())
    {
        "lean".into()
    } else {
        "rocq".into()
    };

    state.packages.push(CertificatePackage {
        contributor_contribution_id: contribution_id.to_string(),
        contributor_username: String::new(),
        prover,
        conjecture_ids: conjecture_ids.clone(),
        archive_sha256: sha,
        import_source: format!("local:{}", path.display()),
    });

    save_certification_state(&certification_dir, &state)?;

    println!(
        "{} Imported {} ({} proof files)",
        "✓".green(),
        contribution_id,
        conjecture_ids.len()
    );

    Ok(())
}

// ── certificate compare ──

pub async fn cmd_compare(strategy_name: Option<&str>) -> Result<()> {
    let config = Config::load_or_default();
    let (certification_dir, mut state) = get_active_certification()?;

    if state.packages.len() < 2 {
        anyhow::bail!("Need at least 2 packages to compare. Import more packages first.");
    }

    let result =
        comparison::run_comparison(&config, &state, &certification_dir, strategy_name).await?;

    let comp_path = certification_dir.join("ai_comparison.json");
    let content = serde_json::to_string_pretty(&result)?;
    std::fs::write(&comp_path, content)?;

    state.status = CertificationStatus::Compared;
    save_certification_state(&certification_dir, &state)?;

    println!("\n{}", "=== AI Comparison Results ===".bold());
    println!(
        "Model: {}  |  Cost: ${:.4}\n",
        result.model, result.cost_usd
    );
    println!(
        "{}",
        "Scoring dimensions (1-10): succinctness = shorter/cleaner proofs,".dimmed()
    );
    println!(
        "{}",
        "library reuse = use of existing lemmas, generality = general vs specific,".dimmed()
    );
    println!(
        "{}",
        "modularity = decomposition into reusable parts, math strategy = proof elegance".dimmed()
    );
    println!();

    for pc in &result.conjecture_comparisons {
        println!("{} ({})", pc.conjecture_title.bold(), pc.conjecture_id);
        println!("  {}", pc.analysis);
        for r in &pc.rankings {
            println!(
                "    {} — overall: {} | succinctness: {} library: {} generality: {} modularity: {} strategy: {}",
                r.contributor_username,
                r.scores.overall,
                r.scores.succinctness,
                r.scores.library_reuse,
                r.scores.generality,
                r.scores.modularity,
                r.scores.math_strategy,
            );
            println!("      {}", r.reasoning);
        }
        println!();
    }

    println!("{}", "=== Package Rankings ===".bold());
    for pr in &result.package_rankings {
        println!(
            "  #{} {} — overall avg: {} ({} conjectures)",
            pr.rank, pr.contributor_username, pr.avg_scores.overall, pr.conjectures_compared
        );
        if !pr.summary.is_empty() {
            println!("     {}", pr.summary);
        }
    }

    println!(
        "\nComparison saved to: {}",
        comp_path.display().to_string().cyan()
    );

    Ok(())
}

// ── certificate report ──

pub fn cmd_report(template_variant: &str) -> Result<()> {
    let (certification_dir, state) = get_active_certification()?;
    let report_path = certification_dir.join("certification_report.toml");

    if !report_path.exists() {
        let comp_path = certification_dir.join("ai_comparison.json");
        let comparison: Option<ComparisonResult> = if comp_path.exists() {
            let content = std::fs::read_to_string(&comp_path)?;
            serde_json::from_str(&content).ok()
        } else {
            None
        };

        let template_content =
            templates::get_template(template_variant, &state, comparison.as_ref());
        std::fs::write(&report_path, &template_content)?;
        println!(
            "{} Certification report template written to: {}",
            "✓".green(),
            report_path.display()
        );

        if let Ok(editor) = std::env::var("EDITOR") {
            println!("Opening in {}...", editor);
            let _ = std::process::Command::new(&editor)
                .arg(&report_path)
                .status();
        } else {
            println!(
                "Edit the file manually: {}",
                report_path.display().to_string().cyan()
            );
        }
    } else {
        println!("Validating {}...\n", report_path.display());
        match templates::validate_report(&report_path) {
            Ok(errors) => {
                if errors.is_empty() {
                    println!("{} Report is valid and ready for sealing.", "✓".green());
                } else {
                    println!("{} Validation errors:", "✗".red());
                    for e in &errors {
                        println!("  - {}", e);
                    }
                }
            }
            Err(e) => {
                println!("{} Failed to parse report: {}", "✗".red(), e);
            }
        }
    }

    Ok(())
}

// ── certificate seal ──

pub async fn cmd_seal() -> Result<()> {
    let config = Config::load_or_default();
    config.require_login()?;
    let (certification_dir, mut state) = get_active_certification()?;

    let is_reseal = state.status == CertificationStatus::Sealed;

    let report_path = certification_dir.join("certification_report.toml");
    if !report_path.exists() {
        anyhow::bail!("certification_report.toml not found. Run `pah certificate report` first.");
    }

    let errors = templates::validate_report(&report_path)?;
    if !errors.is_empty() {
        println!("{} Report validation errors:", "✗".red());
        for e in &errors {
            println!("  - {}", e);
        }
        anyhow::bail!("Fix validation errors before sealing.");
    }

    let report = templates::parse_report(&report_path)?;

    let comp_path = certification_dir.join("ai_comparison.json");
    let comparison: Option<ComparisonResult> = if comp_path.exists() {
        let content = std::fs::read_to_string(&comp_path)?;
        serde_json::from_str(&content).ok()
    } else {
        eprintln!(
            "{}: ai_comparison.json not found. Sealing without AI comparison.",
            "Warning".yellow()
        );
        None
    };

    let top_contributor = report
        .package_assessments
        .iter()
        .min_by_key(|r| r.rank)
        .map(|r| r.contributor_username.clone())
        .unwrap_or_default();

    let conjectures_compared = comparison
        .as_ref()
        .map(|c| c.conjecture_comparisons.len() as u32)
        .unwrap_or(0);

    let ai_cost = comparison.as_ref().map(|c| c.cost_usd).unwrap_or(0.0);

    let summary_path = certification_dir.join("certification_summary.json");
    let package_ranking_summaries: Vec<serde_json::Value> = report
        .package_assessments
        .iter()
        .map(|r| {
            let overall_score = comparison
                .as_ref()
                .and_then(|c| {
                    c.package_rankings
                        .iter()
                        .find(|pr| pr.contributor_contribution_id == r.contributor_contribution_id)
                })
                .map(|pr| pr.avg_scores.overall as f64)
                .unwrap_or(0.0);

            serde_json::json!({
                "contributor_contribution_id": r.contributor_contribution_id,
                "rank": r.rank,
                "overall_score": overall_score,
            })
        })
        .collect();

    let summary = serde_json::json!({
        "certifier_username": report.certifier.username,
        "certification_id": state.certification_id,
        "packages_certified": state.packages.len(),
        "conjectures_compared": conjectures_compared,
        "package_rankings": package_ranking_summaries,
        "recommendation": report.summary.recommendation,
        "confidence": report.summary.confidence,
        "overall_assessment": report.summary.overall_assessment,
    });

    std::fs::write(&summary_path, serde_json::to_string_pretty(&summary)?)?;

    let archive_path = certification_dir.join("certification_package.tar.gz");
    create_certification_archive(&certification_dir, &archive_path)?;

    let server = ServerClient::new(&config.server_url(), &config.api.auth_token);

    let server_summary = crate::server_client::api::Certificate {
        certifier_username: report.certifier.username.clone(),
        certificate_id: state.certification_id.clone(),
        packages_certified: state.packages.len() as u32,
        conjectures_compared,
        package_rankings: report
            .package_assessments
            .iter()
            .map(|r| {
                let overall_score = comparison
                    .as_ref()
                    .and_then(|c| {
                        c.package_rankings.iter().find(|pr| {
                            pr.contributor_contribution_id == r.contributor_contribution_id
                        })
                    })
                    .map(|pr| pr.avg_scores.overall as f64)
                    .unwrap_or(0.0);

                crate::server_client::api::ContributionRanking {
                    contributor_contribution_id: r.contributor_contribution_id.clone(),
                    rank: r.rank,
                    overall_score,
                }
            })
            .collect(),
        recommendation: report.summary.recommendation.clone(),
        archive_sha256: String::new(),
        nft_metadata: serde_json::Value::Null,
    };

    print!("Submitting certificate to server... ");
    let commit_sha = match server.submit_certificate(&server_summary).await {
        Ok(resp) => {
            println!("{} ({})", "OK".green(), &resp.commit_sha[..8]);
            resp.commit_sha
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            anyhow::bail!("Could not submit certificate to server: {}", e);
        }
    };

    let (certifier_public_key, commit_signature) = match Config::signing_key_path()
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
                "{}: No signing key found. Run `pah setting set` to generate one.",
                "Warning".yellow()
            );
            (String::new(), String::new())
        }
    };

    let certified_contribution_ids: Vec<String> = state
        .packages
        .iter()
        .map(|p| p.contributor_contribution_id.clone())
        .collect();

    let nft_info = CertificateInfo {
        certifier_username: report.certifier.username.clone(),
        certificate_id: state.certification_id.clone(),
        packages_certified: state.packages.len() as u32,
        conjectures_compared,
        top_contributor: top_contributor.clone(),
        recommendation: report.summary.recommendation.clone(),
        ai_comparison_cost_usd: ai_cost,
        certified_contribution_ids,
        git_commit: commit_sha.clone(),
        git_repository: config.server_url(),
        certifier_public_key,
        commit_signature,
    };

    let nft_metadata = generate_certificate_nft_metadata(&nft_info);
    let nft_path = certification_dir.join("certification_nft_metadata.json");
    std::fs::write(&nft_path, serde_json::to_string_pretty(&nft_metadata)?)?;

    print!("Sealing certificate (creating PR)... ");
    match server
        .seal_certificate(&state.certification_id, &nft_metadata)
        .await
    {
        Ok(seal_resp) => {
            println!("{}", "OK".green());
            println!("  PR: {}", seal_resp.pr_url.cyan());
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not seal on server: {}", "Warning".yellow(), e);
        }
    }

    state.status = CertificationStatus::Sealed;
    save_certification_state(&certification_dir, &state)?;

    if is_reseal {
        println!(
            "\n{}: Previous NFT metadata overwritten. Re-publish if you already published.",
            "Note".yellow()
        );
    }

    println!("\n{}", "=== Certification Sealed ===".bold());
    println!("  Certification ID: {}", state.certification_id);
    println!("  Archive:      {}", archive_path.display());
    println!("  Git Commit:   {}", commit_sha);
    println!("  NFT metadata: {}", nft_path.display());
    println!("  Packages:     {}", state.packages.len());
    println!("  Compared:     {} conjectures", conjectures_compared);
    println!("  Top contributor: {}", top_contributor);
    println!("  Recommendation: {}", report.summary.recommendation);

    Ok(())
}

// ── certificate publish (delegates to publish module) ──

pub async fn cmd_publish(id: &str) -> Result<()> {
    super::publish::run_publish("certificate", id).await
}

// ── Helpers ──

fn extract_archive(archive_path: &Path, dest_dir: &Path) -> Result<()> {
    let file = std::fs::File::open(archive_path)
        .with_context(|| format!("Failed to open {}", archive_path.display()))?;
    let decoder = flate2::read::GzDecoder::new(file);
    let mut archive = tar::Archive::new(decoder);
    archive
        .unpack(dest_dir)
        .with_context(|| format!("Failed to extract {}", archive_path.display()))?;
    Ok(())
}

fn compute_sha256(path: &Path) -> Result<String> {
    let data = std::fs::read(path)?;
    let hash = Sha256::digest(&data);
    Ok(hex::encode(hash))
}

fn scan_proof_files(dir: &Path) -> Result<Vec<String>> {
    let mut ids = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
                if ext == "v" || ext == "lean" {
                    if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                        ids.push(stem.to_string());
                    }
                }
            }
        }
    }
    ids.sort();
    Ok(ids)
}

fn create_certification_archive(certification_dir: &Path, archive_path: &Path) -> Result<()> {
    let file = std::fs::File::create(archive_path)?;
    let encoder = flate2::write::GzEncoder::new(file, flate2::Compression::default());
    let mut tar_builder = tar::Builder::new(encoder);

    let items = [
        "packages",
        "ai_comparison.json",
        "certification_report.toml",
        "certification_summary.json",
        "certification_audit.jsonl",
    ];

    for item in &items {
        let item_path = certification_dir.join(item);
        if !item_path.exists() {
            continue;
        }
        if item_path.is_dir() {
            tar_builder
                .append_dir_all(*item, &item_path)
                .with_context(|| format!("Failed to add {} to archive", item))?;
        } else {
            let mut f = std::fs::File::open(&item_path)?;
            tar_builder
                .append_file(*item, &mut f)
                .with_context(|| format!("Failed to add {} to archive", item))?;
        }
    }

    tar_builder.finish()?;
    Ok(())
}
