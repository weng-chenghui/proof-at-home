use anyhow::{Context, Result};
use chrono::Utc;
use colored::Colorize;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

use crate::config::Config;
use crate::nft::metadata::generate_review_nft_metadata;
use crate::nft::metadata::ReviewInfo;
use crate::reviewer::comparison;
use crate::reviewer::templates;
use crate::reviewer::types::*;
use crate::server_client::api::ServerClient;
use crate::signing;

/// Resolve the reviews base directory: ~/.proof-at-home/reviews/
fn reviews_dir() -> Result<PathBuf> {
    let dir = Config::config_dir()?.join("reviews");
    std::fs::create_dir_all(&dir)?;
    Ok(dir)
}

/// Path to the active review pointer file
fn active_review_path() -> Result<PathBuf> {
    Ok(Config::config_dir()?.join("active_review"))
}

/// Get the active review session ID (if any)
fn get_active_review_id() -> Result<Option<String>> {
    let path = active_review_path()?;
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

/// Set the active review session ID
fn set_active_review_id(id: &str) -> Result<()> {
    let path = active_review_path()?;
    std::fs::write(&path, id)?;
    Ok(())
}

/// Load a review session from its directory
fn load_session(review_dir: &Path) -> Result<ReviewSession> {
    let session_path = review_dir.join("review_session.json");
    let content = std::fs::read_to_string(&session_path)
        .with_context(|| format!("Failed to read {}", session_path.display()))?;
    let session: ReviewSession =
        serde_json::from_str(&content).context("Failed to parse review_session.json")?;
    Ok(session)
}

/// Save a review session to its directory
fn save_session(review_dir: &Path, session: &ReviewSession) -> Result<()> {
    let session_path = review_dir.join("review_session.json");
    let content = serde_json::to_string_pretty(session)?;
    std::fs::write(&session_path, content)?;
    Ok(())
}

/// Get the active review session directory and loaded session
fn get_active_session() -> Result<(PathBuf, ReviewSession)> {
    let review_id = get_active_review_id()?
        .context("No active review session. Run `proof-at-home review start` first.")?;
    let review_dir = reviews_dir()?.join(&review_id);
    if !review_dir.exists() {
        anyhow::bail!(
            "Review session directory not found: {}. Run `proof-at-home review start`.",
            review_dir.display()
        );
    }
    let session = load_session(&review_dir)?;
    Ok((review_dir, session))
}

// ── Subcommand dispatch ──

use clap::Subcommand;

#[derive(Subcommand)]
pub enum ReviewAction {
    /// Start a new review session (optionally fetch packages from server)
    Start,
    /// Import a local proof archive into the active review session
    Import {
        /// Path to a proof archive (.tar.gz)
        path: PathBuf,
    },
    /// List packages loaded in the active review session
    List,
    /// AI-compare proofs across packages
    AiCompare,
    /// Generate or edit review report from template
    Report {
        /// Template variant: default, minimal, detailed
        #[arg(long, default_value = "default")]
        template: String,
    },
    /// Seal review package with NFT metadata
    Seal,
}

pub async fn run_review(action: ReviewAction) -> Result<()> {
    match action {
        ReviewAction::Start => cmd_start().await,
        ReviewAction::Import { path } => cmd_import(&path).await,
        ReviewAction::List => cmd_list(),
        ReviewAction::AiCompare => cmd_ai_compare().await,
        ReviewAction::Report { template } => cmd_report(&template),
        ReviewAction::Seal => cmd_seal().await,
    }
}

// ── review start ──

async fn cmd_start() -> Result<()> {
    let config = Config::load()?;
    let review_id = uuid::Uuid::new_v4().to_string();
    let review_dir = reviews_dir()?.join(&review_id);
    let packages_dir = review_dir.join("packages");
    std::fs::create_dir_all(&packages_dir)?;

    let mut session = ReviewSession {
        review_id: review_id.clone(),
        reviewer_username: config.identity.username.clone(),
        created_at: Utc::now().to_rfc3339(),
        packages: Vec::new(),
        status: ReviewStatus::Open,
    };

    // Try to fetch available packages from server
    let server = ServerClient::new(&config.api.server_url, &config.api.auth_token);
    let available = match server.fetch_review_packages().await {
        Ok(pkgs) => pkgs,
        Err(e) => {
            eprintln!(
                "{}: Could not fetch packages from server: {}",
                "Warning".yellow(),
                e
            );
            eprintln!("You can import local archives with `proof-at-home review import <path>`.");
            Vec::new()
        }
    };

    if !available.is_empty() {
        println!("Available proof packages from server:\n");
        let items: Vec<String> = available
            .iter()
            .map(|p| {
                format!(
                    "{} ({}) — {} problems [{}]",
                    p.prover_username,
                    &p.prover_session_id[..8],
                    p.problem_ids.len(),
                    p.proof_assistant,
                )
            })
            .collect();

        let selections = dialoguer::MultiSelect::new()
            .with_prompt("Select packages to include (space to toggle, enter to confirm)")
            .items(&items)
            .interact()?;

        for idx in selections {
            let pkg_info = &available[idx];
            let dest_dir = packages_dir.join(&pkg_info.prover_session_id);
            std::fs::create_dir_all(&dest_dir)?;

            print!(
                "  Downloading {} ({})...",
                pkg_info.prover_username,
                &pkg_info.prover_session_id[..8]
            );
            let archive_dest = dest_dir.join("proofs.tar.gz");
            match server
                .download_package(&pkg_info.prover_session_id, &archive_dest)
                .await
            {
                Ok(()) => {
                    println!(" {}", "done".green());
                    // Extract archive
                    extract_archive(&archive_dest, &dest_dir)?;

                    // Compute SHA-256
                    let sha = compute_sha256(&archive_dest)?;

                    session.packages.push(ProofPackage {
                        prover_session_id: pkg_info.prover_session_id.clone(),
                        prover_username: pkg_info.prover_username.clone(),
                        proof_assistant: pkg_info.proof_assistant.clone(),
                        problem_ids: pkg_info.problem_ids.clone(),
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

    save_session(&review_dir, &session)?;
    set_active_review_id(&review_id)?;

    println!("\n{} Review session created: {}", "✓".green(), review_id);
    println!("  Directory: {}", review_dir.display());
    println!("  Packages loaded: {}", session.packages.len());
    if session.packages.is_empty() {
        println!(
            "\n  Import local archives with: {}",
            "proof-at-home review import <path>".cyan()
        );
    }

    Ok(())
}

// ── review import ──

async fn cmd_import(path: &Path) -> Result<()> {
    let (review_dir, mut session) = get_active_session()?;

    if session.status == ReviewStatus::Sealed {
        anyhow::bail!("Cannot import into a sealed review session.");
    }

    if !path.exists() {
        anyhow::bail!("Archive not found: {}", path.display());
    }

    let packages_dir = review_dir.join("packages");

    // Derive a session ID from the archive filename or generate one
    let archive_stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");
    // Strip .tar if double extension
    let session_id = archive_stem.strip_suffix(".tar").unwrap_or(archive_stem);
    let dest_dir = packages_dir.join(session_id);
    std::fs::create_dir_all(&dest_dir)?;

    // Copy archive
    let archive_dest = dest_dir.join("proofs.tar.gz");
    std::fs::copy(path, &archive_dest)
        .with_context(|| format!("Failed to copy archive to {}", archive_dest.display()))?;

    // Extract
    extract_archive(&archive_dest, &dest_dir)?;

    // Compute SHA-256
    let sha = compute_sha256(&archive_dest)?;

    // Scan for proof files to build problem_ids list
    let problem_ids = scan_proof_files(&dest_dir)?;

    // Detect proof assistant
    let proof_assistant = if problem_ids
        .iter()
        .any(|p| dest_dir.join(format!("{}.lean", p)).exists())
    {
        "lean".into()
    } else {
        "rocq".into()
    };

    session.packages.push(ProofPackage {
        prover_session_id: session_id.to_string(),
        prover_username: String::new(), // unknown for local imports
        proof_assistant,
        problem_ids: problem_ids.clone(),
        archive_sha256: sha,
        import_source: format!("local:{}", path.display()),
    });

    save_session(&review_dir, &session)?;

    println!(
        "{} Imported {} ({} proof files)",
        "✓".green(),
        session_id,
        problem_ids.len()
    );

    Ok(())
}

// ── review list ──

fn cmd_list() -> Result<()> {
    let (_review_dir, session) = get_active_session()?;

    println!(
        "Review session: {} (status: {})\n",
        session.review_id, session.status
    );

    if session.packages.is_empty() {
        println!("  No packages loaded.");
        return Ok(());
    }

    println!(
        "  {:<40} {:<20} {:<10} {:<8}",
        "Session ID", "Prover", "Assistant", "Problems"
    );
    println!("  {}", "-".repeat(78));

    for pkg in &session.packages {
        let display_id = if pkg.prover_session_id.len() > 36 {
            &pkg.prover_session_id[..36]
        } else {
            &pkg.prover_session_id
        };
        println!(
            "  {:<40} {:<20} {:<10} {:<8}",
            display_id,
            if pkg.prover_username.is_empty() {
                "(local)"
            } else {
                &pkg.prover_username
            },
            pkg.proof_assistant,
            pkg.problem_ids.len(),
        );
    }

    println!("\n  Total packages: {}", session.packages.len());
    Ok(())
}

// ── review ai-compare ──

async fn cmd_ai_compare() -> Result<()> {
    let config = Config::load()?;
    let (review_dir, mut session) = get_active_session()?;

    if session.packages.len() < 2 {
        anyhow::bail!("Need at least 2 packages to compare. Import more packages first.");
    }

    let result = comparison::run_comparison(&config, &session, &review_dir).await?;

    // Write ai_comparison.json
    let comp_path = review_dir.join("ai_comparison.json");
    let content = serde_json::to_string_pretty(&result)?;
    std::fs::write(&comp_path, content)?;

    // Update session status
    session.status = ReviewStatus::Compared;
    save_session(&review_dir, &session)?;

    // Print results table
    println!("\n{}", "=== AI Comparison Results ===".bold());
    println!(
        "Model: {}  |  Cost: ${:.4}\n",
        result.model, result.cost_usd
    );

    for pc in &result.problem_comparisons {
        println!("{} ({})", pc.problem_title.bold(), pc.problem_id);
        println!("  {}", pc.analysis);
        for r in &pc.rankings {
            println!(
                "    {} — overall: {} | suc: {} lib: {} gen: {} mod: {} math: {}",
                r.prover_username,
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
            "  #{} {} — overall avg: {} ({} problems)",
            pr.rank, pr.prover_username, pr.avg_scores.overall, pr.problems_compared
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

// ── review report ──

fn cmd_report(template_variant: &str) -> Result<()> {
    let (review_dir, session) = get_active_session()?;
    let report_path = review_dir.join("review_report.toml");

    if !report_path.exists() {
        // Load AI comparison if available
        let comp_path = review_dir.join("ai_comparison.json");
        let comparison: Option<ComparisonResult> = if comp_path.exists() {
            let content = std::fs::read_to_string(&comp_path)?;
            serde_json::from_str(&content).ok()
        } else {
            None
        };

        let template_content =
            templates::get_template(template_variant, &session, comparison.as_ref());
        std::fs::write(&report_path, &template_content)?;
        println!(
            "{} Review report template written to: {}",
            "✓".green(),
            report_path.display()
        );

        // Try to open in $EDITOR
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
        // Validate existing report
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

// ── review seal ──

async fn cmd_seal() -> Result<()> {
    let config = Config::load()?;
    let (review_dir, mut session) = get_active_session()?;

    // 1. Validate report exists and is valid
    let report_path = review_dir.join("review_report.toml");
    if !report_path.exists() {
        anyhow::bail!("review_report.toml not found. Run `proof-at-home review report` first.");
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

    // 2. Check for AI comparison (warn if missing)
    let comp_path = review_dir.join("ai_comparison.json");
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

    // 3. Build review_summary.json
    let top_prover = report
        .package_reviews
        .iter()
        .min_by_key(|r| r.rank)
        .map(|r| r.prover_username.clone())
        .unwrap_or_default();

    let package_ranking_summaries: Vec<serde_json::Value> = report
        .package_reviews
        .iter()
        .map(|r| {
            let overall_score = comparison
                .as_ref()
                .and_then(|c| {
                    c.package_rankings
                        .iter()
                        .find(|pr| pr.prover_session_id == r.prover_session_id)
                })
                .map(|pr| pr.avg_scores.overall as f64)
                .unwrap_or(0.0);

            serde_json::json!({
                "prover_session_id": r.prover_session_id,
                "rank": r.rank,
                "overall_score": overall_score,
            })
        })
        .collect();

    let problems_compared = comparison
        .as_ref()
        .map(|c| c.problem_comparisons.len() as u32)
        .unwrap_or(0);

    let ai_cost = comparison.as_ref().map(|c| c.cost_usd).unwrap_or(0.0);

    let summary = serde_json::json!({
        "reviewer_username": report.reviewer.username,
        "review_id": session.review_id,
        "packages_reviewed": session.packages.len(),
        "problems_compared": problems_compared,
        "package_rankings": package_ranking_summaries,
        "recommendation": report.summary.recommendation,
        "confidence": report.summary.confidence,
        "overall_assessment": report.summary.overall_assessment,
    });

    let summary_path = review_dir.join("review_summary.json");
    std::fs::write(&summary_path, serde_json::to_string_pretty(&summary)?)?;

    // 4. Archive everything into review_package.tar.gz
    let archive_path = review_dir.join("review_package.tar.gz");
    create_review_archive(&review_dir, &archive_path)?;

    // 5. Compute SHA-256
    let archive_sha = compute_sha256(&archive_path)?;

    // 5b. Sign archive hash
    let (reviewer_public_key, archive_signature) = match Config::signing_key_path()
        .ok()
        .filter(|p| p.exists())
        .and_then(|p| std::fs::read_to_string(&p).ok())
    {
        Some(key_hex) => match signing::load_signing_key(&key_hex) {
            Ok(key) => {
                let sig = signing::sign_hash(&key, &archive_sha).unwrap_or_default();
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

    // 6. Generate NFT metadata
    let reviewed_session_ids: Vec<String> = session
        .packages
        .iter()
        .map(|p| p.prover_session_id.clone())
        .collect();

    let nft_info = ReviewInfo {
        reviewer_username: report.reviewer.username.clone(),
        review_id: session.review_id.clone(),
        packages_reviewed: session.packages.len() as u32,
        problems_compared,
        top_prover: top_prover.clone(),
        recommendation: report.summary.recommendation.clone(),
        archive_sha256: archive_sha.clone(),
        ai_comparison_cost_usd: ai_cost,
        reviewed_session_ids,
        reviewer_public_key,
        archive_signature,
    };

    let nft_metadata = generate_review_nft_metadata(&nft_info);
    let nft_path = review_dir.join("review_nft_metadata.json");
    std::fs::write(&nft_path, serde_json::to_string_pretty(&nft_metadata)?)?;

    // 7. Submit to server
    let server = ServerClient::new(&config.api.server_url, &config.api.auth_token);

    let server_summary = crate::server_client::api::ReviewSummary {
        reviewer_username: report.reviewer.username.clone(),
        review_id: session.review_id.clone(),
        packages_reviewed: session.packages.len() as u32,
        problems_compared,
        package_rankings: report
            .package_reviews
            .iter()
            .map(|r| {
                let overall_score = comparison
                    .as_ref()
                    .and_then(|c| {
                        c.package_rankings
                            .iter()
                            .find(|pr| pr.prover_session_id == r.prover_session_id)
                    })
                    .map(|pr| pr.avg_scores.overall as f64)
                    .unwrap_or(0.0);

                crate::server_client::api::PackageRankingSummary {
                    prover_session_id: r.prover_session_id.clone(),
                    rank: r.rank,
                    overall_score,
                }
            })
            .collect(),
        recommendation: report.summary.recommendation.clone(),
        archive_sha256: archive_sha.clone(),
        nft_metadata: nft_metadata.clone(),
    };

    match server.submit_review(&server_summary).await {
        Ok(()) => println!("{} Review submitted to server.", "✓".green()),
        Err(e) => eprintln!("{}: Could not submit to server: {}", "Warning".yellow(), e),
    }

    // 8. Mark session as sealed
    session.status = ReviewStatus::Sealed;
    save_session(&review_dir, &session)?;

    // Print summary
    println!("\n{}", "=== Review Sealed ===".bold());
    println!("  Review ID:    {}", session.review_id);
    println!("  Archive:      {}", archive_path.display());
    println!("  SHA-256:      {}", archive_sha);
    println!("  NFT metadata: {}", nft_path.display());
    println!("  Packages:     {}", session.packages.len());
    println!("  Compared:     {} problems", problems_compared);
    println!("  Top prover:   {}", top_prover);
    println!("  Recommendation: {}", report.summary.recommendation);

    Ok(())
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

/// Scan a directory for .v and .lean files, return problem IDs (file stems)
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

/// Create a tar.gz archive of the review directory contents (excluding the archive itself)
fn create_review_archive(review_dir: &Path, archive_path: &Path) -> Result<()> {
    let file = std::fs::File::create(archive_path)?;
    let encoder = flate2::write::GzEncoder::new(file, flate2::Compression::default());
    let mut tar_builder = tar::Builder::new(encoder);

    // Add specific files/dirs
    let items = [
        "packages",
        "ai_comparison.json",
        "review_report.toml",
        "review_summary.json",
        "review_audit.jsonl",
    ];

    for item in &items {
        let item_path = review_dir.join(item);
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
