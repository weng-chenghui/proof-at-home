use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

use crate::config::Config;
use crate::nft::metadata::{generate_submitter_nft_metadata, ConjectureSubmitterInfo};
use crate::server_client::api::{ConjectureCreateResponse, ServerClient};
use crate::signing;

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let conjectures = client.fetch_conjectures().await?;

    if conjectures.is_empty() {
        println!("No conjectures found.");
        return Ok(());
    }

    println!(
        "{:<40} {:<30} {:<12} {:<10} {:<10}",
        "ID", "Title", "Difficulty", "Prover", "Status"
    );
    println!("{}", "-".repeat(102));

    for c in &conjectures {
        let display_id = if c.id.len() > 36 { &c.id[..36] } else { &c.id };
        let display_title = if c.title.len() > 28 {
            format!("{}…", &c.title[..27])
        } else {
            c.title.clone()
        };
        println!(
            "{:<40} {:<30} {:<12} {:<10} {:<10}",
            display_id, display_title, c.difficulty, c.prover, c.status
        );
    }

    println!("\nTotal: {}", conjectures.len());
    Ok(())
}

pub async fn cmd_get(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let c = client.fetch_conjecture(id).await?;

    println!("{}", "=== Conjecture ===".bold());
    println!("ID:         {}", c.id);
    println!("Title:      {}", c.title);
    println!("Difficulty: {}", c.difficulty);
    println!("Prover:     {}", c.prover);
    println!("Status:     {}", c.status);
    if !c.preamble.is_empty() {
        println!("\nPreamble:\n{}", c.preamble);
    }
    if !c.lemma_statement.is_empty() {
        println!("\nLemma Statement:\n{}", c.lemma_statement);
    }
    if !c.hints.is_empty() {
        println!("\nHints:");
        for h in &c.hints {
            println!("  - {}", h);
        }
    }
    if !c.skeleton.is_empty() {
        println!("\nSkeleton:\n{}", c.skeleton);
    }

    Ok(())
}

pub async fn cmd_create(source: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let resp = if is_git_url(source) {
        println!("{} Submitting git URL: {}", "→".blue(), source);
        client.create_conjecture_git_url(source).await?
    } else {
        let path = Path::new(source);
        if !path.exists() {
            anyhow::bail!("Source path does not exist: {}", source);
        }

        if path.is_dir() {
            println!("{} Packaging directory: {}", "→".blue(), source);
            let tar_bytes = tar_directory(path)?;
            client.create_conjecture_tar(tar_bytes).await?
        } else if source.ends_with(".tar.gz") || source.ends_with(".tgz") {
            println!("{} Submitting archive: {}", "→".blue(), source);
            let tar_bytes =
                std::fs::read(path).with_context(|| format!("Failed to read {}", source))?;
            client.create_conjecture_tar(tar_bytes).await?
        } else {
            anyhow::bail!(
                "Unsupported source: {}. Expected a directory, .tar.gz file, or git URL.",
                source
            );
        }
    };

    print_result(&resp);
    seal_submitter_nft(&cfg, &client, &resp).await?;

    Ok(())
}

pub async fn cmd_seal(batch_id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let (public_key, commit_signature) = sign_if_possible(&cfg, batch_id);

    let nft_info = ConjectureSubmitterInfo {
        submitter_username: cfg.identity.username.clone(),
        batch_id: batch_id.to_string(),
        conjectures_submitted: 0,
        conjecture_ids: Vec::new(),
        difficulties: Vec::new(),
        proof_assistants: Vec::new(),
        git_commit: batch_id.to_string(),
        git_repository: cfg.server_url(),
        public_key,
        commit_signature,
    };

    let nft_metadata = generate_submitter_nft_metadata(&nft_info);

    print!("Sealing conjecture batch (creating PR)... ");
    match client.seal_conjecture_batch(batch_id, &nft_metadata).await {
        Ok(seal_resp) => {
            println!("{}", "OK".green());
            if !seal_resp.pr_url.is_empty() {
                println!("  PR: {}", seal_resp.pr_url.cyan());
            }
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not seal on server: {}", "Warning".yellow(), e);
        }
    }

    println!("\n{}", "=== Conjecture Batch Sealed ===".bold());
    println!("  Batch ID: {}", batch_id);

    Ok(())
}

// ── Helpers ──

async fn seal_submitter_nft(
    cfg: &Config,
    client: &ServerClient,
    resp: &ConjectureCreateResponse,
) -> Result<()> {
    let commit_sha = &resp.commit_sha;

    let (public_key, commit_signature) = sign_if_possible(cfg, commit_sha);

    let nft_info = ConjectureSubmitterInfo {
        submitter_username: cfg.identity.username.clone(),
        batch_id: resp.batch_id.clone(),
        conjectures_submitted: resp.count,
        conjecture_ids: resp.added_conjecture_ids.clone(),
        difficulties: resp.difficulties.clone(),
        proof_assistants: resp.proof_assistants.clone(),
        git_commit: commit_sha.clone(),
        git_repository: cfg.server_url(),
        public_key,
        commit_signature,
    };

    let nft_metadata = generate_submitter_nft_metadata(&nft_info);

    print!("Sealing conjecture submission (creating PR)... ");
    match client
        .seal_conjecture_batch(&resp.batch_id, &nft_metadata)
        .await
    {
        Ok(seal_resp) => {
            println!("{}", "OK".green());
            if !seal_resp.pr_url.is_empty() {
                println!("  PR: {}", seal_resp.pr_url.cyan());
            }
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not seal on server: {}", "Warning".yellow(), e);
        }
    }

    println!("\n{}", "=== Conjecture Submission Sealed ===".bold());
    println!("  Batch ID:    {}", resp.batch_id);
    println!("  Git Commit:  {}", commit_sha);
    println!("  Conjectures: {}", resp.count);

    Ok(())
}

fn sign_if_possible(cfg: &Config, commit_sha: &str) -> (String, String) {
    match Config::signing_key_path()
        .ok()
        .filter(|p| p.exists())
        .and_then(|p| std::fs::read_to_string(&p).ok())
    {
        Some(key_hex) => match signing::load_signing_key(&key_hex) {
            Ok(key) => {
                let sig = signing::sign_commit(&key, commit_sha).unwrap_or_default();
                (cfg.identity.public_key.clone(), sig)
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
    }
}

fn is_git_url(source: &str) -> bool {
    source.starts_with("http://")
        || source.starts_with("https://")
        || source.starts_with("git@")
        || source.starts_with("git://")
}

fn tar_directory(dir: &Path) -> Result<Vec<u8>> {
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use std::fs;
    use tar::Builder;

    let buf = Vec::new();
    let enc = GzEncoder::new(buf, Compression::default());
    let mut ar = Builder::new(enc);

    for entry in fs::read_dir(dir).context("Failed to read directory")? {
        let entry = entry?;
        let path = entry.path();
        if path.is_file() && path.extension().and_then(|e| e.to_str()) == Some("json") {
            let name = entry.file_name();
            ar.append_path_with_name(&path, &name)
                .with_context(|| format!("Failed to add {} to archive", path.display()))?;
        }
    }

    let enc = ar.into_inner().context("Failed to finish tar archive")?;
    let bytes = enc.finish().context("Failed to finish gzip")?;
    Ok(bytes)
}

fn print_result(resp: &ConjectureCreateResponse) {
    println!("{} {} conjecture(s) added", "✓".green(), resp.count);
    if !resp.added_conjecture_ids.is_empty() {
        println!("  IDs: {}", resp.added_conjecture_ids.join(", "));
    }
}
