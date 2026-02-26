use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

use crate::config::Config;
use crate::nft::metadata::{generate_submitter_nft_metadata, ConjectureSubmitterInfo};
use crate::server_client::api::{ConjectureCreateResponse, ServerClient};
use crate::signing;

pub async fn run_submit_package(source: &str) -> Result<()> {
    let cfg = Config::load()?;
    let client = ServerClient::new(&cfg.api.server_url, &cfg.api.auth_token);

    // Detect source type
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

    // Generate submitter NFT metadata, sign, and seal
    seal_submitter_nft(&cfg, &client, &resp).await?;

    Ok(())
}

async fn seal_submitter_nft(
    cfg: &Config,
    client: &ServerClient,
    resp: &ConjectureCreateResponse,
) -> Result<()> {
    let commit_sha = &resp.commit_sha;

    // Sign the commit SHA
    let (public_key, commit_signature) = match Config::signing_key_path()
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
                "{}: No signing key found. Run `proof-at-home init` to generate one.",
                "Warning".yellow()
            );
            (String::new(), String::new())
        }
    };

    let nft_info = ConjectureSubmitterInfo {
        submitter_username: cfg.identity.username.clone(),
        batch_id: resp.batch_id.clone(),
        conjectures_submitted: resp.count,
        conjecture_ids: resp.added_conjecture_ids.clone(),
        difficulties: resp.difficulties.clone(),
        proof_assistants: resp.proof_assistants.clone(),
        git_commit: commit_sha.clone(),
        git_repository: cfg.api.server_url.clone(),
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
