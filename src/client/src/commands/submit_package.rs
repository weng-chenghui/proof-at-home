use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

use crate::config::Config;
use crate::server_client::api::ServerClient;

pub async fn run_submit_package(source: &str) -> Result<()> {
    let cfg = Config::load()?;
    let client = ServerClient::new(&cfg.api.server_url, &cfg.api.auth_token);

    // Detect source type
    if is_git_url(source) {
        println!("{} Submitting git URL: {}", "→".blue(), source);
        let resp = client.submit_package_git_url(source).await?;
        print_result(&resp);
    } else {
        let path = Path::new(source);
        if !path.exists() {
            anyhow::bail!("Source path does not exist: {}", source);
        }

        if path.is_dir() {
            println!("{} Packaging directory: {}", "→".blue(), source);
            let tar_bytes = tar_directory(path)?;
            let resp = client.submit_package_tar(tar_bytes).await?;
            print_result(&resp);
        } else if source.ends_with(".tar.gz") || source.ends_with(".tgz") {
            println!("{} Submitting archive: {}", "→".blue(), source);
            let tar_bytes =
                std::fs::read(path).with_context(|| format!("Failed to read {}", source))?;
            let resp = client.submit_package_tar(tar_bytes).await?;
            print_result(&resp);
        } else {
            anyhow::bail!(
                "Unsupported source: {}. Expected a directory, .tar.gz file, or git URL.",
                source
            );
        }
    }

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

fn print_result(resp: &crate::server_client::api::PackageSubmitResponse) {
    println!("{} {} conjecture(s) added", "✓".green(), resp.count);
    if !resp.added_conjecture_ids.is_empty() {
        println!("  IDs: {}", resp.added_conjecture_ids.join(", "));
    }
}
