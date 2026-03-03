use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::path::Path;
use std::process::Command;

use crate::config::types::Config;
use crate::server_client::api::ServerClient;

pub async fn cmd_clone(dir: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    let pool_dir = if let Some(d) = dir {
        std::path::PathBuf::from(d)
    } else {
        cfg.pool_dir()?
    };

    // If pool dir already exists with .git, suggest pull
    if pool_dir.join(".git").exists() {
        println!("Already cloned at {}", pool_dir.display());
        println!("Use {} to update.", "pah pool pull".bold());
        return Ok(());
    }

    // Fetch pool URL from server
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let git_url = client.get_pool_url().await?;

    println!("Cloning pool from {} ...", git_url);

    let status = Command::new("git")
        .args(["clone", &git_url, &pool_dir.to_string_lossy()])
        .status()
        .context("Failed to run git clone")?;

    if !status.success() {
        bail!("git clone failed");
    }

    // Auto-configure git identity from config.toml
    configure_git_identity(&pool_dir, &cfg)?;

    println!("{} Pool cloned to {}", "Done.".green(), pool_dir.display());
    Ok(())
}

pub async fn cmd_pull() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;
    require_pool_dir(&pool_dir)?;

    println!("Fetching latest changes...");

    let fetch = Command::new("git")
        .args(["fetch", "origin"])
        .current_dir(&pool_dir)
        .status()
        .context("Failed to run git fetch")?;

    if !fetch.success() {
        bail!("git fetch failed");
    }

    let rebase = Command::new("git")
        .args(["rebase", "origin/main"])
        .current_dir(&pool_dir)
        .output()
        .context("Failed to run git rebase")?;

    if !rebase.status.success() {
        let stderr = String::from_utf8_lossy(&rebase.stderr);
        if stderr.contains("CONFLICT") || stderr.contains("conflict") {
            eprintln!("{}", "Rebase conflict detected.".yellow());
            eprintln!("Resolve conflicts in {}, then run:", pool_dir.display());
            eprintln!("  cd {} && git rebase --continue", pool_dir.display());
            eprintln!("Or abort with:");
            eprintln!("  cd {} && git rebase --abort", pool_dir.display());
            return Ok(());
        }
        bail!("git rebase failed: {}", stderr);
    }

    println!("{} Pool is up to date.", "Done.".green());
    Ok(())
}

pub async fn cmd_push() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;
    require_pool_dir(&pool_dir)?;

    println!("Pushing to remote...");

    let output = Command::new("git")
        .args(["push", "origin", "HEAD"])
        .current_dir(&pool_dir)
        .output()
        .context("Failed to run git push")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("Authentication") || stderr.contains("403") || stderr.contains("401") {
            eprintln!("{}", "Push failed: authentication error.".red());
            eprintln!("Check your credentials with: {}", "pah auth status".bold());
            return Ok(());
        }
        bail!("git push failed: {}", stderr);
    }

    println!("{} Changes pushed.", "Done.".green());
    Ok(())
}

pub async fn cmd_status() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;
    require_pool_dir(&pool_dir)?;

    let output = Command::new("git")
        .args(["status"])
        .current_dir(&pool_dir)
        .output()
        .context("Failed to run git status")?;

    if !output.status.success() {
        bail!(
            "git status failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    print!("{}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}

fn require_pool_dir(pool_dir: &Path) -> Result<()> {
    if !pool_dir.join(".git").exists() {
        bail!(
            "Pool not found at {}. Run {} first.",
            pool_dir.display(),
            "pah pool clone".bold()
        );
    }
    Ok(())
}

fn configure_git_identity(pool_dir: &Path, cfg: &Config) -> Result<()> {
    let name = if !cfg.identity.real_name.is_empty() {
        &cfg.identity.real_name
    } else if !cfg.identity.username.is_empty() {
        &cfg.identity.username
    } else {
        return Ok(());
    };

    Command::new("git")
        .args(["config", "user.name", name])
        .current_dir(pool_dir)
        .status()
        .context("Failed to set git user.name")?;

    if !cfg.identity.email.is_empty() {
        Command::new("git")
            .args(["config", "user.email", &cfg.identity.email])
            .current_dir(pool_dir)
            .status()
            .context("Failed to set git user.email")?;
    }

    Ok(())
}
