use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::path::Path;
use std::process::Command;

use crate::config::types::{Config, Identity};
use crate::server_client::api::ServerClient;

// ── Extracted testable functions ──

/// Clone a git repo into `pool_dir` and configure identity.
/// Returns Ok(()) if already cloned.
pub fn clone_pool(pool_dir: &Path, git_url: &str, identity: &Identity) -> Result<()> {
    if pool_dir.join(".git").exists() {
        return Ok(());
    }

    let status = Command::new("git")
        .args(["clone", git_url, &pool_dir.to_string_lossy()])
        .status()
        .context("Failed to run git clone")?;

    if !status.success() {
        bail!("git clone failed");
    }

    configure_git_identity(pool_dir, identity)?;
    Ok(())
}

/// Fetch + rebase from origin's default branch.
pub fn pull_pool(pool_dir: &Path) -> Result<()> {
    require_pool_dir(pool_dir)?;

    let fetch = Command::new("git")
        .args(["fetch", "origin"])
        .current_dir(pool_dir)
        .status()
        .context("Failed to run git fetch")?;

    if !fetch.success() {
        bail!("git fetch failed");
    }

    // Detect origin's default branch (e.g. origin/main or origin/master)
    let head_ref = Command::new("git")
        .args(["symbolic-ref", "refs/remotes/origin/HEAD"])
        .current_dir(pool_dir)
        .output()
        .ok()
        .and_then(|o| {
            if o.status.success() {
                let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
                // "refs/remotes/origin/main" -> "origin/main"
                s.strip_prefix("refs/remotes/").map(|b| b.to_string())
            } else {
                None
            }
        })
        .unwrap_or_else(|| "origin/main".to_string());

    let rebase = Command::new("git")
        .args(["rebase", &head_ref])
        .current_dir(pool_dir)
        .output()
        .context("Failed to run git rebase")?;

    if !rebase.status.success() {
        let stderr = String::from_utf8_lossy(&rebase.stderr);
        if stderr.contains("CONFLICT") || stderr.contains("conflict") {
            bail!("Rebase conflict detected");
        }
        bail!("git rebase failed: {}", stderr);
    }

    Ok(())
}

/// Push HEAD to origin.
pub fn push_pool(pool_dir: &Path) -> Result<()> {
    require_pool_dir(pool_dir)?;

    let output = Command::new("git")
        .args(["push", "origin", "HEAD"])
        .current_dir(pool_dir)
        .output()
        .context("Failed to run git push")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("git push failed: {}", stderr);
    }

    Ok(())
}

/// Return `git status` output as a string.
pub fn status_pool(pool_dir: &Path) -> Result<String> {
    require_pool_dir(pool_dir)?;

    let output = Command::new("git")
        .args(["status"])
        .current_dir(pool_dir)
        .output()
        .context("Failed to run git status")?;

    if !output.status.success() {
        bail!(
            "git status failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

// ── Helpers ──

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

pub fn configure_git_identity(pool_dir: &Path, identity: &Identity) -> Result<()> {
    let name = if !identity.real_name.is_empty() {
        &identity.real_name
    } else if !identity.username.is_empty() {
        &identity.username
    } else {
        return Ok(());
    };

    Command::new("git")
        .args(["config", "user.name", name])
        .current_dir(pool_dir)
        .status()
        .context("Failed to set git user.name")?;

    if !identity.email.is_empty() {
        Command::new("git")
            .args(["config", "user.email", &identity.email])
            .current_dir(pool_dir)
            .status()
            .context("Failed to set git user.email")?;
    }

    Ok(())
}

// ── CLI entry points (thin wrappers) ──

pub async fn cmd_clone(dir: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    let pool_dir = if let Some(d) = dir {
        std::path::PathBuf::from(d)
    } else {
        cfg.pool_dir()?
    };

    if pool_dir.join(".git").exists() {
        println!("Already cloned at {}", pool_dir.display());
        println!("Use {} to update.", "pah pool pull".bold());
        return Ok(());
    }

    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let git_url = client.get_pool_url().await?;

    println!("Cloning pool from {} ...", git_url);
    clone_pool(&pool_dir, &git_url, &cfg.identity)?;
    println!("{} Pool cloned to {}", "Done.".green(), pool_dir.display());
    Ok(())
}

pub async fn cmd_pull() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;

    println!("Fetching latest changes...");
    pull_pool(&pool_dir)?;
    println!("{} Pool is up to date.", "Done.".green());
    Ok(())
}

pub async fn cmd_push() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;

    println!("Pushing to remote...");
    push_pool(&pool_dir)?;
    println!("{} Changes pushed.", "Done.".green());
    Ok(())
}

pub async fn cmd_status() -> Result<()> {
    let cfg = Config::load_or_default();
    let pool_dir = cfg.pool_dir()?;

    let output = status_pool(&pool_dir)?;
    print!("{}", output);
    Ok(())
}

// ── Tests ──

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    /// Create a bare git repo to act as a remote, returning its TempDir.
    fn create_bare_remote() -> TempDir {
        let dir = TempDir::new().unwrap();
        let status = Command::new("git")
            .args(["init", "--bare", "--initial-branch=main"])
            .current_dir(dir.path())
            .output()
            .unwrap();
        assert!(status.status.success(), "git init --bare failed");

        // Create an initial commit so origin/main exists.
        // We do this by cloning into a temp, committing, and pushing.
        let tmp_clone = TempDir::new().unwrap();
        for cmd_args in [
            vec![
                "clone",
                &dir.path().to_string_lossy(),
                &tmp_clone.path().to_string_lossy(),
            ],
            vec![
                "-C",
                &tmp_clone.path().to_string_lossy(),
                "config",
                "user.name",
                "test",
            ],
            vec![
                "-C",
                &tmp_clone.path().to_string_lossy(),
                "config",
                "user.email",
                "test@test.com",
            ],
            vec![
                "-C",
                &tmp_clone.path().to_string_lossy(),
                "commit",
                "--allow-empty",
                "-m",
                "init",
            ],
            vec![
                "-C",
                &tmp_clone.path().to_string_lossy(),
                "push",
                "origin",
                "HEAD",
            ],
        ] {
            let args: Vec<&str> = cmd_args.iter().map(|s| s.as_ref()).collect();
            let out = Command::new("git").args(&args).output().unwrap();
            assert!(
                out.status.success(),
                "setup cmd failed: git {:?}\n{}",
                args,
                String::from_utf8_lossy(&out.stderr)
            );
        }

        dir
    }

    #[test]
    fn test_clone_pool() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");

        let identity = Identity {
            real_name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            ..Default::default()
        };

        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();

        assert!(pool_dir.join(".git").exists());

        // Verify identity was configured
        let name_out = Command::new("git")
            .args(["config", "user.name"])
            .current_dir(&pool_dir)
            .output()
            .unwrap();
        assert_eq!(String::from_utf8_lossy(&name_out.stdout).trim(), "Alice");
        let email_out = Command::new("git")
            .args(["config", "user.email"])
            .current_dir(&pool_dir)
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&email_out.stdout).trim(),
            "alice@example.com"
        );
    }

    #[test]
    fn test_clone_pool_already_exists() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");
        let identity = Identity::default();

        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();
        // Second clone should be a no-op
        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();

        assert!(pool_dir.join(".git").exists());
    }

    #[test]
    fn test_pull_pool() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");
        let identity = Identity::default();

        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();

        // Add a new commit to the remote via a second clone
        let pusher = TempDir::new().unwrap();
        for cmd_args in [
            vec![
                "clone",
                &remote.path().to_string_lossy(),
                &pusher.path().to_string_lossy(),
            ],
            vec![
                "-C",
                &pusher.path().to_string_lossy(),
                "config",
                "user.name",
                "bot",
            ],
            vec![
                "-C",
                &pusher.path().to_string_lossy(),
                "config",
                "user.email",
                "bot@test.com",
            ],
        ] {
            let args: Vec<&str> = cmd_args.iter().map(|s| s.as_ref()).collect();
            Command::new("git").args(&args).output().unwrap();
        }
        fs::write(pusher.path().join("newfile.txt"), "hello").unwrap();
        for cmd_args in [
            vec!["-C", &pusher.path().to_string_lossy(), "add", "newfile.txt"],
            vec![
                "-C",
                &pusher.path().to_string_lossy(),
                "commit",
                "-m",
                "add file",
            ],
            vec![
                "-C",
                &pusher.path().to_string_lossy(),
                "push",
                "origin",
                "HEAD",
            ],
        ] {
            let args: Vec<&str> = cmd_args.iter().map(|s| s.as_ref()).collect();
            Command::new("git").args(&args).output().unwrap();
        }

        // Now pull should bring the new file
        pull_pool(&pool_dir).unwrap();
        assert!(pool_dir.join("newfile.txt").exists());
    }

    #[test]
    fn test_push_pool() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");
        let identity = Identity {
            username: "pusher".to_string(),
            email: "pusher@test.com".to_string(),
            ..Default::default()
        };

        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();

        // Make a local commit
        fs::write(pool_dir.join("local.txt"), "data").unwrap();
        for cmd_args in [
            vec!["add", "local.txt"],
            vec!["commit", "-m", "local commit"],
        ] {
            Command::new("git")
                .args(&cmd_args)
                .current_dir(&pool_dir)
                .output()
                .unwrap();
        }

        push_pool(&pool_dir).unwrap();

        // Verify the remote has the commit by cloning fresh
        let verify = TempDir::new().unwrap();
        Command::new("git")
            .args([
                "clone",
                &remote.path().to_string_lossy(),
                &verify.path().to_string_lossy(),
            ])
            .output()
            .unwrap();
        assert!(verify.path().join("local.txt").exists());
    }

    #[test]
    fn test_status_pool() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");
        let identity = Identity::default();

        clone_pool(&pool_dir, &remote.path().to_string_lossy(), &identity).unwrap();

        // Create an untracked file
        fs::write(pool_dir.join("untracked.txt"), "stuff").unwrap();

        let output = status_pool(&pool_dir).unwrap();
        assert!(
            output.contains("untracked.txt"),
            "status output should mention untracked file, got: {}",
            output
        );
    }

    #[test]
    fn test_pull_pool_no_repo() {
        let dir = TempDir::new().unwrap();
        let result = pull_pool(dir.path());
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("Pool not found"),
            "expected 'Pool not found' error, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_configure_git_identity() {
        let remote = create_bare_remote();
        let local = TempDir::new().unwrap();
        let pool_dir = local.path().join("pool");

        // Clone with empty identity first
        clone_pool(
            &pool_dir,
            &remote.path().to_string_lossy(),
            &Identity::default(),
        )
        .unwrap();

        // Now configure identity
        let identity = Identity {
            real_name: "Bob Builder".to_string(),
            email: "bob@example.com".to_string(),
            ..Default::default()
        };
        configure_git_identity(&pool_dir, &identity).unwrap();

        let name_out = Command::new("git")
            .args(["config", "user.name"])
            .current_dir(&pool_dir)
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&name_out.stdout).trim(),
            "Bob Builder"
        );
        let email_out = Command::new("git")
            .args(["config", "user.email"])
            .current_dir(&pool_dir)
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&email_out.stdout).trim(),
            "bob@example.com"
        );
    }
}
