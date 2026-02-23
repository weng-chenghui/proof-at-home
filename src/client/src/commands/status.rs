use anyhow::{bail, Result};
use colored::Colorize;
use std::path::Path;

use crate::config::Config;

pub fn run_status() -> Result<()> {
    if !Config::exists() {
        bail!("No config found. Run `proof-at-home init` first.");
    }

    let config = Config::load()?;

    println!("{}", "=== Proof@Home Status ===".bold().cyan());
    println!();

    println!("{}", "Identity".bold());
    println!("  Name:        {}", config.identity.real_name);
    println!("  Username:    {}", config.identity.username);
    println!("  Email:       {}", config.identity.email);
    if !config.identity.affiliation.is_empty() {
        println!("  Affiliation: {}", config.identity.affiliation);
    }
    println!();

    println!("{}", "API".bold());
    let key_display = if config.api.anthropic_api_key.len() > 8 {
        format!(
            "{}...{}",
            &config.api.anthropic_api_key[..8],
            &config.api.anthropic_api_key[config.api.anthropic_api_key.len() - 4..]
        )
    } else {
        "***".to_string()
    };
    println!("  API Key:     {}", key_display);
    println!("  Server:      {}", config.api.server_url);
    println!("  Model:       {}", config.api.model);
    println!();

    // Show cached environments
    println!("{}", "Cached Environments".bold());
    let envs_dir = Path::new(&config.prover.envs_dir);
    if envs_dir.exists() {
        let mut found_any = false;
        for prover in &["rocq", "lean"] {
            let prover_dir = envs_dir.join(prover);
            if !prover_dir.exists() {
                continue;
            }
            if let Ok(entries) = std::fs::read_dir(&prover_dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if !path.is_dir() {
                        continue;
                    }
                    let name = path.file_name().unwrap_or_default().to_string_lossy();
                    let ready = path.join(".ready").exists();
                    let status_icon = if ready {
                        "✓".green().to_string()
                    } else {
                        "…".yellow().to_string()
                    };

                    // Compute directory size (rough estimate)
                    let size = dir_size(&path).unwrap_or(0);
                    let size_str = human_size(size);

                    println!("  {} {}/{} ({})", status_icon, prover, name, size_str);
                    found_any = true;
                }
            }
        }
        if !found_any {
            println!(
                "  {}",
                "(none — environments are created on first prove)".dimmed()
            );
        }
    } else {
        println!(
            "  {}",
            "(none — environments are created on first prove)".dimmed()
        );
    }
    println!();

    println!("{}", "Budget".bold());
    let donated = config.budget.donated_usd;
    let spent = config.budget.total_spent;
    let remaining = (donated - spent).max(0.0);

    if donated > 0.0 {
        println!("  Donated:     {}", format!("${:.2}", donated).green());
    } else {
        println!(
            "  Donated:     {} (run `proof-at-home donate`)",
            "$0.00".yellow()
        );
    }
    println!("  Total Spent: ${:.2}", spent);
    println!("  Remaining:   ${:.2}", remaining);

    let config_path = Config::config_path()?;
    println!();
    println!("{}", "Config".dimmed());
    println!("  {}", config_path.display().to_string().dimmed());

    Ok(())
}

fn dir_size(path: &Path) -> Result<u64> {
    let mut total = 0u64;
    if path.is_file() {
        return Ok(path.metadata()?.len());
    }
    for entry in std::fs::read_dir(path)? {
        let entry = entry?;
        let p = entry.path();
        if p.is_dir() {
            total += dir_size(&p).unwrap_or(0);
        } else {
            total += p.metadata().map(|m| m.len()).unwrap_or(0);
        }
    }
    Ok(total)
}

fn human_size(bytes: u64) -> String {
    if bytes < 1024 {
        format!("{} B", bytes)
    } else if bytes < 1024 * 1024 {
        format!("{:.1} KB", bytes as f64 / 1024.0)
    } else if bytes < 1024 * 1024 * 1024 {
        format!("{:.1} MB", bytes as f64 / (1024.0 * 1024.0))
    } else {
        format!("{:.1} GB", bytes as f64 / (1024.0 * 1024.0 * 1024.0))
    }
}
