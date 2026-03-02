use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::process::Command;

use crate::tools::cache;
use crate::tools::registry::{self, ToolStatus};

/// `pah tools check` — scan all tools and print status.
pub fn cmd_check() -> Result<()> {
    println!("{}", "=== Proof@Home Tool Check ===".bold().cyan());
    println!();

    let results = registry::check_all_tools();
    let mut found = 0;
    let mut missing = 0;

    for status in &results {
        match status {
            ToolStatus::Found(info) => {
                println!(
                    "  {} {:<20} {} ({})",
                    "✓".green(),
                    info.name,
                    info.version.dimmed(),
                    info.path.display().to_string().dimmed()
                );
                found += 1;
            }
            ToolStatus::NotFound {
                name,
                install_hint,
                required_by,
            } => {
                println!("  {} {:<20} {}", "✗".red(), name, "NOT FOUND".yellow());
                println!("    {}: {}", "Needed for".dimmed(), required_by.dimmed());
                println!("    {}", install_hint.dimmed());
                missing += 1;
            }
        }
    }

    println!();
    println!(
        "  {} found, {} missing",
        found.to_string().green(),
        if missing > 0 {
            missing.to_string().yellow().to_string()
        } else {
            missing.to_string().green().to_string()
        }
    );

    Ok(())
}

/// `pah tools list` — tabular listing of all tools.
pub fn cmd_list() -> Result<()> {
    println!(
        "{:<20} {:<12} {:<12} {:<30} Required by",
        "Tool", "Status", "Version", "Path"
    );
    println!("{}", "-".repeat(95));

    let results = registry::check_all_tools();
    for status in &results {
        match status {
            ToolStatus::Found(info) => {
                let path_str = info.path.display().to_string();
                let short_path = if path_str.len() > 28 {
                    format!("...{}", &path_str[path_str.len() - 25..])
                } else {
                    path_str
                };
                let spec = registry::get_spec(&info.name);
                let required_by = spec.map(|s| s.required_by).unwrap_or("");
                println!(
                    "{:<20} {:<12} {:<12} {:<30} {}",
                    info.name,
                    "OK".green(),
                    info.version,
                    short_path,
                    required_by
                );
            }
            ToolStatus::NotFound {
                name, required_by, ..
            } => {
                println!(
                    "{:<20} {:<12} {:<12} {:<30} {}",
                    name,
                    "MISSING".yellow(),
                    "-",
                    "-",
                    required_by
                );
            }
        }
    }

    Ok(())
}

/// `pah tools install <name>` — install a tool if possible.
pub fn cmd_install(name: &str) -> Result<()> {
    let spec = registry::get_spec(name).with_context(|| {
        format!(
            "Unknown tool: '{}'. Run 'pah tools list' to see available tools.",
            name
        )
    })?;

    // Check if already installed
    if let Some(info) = registry::detect_tool(spec) {
        println!(
            "{} {} is already installed ({})",
            "✓".green(),
            name,
            info.version
        );
        return Ok(());
    }

    match spec.install_command {
        Some(install_cmd) => {
            println!("Installing {}...", name);
            println!("  Running: {}", install_cmd.dimmed());

            let status = Command::new("sh")
                .args(["-c", install_cmd])
                .status()
                .context("Failed to run install command")?;

            if !status.success() {
                bail!(
                    "Installation command failed with exit code {:?}",
                    status.code()
                );
            }

            // Verify installation
            if let Some(info) = registry::detect_tool(spec) {
                let _ = cache::save_cached_tool(&info);
                println!(
                    "{} {} installed successfully ({})",
                    "✓".green(),
                    name,
                    info.version
                );
            } else {
                println!(
                    "{} Installation completed but '{}' was not found in PATH.",
                    "!".yellow(),
                    name
                );
                println!("  You may need to restart your shell or update your PATH.");
            }
        }
        None => {
            println!(
                "{} No automatic installer available for '{}'.",
                "ℹ".blue(),
                name
            );
            println!("  {}", spec.install_hint);
        }
    }

    Ok(())
}
