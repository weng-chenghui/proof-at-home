use anyhow::Result;
use colored::Colorize;
use dialoguer::{Input, Password, Select};
use std::process::Command;

use crate::config::types::*;
use crate::config::Config;

pub fn run_init() -> Result<()> {
    println!("{}", "=== Proof@Home Setup Wizard ===".bold().cyan());
    println!();

    // Identity
    let real_name: String = Input::new()
        .with_prompt("Your real name")
        .interact_text()?;

    let username: String = Input::new()
        .with_prompt("Username (for attribution)")
        .interact_text()?;

    let email: String = Input::new()
        .with_prompt("Email")
        .interact_text()?;

    let affiliation: String = Input::new()
        .with_prompt("Affiliation (optional, press Enter to skip)")
        .default(String::new())
        .interact_text()?;

    // API key
    println!();
    println!(
        "{}",
        "Get your API key at: https://console.anthropic.com → Settings → API Keys"
            .dimmed()
    );
    let api_key: String = Password::new()
        .with_prompt("Anthropic API key")
        .interact()?;

    let models = vec![
        "claude-sonnet-4-6",
        "claude-opus-4-6",
        "claude-haiku-4-5",
        "claude-3-5-sonnet-20241022",
    ];
    let model_selection = Select::new()
        .with_prompt("Model")
        .items(&models)
        .default(0)
        .interact()?;
    let model = models[model_selection].to_string();

    // Server
    let server_url: String = Input::new()
        .with_prompt("Server URL")
        .default("http://localhost:8080".to_string())
        .interact_text()?;

    // Check proof assistant toolchains
    println!();
    println!("{}", "Checking proof assistant toolchains...".bold());

    // Check opam (for Coq)
    print!("  opam... ");
    match Command::new("opam").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => {
            println!("{}", "NOT FOUND".yellow());
            println!(
                "    {}",
                "Install opam: https://opam.ocaml.org/doc/Install.html".dimmed()
            );
            println!(
                "    {}",
                "Coq problems will not work without opam.".dimmed()
            );
        }
    }

    // Check elan (for Lean)
    print!("  elan... ");
    match Command::new("elan").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => {
            println!("{}", "NOT FOUND".yellow());
            println!(
                "    {}",
                "Install elan: https://github.com/leanprover/elan#installation".dimmed()
            );
            println!(
                "    {}",
                "Lean problems will not work without elan.".dimmed()
            );
        }
    }

    // Check lake (for Lean)
    print!("  lake... ");
    match Command::new("lake").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => {
            println!("{}", "NOT FOUND".yellow());
            println!(
                "    {}",
                "lake is usually installed with elan.".dimmed()
            );
        }
    }

    // Check claude CLI
    print!("  claude CLI... ");
    match Command::new("claude").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => println!(
            "{} (will use API fallback)",
            "NOT FOUND".yellow()
        ),
    }

    let config = Config {
        identity: Identity {
            real_name,
            username,
            email,
            affiliation,
        },
        api: Api {
            anthropic_api_key: api_key,
            server_url,
            model,
        },
        proof_assistant: ProofAssistant {
            scratch_dir: "/tmp/proof-at-home".to_string(),
            envs_dir: default_envs_dir(),
        },
        budget: Budget::default(),
    };

    config.save()?;
    let path = Config::config_path()?;
    println!();
    println!(
        "{} Config saved to {}",
        "✓".green().bold(),
        path.display()
    );
    println!(
        "{}",
        "Proof environments will be auto-created when you run problems.".dimmed()
    );
    println!("Run {} to set your donation budget.", "proof-at-home donate".cyan());

    Ok(())
}

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| std::path::PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
}
