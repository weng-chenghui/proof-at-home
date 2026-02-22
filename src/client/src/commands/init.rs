use anyhow::Result;
use colored::Colorize;
use dialoguer::{Input, Password, Select};
use std::process::Command;

use crate::config::types::*;
use crate::config::Config;
use crate::signing;

pub fn run_init() -> Result<()> {
    println!("{}", "=== Proof@Home Setup Wizard ===".bold().cyan());
    println!();

    // Identity
    let real_name: String = Input::new().with_prompt("Your real name").interact_text()?;

    let username: String = Input::new()
        .with_prompt("Username (for attribution)")
        .interact_text()?;

    let email: String = Input::new().with_prompt("Email").interact_text()?;

    let affiliation: String = Input::new()
        .with_prompt("Affiliation (optional, press Enter to skip)")
        .default(String::new())
        .interact_text()?;

    // API key
    println!();
    println!(
        "{}",
        "Get your API key at: https://console.anthropic.com → Settings → API Keys".dimmed()
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

    let auth_token: String = Input::new()
        .with_prompt("Server auth token (optional, press Enter to skip)")
        .default(String::new())
        .allow_empty(true)
        .interact_text()?;

    // Check proof assistant toolchains
    println!();
    println!("{}", "Checking proof assistant toolchains...".bold());

    // Check opam (for Rocq)
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
                "Rocq problems will not work without opam.".dimmed()
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
            println!("    {}", "lake is usually installed with elan.".dimmed());
        }
    }

    // Check claude CLI
    print!("  claude CLI... ");
    match Command::new("claude").arg("--version").output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => println!("{} (will use API fallback)", "NOT FOUND".yellow()),
    }

    // Generate ed25519 keypair
    let (private_hex, public_hex) = signing::generate_keypair();

    let config = Config {
        identity: Identity {
            real_name,
            username,
            email,
            affiliation,
            public_key: public_hex.clone(),
        },
        api: Api {
            anthropic_api_key: api_key,
            server_url,
            model,
            auth_token,
        },
        proof_assistant: ProofAssistant {
            scratch_dir: "/tmp/proof-at-home".to_string(),
            envs_dir: default_envs_dir(),
        },
        budget: Budget::default(),
        ipfs: Default::default(),
    };

    config.save()?;

    // Write signing key with restricted permissions
    let key_path = Config::signing_key_path()?;
    std::fs::write(&key_path, &private_hex)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))?;
    }

    let path = Config::config_path()?;
    println!();
    println!("{} Config saved to {}", "✓".green().bold(), path.display());
    println!(
        "{} Ed25519 public key: {}",
        "✓".green().bold(),
        public_hex.dimmed()
    );
    println!(
        "{}",
        "Proof environments will be auto-created when you run problems.".dimmed()
    );
    println!(
        "Run {} to set your donation budget.",
        "proof-at-home donate".cyan()
    );

    Ok(())
}

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| std::path::PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
}
