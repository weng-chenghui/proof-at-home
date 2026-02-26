use anyhow::Result;
use colored::Colorize;
use dialoguer::{Input, Password, Select};
use std::process::Command;

use crate::config::types::*;
use crate::config::Config;
use crate::signing;
use crate::strategy_store::importer;

pub fn run_setup(add_strategies: Vec<String>) -> Result<()> {
    // If --add-strategies is provided, import and return early
    if !add_strategies.is_empty() {
        println!("{}", "=== Import Strategy Files ===".bold().cyan());
        importer::import_strategies(&add_strategies)?;
        println!("\n{} Strategies imported successfully.", "✓".green().bold());
        return Ok(());
    }

    println!("{}", "=== Proof@Home CLI Setup ===".bold().cyan());
    println!();
    println!(
        "{}",
        "Register your account at the web UI (sign up page) first.".dimmed()
    );
    println!(
        "{}",
        "This command configures CLI-specific settings only.".dimmed()
    );
    println!();

    // Load existing config if available, to preserve identity
    let existing = Config::load().ok();

    // Identity — pull from existing config or ask minimally for attribution
    let identity = if let Some(ref cfg) = existing {
        println!(
            "Identity: {} <{}>",
            cfg.identity.username.green(),
            cfg.identity.email
        );
        println!(
            "{}",
            "(To update identity, edit ~/.proof-at-home/config.toml)".dimmed()
        );
        cfg.identity.clone()
    } else {
        println!(
            "{}",
            "No existing config found. Enter your username and email for proof attribution."
                .dimmed()
        );
        let username: String = Input::new()
            .with_prompt("Username (must match your web account)")
            .interact_text()?;
        let email: String = Input::new()
            .with_prompt("Email (must match your web account)")
            .interact_text()?;

        let (_, public_hex) = signing::generate_keypair();

        // Write signing key
        let key_path = Config::signing_key_path()?;
        let dir = Config::config_dir()?;
        std::fs::create_dir_all(&dir)?;
        std::fs::write(&key_path, &public_hex)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))?;
        }

        Identity {
            real_name: String::new(),
            username,
            email,
            affiliation: String::new(),
            public_key: public_hex,
        }
    };

    // API key
    println!();
    println!(
        "{}",
        "Get your API key at: https://console.anthropic.com → Settings → API Keys".dimmed()
    );
    let default_api_key = existing
        .as_ref()
        .map(|c| c.api.anthropic_api_key.clone())
        .unwrap_or_default();
    let api_key: String = if default_api_key.is_empty() {
        Password::new()
            .with_prompt("Anthropic API key")
            .interact()?
    } else {
        println!("  (Press Enter to keep existing API key)");
        let input: String = Password::new()
            .with_prompt("Anthropic API key")
            .allow_empty_password(true)
            .interact()?;
        if input.is_empty() {
            default_api_key
        } else {
            input
        }
    };

    let models = vec![
        "claude-sonnet-4-6",
        "claude-opus-4-6",
        "claude-haiku-4-5",
        "claude-3-5-sonnet-20241022",
    ];
    let current_model = existing
        .as_ref()
        .map(|c| c.api.model.as_str())
        .unwrap_or("claude-sonnet-4-6");
    let default_idx = models.iter().position(|m| *m == current_model).unwrap_or(0);
    let model_selection = Select::new()
        .with_prompt("Model")
        .items(&models)
        .default(default_idx)
        .interact()?;
    let model = models[model_selection].to_string();

    // Server
    let default_server = existing
        .as_ref()
        .map(|c| c.api.server_url.clone())
        .unwrap_or_else(|| "http://localhost:8080".to_string());
    let server_url: String = Input::new()
        .with_prompt("Server URL")
        .default(default_server)
        .interact_text()?;

    let default_auth = existing
        .as_ref()
        .map(|c| c.api.auth_token.clone())
        .unwrap_or_default();
    let auth_token: String = Input::new()
        .with_prompt("Server auth token (optional, press Enter to skip)")
        .default(default_auth)
        .allow_empty(true)
        .interact_text()?;

    // Check prover toolchains
    println!();
    println!("{}", "Checking prover toolchains...".bold());
    check_tool(
        "opam",
        &["--version"],
        "Install opam: https://opam.ocaml.org/doc/Install.html",
        "Rocq conjectures will not work without opam.",
    );
    check_tool(
        "elan",
        &["--version"],
        "Install elan: https://github.com/leanprover/elan#installation",
        "Lean conjectures will not work without elan.",
    );
    check_tool(
        "lake",
        &["--version"],
        "",
        "lake is usually installed with elan.",
    );
    check_tool("claude", &["--version"], "", "Will use API fallback.");

    let config = Config {
        identity,
        api: Api {
            anthropic_api_key: api_key,
            server_url,
            model,
            auth_token,
        },
        prover: existing
            .as_ref()
            .map(|c| c.prover.clone())
            .unwrap_or(Prover {
                scratch_dir: "/tmp/proof-at-home".to_string(),
                envs_dir: default_envs_dir(),
            }),
        budget: existing
            .as_ref()
            .map(|c| c.budget.clone())
            .unwrap_or_default(),
        ipfs: existing
            .as_ref()
            .map(|c| c.ipfs.clone())
            .unwrap_or_default(),
    };

    config.save()?;

    let path = Config::config_path()?;
    println!();
    println!("{} Config saved to {}", "✓".green().bold(), path.display());
    println!(
        "Run {} to set your donation budget.",
        "proof-at-home donate".cyan()
    );

    Ok(())
}

fn check_tool(name: &str, args: &[&str], install_hint: &str, note: &str) {
    print!("  {}... ", name);
    match Command::new(name).args(args).output() {
        Ok(output) if output.status.success() => {
            let version = String::from_utf8_lossy(&output.stdout);
            println!("{} ({})", "OK".green(), version.trim());
        }
        _ => {
            println!("{}", "NOT FOUND".yellow());
            if !install_hint.is_empty() {
                println!("    {}", install_hint.dimmed());
            }
            if !note.is_empty() {
                println!("    {}", note.dimmed());
            }
        }
    }
}

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| std::path::PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
}
