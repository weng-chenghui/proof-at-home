use anyhow::{bail, Result};
use colored::Colorize;
use dialoguer::{Confirm, Input, Password, Select};
use std::path::Path;

use crate::config::types::*;
use crate::config::Config;
use crate::signing;
use crate::tools::registry;

/// `pah setting get [<key>]` — no key: show full status; with key: show single value
pub fn cmd_get(key: Option<&str>) -> Result<()> {
    match key {
        None => run_status(),
        Some(k) => {
            let cfg = Config::load_or_default();
            let value = match k {
                "username" => cfg.identity.username.clone(),
                "email" => cfg.identity.email.clone(),
                "real_name" => cfg.identity.real_name.clone(),
                "affiliation" => cfg.identity.affiliation.clone(),
                "public_key" => cfg.identity.public_key.clone(),
                "api_key" | "anthropic_api_key" => {
                    if cfg.api.anthropic_api_key.len() > 8 {
                        format!(
                            "{}...{}",
                            &cfg.api.anthropic_api_key[..8],
                            &cfg.api.anthropic_api_key[cfg.api.anthropic_api_key.len() - 4..]
                        )
                    } else {
                        "***".to_string()
                    }
                }
                "server_url" => cfg.api.server_url.clone(),
                "model" => cfg.api.model.clone(),
                "auth_token" => {
                    if cfg.api.auth_token.is_empty() {
                        "(not set)".to_string()
                    } else {
                        format!(
                            "{}…",
                            &cfg.api.auth_token[..20.min(cfg.api.auth_token.len())]
                        )
                    }
                }
                "scratch_dir" => cfg.prover.scratch_dir.clone(),
                "envs_dir" => cfg.prover.envs_dir.clone(),
                "donated_usd" | "budget" => format!("${:.2}", cfg.budget.donated_usd),
                "total_spent" => format!("${:.2}", cfg.budget.total_spent),
                _ => bail!("Unknown setting key: {}", k),
            };
            println!("{}", value);
            Ok(())
        }
    }
}

/// `pah setting set [<key> <value>]` — no args: interactive wizard; with args: set single value
pub fn cmd_set(key: Option<&str>, value: Option<&str>) -> Result<()> {
    match (key, value) {
        (None, None) => run_setup_wizard(),
        (Some("budget"), _) => run_donate(),
        (Some(k), Some(v)) => {
            let mut cfg = Config::load_or_default();
            match k {
                "username" => cfg.identity.username = v.to_string(),
                "email" => cfg.identity.email = v.to_string(),
                "real_name" => cfg.identity.real_name = v.to_string(),
                "affiliation" => cfg.identity.affiliation = v.to_string(),
                "server_url" => cfg.api.server_url = v.to_string(),
                "model" => cfg.api.model = v.to_string(),
                "api_key" | "anthropic_api_key" => cfg.api.anthropic_api_key = v.to_string(),
                "scratch_dir" => cfg.prover.scratch_dir = v.to_string(),
                "envs_dir" => cfg.prover.envs_dir = v.to_string(),
                _ => bail!("Unknown or read-only setting key: {}", k),
            }
            cfg.save()?;
            println!("{} {} = {}", "✓".green(), k, v);
            Ok(())
        }
        (Some(k), None) => bail!(
            "Missing value for key '{}'. Usage: pah setting set <key> <value>",
            k
        ),
        (None, Some(_)) => bail!("Missing key. Usage: pah setting set <key> <value>"),
    }
}

// ── status (merged from status.rs) ──

fn run_status() -> Result<()> {
    let config = Config::load_or_default();

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
    println!("  Server:      {}", config.server_url());
    println!("  Model:       {}", config.api.model);
    println!();

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
        println!("  Budget:      {}", format!("${:.2}", donated).green());
    } else {
        println!(
            "  Budget:      {} (run `pah setting set budget`)",
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

// ── setup wizard (merged from setup.rs) ──

fn run_setup_wizard() -> Result<()> {
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

    let existing = Config::load().ok();

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

    println!();
    println!("{}", "Checking prover toolchains...".bold());
    for name in &["opam", "elan", "lake", "claude"] {
        if let Some(spec) = registry::get_spec(name) {
            print!("  {}... ", name);
            match registry::detect_tool(spec) {
                Some(info) => {
                    println!("{} ({})", "OK".green(), info.version);
                }
                None => {
                    println!("{}", "NOT FOUND".yellow());
                    if !spec.install_hint.is_empty() {
                        println!("    {}", spec.install_hint.dimmed());
                    }
                }
            }
        }
    }

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
        "pah setting set budget".cyan()
    );

    Ok(())
}

// ── donate (merged from donate.rs) ──

const LEGAL_TEXT: &str = r#"
=== Proof@Home Budget Agreement ===

By proceeding, you acknowledge and agree to the following:

1. YOUR API CREDITS: You are allocating a portion of your own Anthropic
   API credits toward automated mathematical theorem proving. This is
   not a donation to a third party — it spends your own API budget.

2. NON-REFUNDABLE: API credits consumed during proof sessions cannot be
   recovered. You are responsible for monitoring your own Anthropic billing.

3. PUBLIC DOMAIN: All proofs generated through Proof@Home are released
   into the public domain (CC0). You waive all intellectual property
   claims over the generated proof scripts.

4. NO WARRANTY: Proofs are generated by AI and mechanically verified.
   While the formal verification provides mathematical certainty, the
   Proof@Home project makes no warranty about fitness for any purpose.

5. ATTRIBUTION: Your username will be permanently associated with the
   proofs you help generate, recorded in NFT-compatible metadata.
"#;

fn run_donate() -> Result<()> {
    let mut config = Config::load_or_default();

    println!("{}", LEGAL_TEXT.dimmed());

    let accepted = Confirm::new()
        .with_prompt("Do you accept the above agreement?")
        .default(false)
        .interact()?;

    if !accepted {
        println!("Donation cancelled.");
        return Ok(());
    }

    println!();
    println!("{}", "Typical costs per proof:".dimmed());
    println!(
        "{}",
        "  Haiku:  ~$0.05   Sonnet: ~$0.50   Opus: ~$2.00".dimmed()
    );
    println!();

    let amounts = vec![
        "$1.00  (~20 proofs with Haiku)",
        "$2.00  (~40 proofs with Haiku)",
        "$5.00  (~100 proofs with Haiku)",
        "$10.00 (~200 proofs with Haiku)",
        "Custom amount",
    ];
    let selection = Select::new()
        .with_prompt("How much API budget to allocate for this run?")
        .items(&amounts)
        .default(1)
        .interact()?;

    let amount: f64 = match selection {
        0 => 1.0,
        1 => 2.0,
        2 => 5.0,
        3 => 10.0,
        _ => {
            let custom: String = Input::new()
                .with_prompt("Enter amount in USD (e.g. 3.50)")
                .interact_text()?;
            custom
                .trim_start_matches('$')
                .parse::<f64>()
                .map_err(|_| anyhow::anyhow!("Invalid amount"))?
        }
    };

    if amount <= 0.0 {
        bail!("Budget amount must be positive.");
    }

    config.budget.donated_usd = amount;
    config.save()?;

    println!();
    println!(
        "{} Budget set to {}",
        "✓".green().bold(),
        format!("${:.2}", amount).cyan().bold()
    );
    println!(
        "Run {} to start proving theorems!",
        "pah contribution run".cyan()
    );

    Ok(())
}

// ── Helpers ──

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| std::path::PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
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
