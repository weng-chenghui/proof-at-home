use anyhow::{Context, Result};
use colored::Colorize;
use dialoguer::{Input, Password};

use crate::config::types::*;
use crate::config::Config;
use crate::server_client::api::ServerClient;

pub async fn run_login() -> Result<()> {
    println!("{}", "=== Proof@Home Login ===".bold().cyan());
    println!();
    println!(
        "{}",
        "Paste your auth token from the web UI (Login page → Settings).".dimmed()
    );
    println!();

    // Determine server URL: env var > existing config > prompt
    let server_url = if let Ok(url) = std::env::var("PAH_SERVER_URL") {
        println!("Server: {} (from PAH_SERVER_URL)", url.green());
        url
    } else if let Ok(cfg) = Config::load() {
        if !cfg.api.server_url.is_empty() {
            println!("Server: {} (from config)", cfg.api.server_url.green());
            cfg.api.server_url.clone()
        } else {
            prompt_server_url()?
        }
    } else {
        prompt_server_url()?
    };

    // Prompt for token
    let token: String = Password::new().with_prompt("Auth token").interact()?;

    let token = token.trim().to_string();
    if token.is_empty() {
        anyhow::bail!("Token cannot be empty");
    }

    // Decode JWT to extract identity
    let parts: Vec<&str> = token.split('.').collect();
    if parts.len() != 3 {
        anyhow::bail!("Invalid token format (expected JWT with 3 parts)");
    }

    let payload_json = base64_decode_jwt(parts[1]).context("Failed to decode token payload")?;
    let payload: serde_json::Value =
        serde_json::from_str(&payload_json).context("Failed to parse token payload as JSON")?;

    let username = payload
        .get("username")
        .or_else(|| payload.get("nickname"))
        .or_else(|| payload.get("email"))
        .or_else(|| payload.get("sub"))
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();

    let email = payload
        .get("email")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();

    if !username.is_empty() {
        println!("  Logged in as: {}", username.green().bold());
    }
    if !email.is_empty() && email != username {
        println!("  Email: {}", email);
    }

    // Verify token against server
    print!("  Verifying with server... ");
    let client = ServerClient::new(&server_url, &token);
    match client.health_check().await {
        Ok(true) => println!("{}", "OK".green()),
        Ok(false) => println!("{}", "server returned unhealthy status".yellow()),
        Err(e) => {
            println!("{}", "FAILED".red());
            println!("  {}", format!("Could not reach server: {e}").dimmed());
            println!(
                "  {}",
                "Token saved anyway — verify your server URL is correct.".dimmed()
            );
        }
    }

    // Load or create config
    let mut config = Config::load().unwrap_or_else(|_| Config {
        identity: Identity {
            real_name: String::new(),
            username: String::new(),
            email: String::new(),
            affiliation: String::new(),
            public_key: String::new(),
        },
        api: Api {
            anthropic_api_key: String::new(),
            server_url: String::new(),
            model: "claude-sonnet-4-6".to_string(),
            auth_token: String::new(),
        },
        prover: Prover {
            scratch_dir: "/tmp/proof-at-home".to_string(),
            envs_dir: default_envs_dir(),
        },
        budget: Budget::default(),
        ipfs: Default::default(),
    });

    // Update auth token and server URL
    config.api.auth_token = token;
    config.api.server_url = server_url;

    // Fill identity from JWT if not already set
    if config.identity.username.is_empty() && !username.is_empty() {
        config.identity.username = username;
    }
    if config.identity.email.is_empty() && !email.is_empty() {
        config.identity.email = email;
    }

    config.save()?;

    println!();
    println!("{} Token saved to config.", "✓".green().bold());
    println!(
        "{}",
        "Run `proof-at-home setup` to configure API key and other settings.".dimmed()
    );

    Ok(())
}

fn prompt_server_url() -> Result<String> {
    let url: String = Input::new()
        .with_prompt("Server URL")
        .default("http://localhost:8080".to_string())
        .interact_text()?;
    Ok(url)
}

/// Decode a JWT base64url segment (no padding).
fn base64_decode_jwt(input: &str) -> Result<String> {
    // JWT uses base64url encoding (- instead of +, _ instead of /)
    let b64 = input.replace('-', "+").replace('_', "/");
    // Add padding
    let padded = match b64.len() % 4 {
        2 => format!("{b64}=="),
        3 => format!("{b64}="),
        _ => b64,
    };
    let bytes = base64_decode_simple(&padded)?;
    String::from_utf8(bytes).context("JWT payload is not valid UTF-8")
}

/// Simple base64 decoder (standard alphabet).
fn base64_decode_simple(input: &str) -> Result<Vec<u8>> {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD
        .decode(input)
        .context("base64 decode failed")
}

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| std::path::PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
}
