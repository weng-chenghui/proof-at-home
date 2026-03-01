use anyhow::{Context, Result};
use colored::Colorize;
use dialoguer::{Input, Password};

use crate::config::Config;
use crate::server_client::api::ServerClient;

pub async fn cmd_login() -> Result<()> {
    println!("{}", "=== Proof@Home Login ===".bold().cyan());
    println!();
    println!("{}", "To log in, follow these steps:".dimmed());
    println!(
        "{}",
        "  1. Open your account page in the web UI (sign up first if needed)".dimmed()
    );
    println!(
        "{}",
        "  2. Copy the CLI auth token from the account page".dimmed()
    );
    println!("{}", "  3. Paste it below".dimmed());
    println!();

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

    let token: String = Password::new().with_prompt("Auth token").interact()?;

    let token = token.trim().to_string();
    if token.is_empty() {
        anyhow::bail!("Token cannot be empty");
    }

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

    print!("  Verifying with server... ");
    let client = ServerClient::new(&server_url, &token);
    match client.health_check().await {
        Ok(true) => println!("{}", "OK".green()),
        Ok(false) => println!("{}", "server returned unhealthy status".yellow()),
        Err(e) => {
            println!("{}", "FAILED".red());
            println!("  {}", format!("Could not reach server: {e}").dimmed());
            println!("  {}", "Token saved anyway. Check that:".dimmed());
            println!(
                "  {}",
                "  - The server URL is correct (currently set to the value above)".dimmed()
            );
            println!(
                "  {}",
                "  - The server is running and accessible from your network".dimmed()
            );
        }
    }

    let mut config = Config::load_or_default();

    config.api.auth_token = token;
    config.api.server_url = server_url;

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
        "Run `pah setting set` to configure API key and other settings.".dimmed()
    );

    Ok(())
}

pub fn cmd_status() -> Result<()> {
    let cfg = Config::load_or_default();

    println!("{}", "=== Auth Status ===".bold());
    if cfg.identity.username.is_empty() {
        println!("Status:    {}", "not logged in".yellow());
        println!("\nRun `pah auth login` to authenticate.");
        return Ok(());
    }
    println!("Username:  {}", cfg.identity.username);
    println!("Email:     {}", cfg.identity.email);
    if !cfg.api.auth_token.is_empty() {
        println!("Token:     {}", "set".green());
    } else {
        println!("Token:     {}", "not set".yellow());
    }
    println!("Server:    {}", cfg.server_url());

    if !cfg.identity.public_key.is_empty() {
        println!("Public key: {}", cfg.identity.public_key.dimmed());
    }

    Ok(())
}

pub fn cmd_logout() -> Result<()> {
    let mut cfg = Config::load_or_default();
    cfg.api.auth_token = String::new();
    cfg.save()?;
    println!("{} Auth token cleared.", "✓".green().bold());
    Ok(())
}

// ── Helpers ──

fn prompt_server_url() -> Result<String> {
    let url: String = Input::new()
        .with_prompt("Server URL")
        .default("http://localhost:8080".to_string())
        .interact_text()?;
    Ok(url)
}

fn base64_decode_jwt(input: &str) -> Result<String> {
    let b64 = input.replace('-', "+").replace('_', "/");
    let padded = match b64.len() % 4 {
        2 => format!("{b64}=="),
        3 => format!("{b64}="),
        _ => b64,
    };
    let bytes = base64_decode_simple(&padded)?;
    String::from_utf8(bytes).context("JWT payload is not valid UTF-8")
}

fn base64_decode_simple(input: &str) -> Result<Vec<u8>> {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD
        .decode(input)
        .context("base64 decode failed")
}
