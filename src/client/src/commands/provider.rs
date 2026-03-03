use anyhow::Result;
use colored::Colorize;

use crate::ai;
use crate::config::Config;

/// `pah provider list` — list all supported AI providers.
pub fn cmd_list() -> Result<()> {
    println!("{}", "Supported AI providers:".bold());
    println!();
    for (name, description) in ai::PROVIDERS {
        println!("  {:<12} {}", name.cyan(), description);
    }
    println!();
    println!(
        "Switch providers with: {}",
        "pah setting set provider <name>".dimmed()
    );
    Ok(())
}

/// `pah provider get` — show the current provider configuration.
pub fn cmd_get() -> Result<()> {
    let config = Config::load_or_default();
    let provider = config.provider();
    let model = config.model();
    let base_url = config.api_base_url();

    println!("{}", "Current AI provider:".bold());
    println!("  Provider:  {}", provider.cyan());
    println!("  Model:     {}", model);
    if !base_url.is_empty() {
        println!("  Base URL:  {}", base_url);
    }

    let api_key = config.api_key();
    if !api_key.is_empty() {
        let masked = if api_key.len() > 8 {
            format!("{}...{}", &api_key[..8], &api_key[api_key.len() - 4..])
        } else {
            "***".to_string()
        };
        println!("  API Key:   {}", masked);
    } else {
        println!("  API Key:   {}", "(not set)".yellow());
    }

    Ok(())
}

/// `pah provider quota` — query remaining credits/requests from the provider.
pub async fn cmd_quota() -> Result<()> {
    let config = Config::load_or_default();
    let provider = ai::create_provider(&config)?;

    println!("Querying quota for {} provider...", provider.name().cyan());

    let quota = provider.query_quota().await?;

    println!();
    println!("{}", "Quota Info:".bold());
    println!("  {}", quota.description);
    if let Some(remaining) = quota.remaining_usd {
        println!("  Remaining credits: ${:.2}", remaining);
    }
    if let Some(requests) = quota.remaining_requests {
        println!("  Remaining requests: {}", requests);
    }
    if let Some(spend) = quota.monthly_spend_usd {
        println!("  Monthly spend: ${:.2}", spend);
    }

    Ok(())
}
