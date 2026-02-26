use anyhow::Result;
use colored::Colorize;

use crate::config::Config;
use crate::server_client::api::ServerClient;
use crate::strategy_store::importer;

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load()?;
    let client = ServerClient::new(&cfg.api.server_url, &cfg.api.auth_token);
    let strategies = client.fetch_strategies().await?;

    if strategies.is_empty() {
        println!("No strategies found.");
        return Ok(());
    }

    println!(
        "{:<30} {:<12} {:<12} {:<8} Description",
        "Name", "Kind", "Prover", "Priority"
    );
    println!("{}", "-".repeat(90));

    for s in &strategies {
        let desc = if s.description.len() > 30 {
            format!("{}…", &s.description[..29])
        } else {
            s.description.clone()
        };
        println!(
            "{:<30} {:<12} {:<12} {:<8} {}",
            s.name, s.kind, s.prover, s.priority, desc
        );
    }

    println!("\nTotal: {}", strategies.len());
    Ok(())
}

pub async fn cmd_get(name: &str) -> Result<()> {
    let cfg = Config::load()?;
    let client = ServerClient::new(&cfg.api.server_url, &cfg.api.auth_token);
    let s = client.fetch_strategy(name).await?;

    println!("{}", "=== Strategy ===".bold());
    println!("Name:        {}", s.name);
    println!("Kind:        {}", s.kind);
    println!("Prover:      {}", s.prover);
    println!("Priority:    {}", s.priority);
    println!("Description: {}", s.description);
    if !s.body.is_empty() {
        println!("\nBody:\n{}", s.body);
    }

    Ok(())
}

pub fn cmd_import(paths: &[String]) -> Result<()> {
    println!("{}", "=== Import Strategy Files ===".bold().cyan());
    importer::import_strategies(paths)?;
    println!("\n{} Strategies imported successfully.", "✓".green().bold());
    Ok(())
}
