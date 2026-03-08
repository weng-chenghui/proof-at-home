use anyhow::Result;
use colored::Colorize;

use crate::agent::memory;
use crate::config::Config;
use crate::server_client::api::ServerClient;
use crate::strategy_store::importer;

pub async fn cmd_list(kind: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let strategies = client.fetch_strategies().await?;

    let filtered: Vec<_> = strategies
        .into_iter()
        .filter(|s| kind.is_none_or(|k| s.kind == k))
        .collect();

    if filtered.is_empty() {
        println!("No strategies found.");
        return Ok(());
    }

    println!(
        "{:<30} {:<12} {:<12} {:<8} Description",
        "Name", "Kind", "Prover", "Priority"
    );
    println!("{}", "-".repeat(90));

    for s in &filtered {
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

    println!("\nTotal: {}", filtered.len());
    Ok(())
}

pub async fn cmd_get(name: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
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

pub fn cmd_memory_list(kind: Option<&str>, agent: Option<&str>) -> Result<()> {
    let memories = memory::list_memories(kind, agent)?;

    if memories.is_empty() {
        println!("No memories found.");
        return Ok(());
    }

    println!("{:<30} {:<20} {:<50}", "Name", "Kind", "Description");
    println!("{}", "-".repeat(100));

    for m in &memories {
        let desc = if m.meta.description.len() > 48 {
            format!("{}...", &m.meta.description[..45])
        } else {
            m.meta.description.clone()
        };
        println!("{:<30} {:<20} {:<50}", m.meta.name, m.meta.kind, desc);
    }

    println!("\nTotal: {}", memories.len());
    Ok(())
}

pub fn cmd_memory_get(name: &str) -> Result<()> {
    let mem = memory::get_memory(name)?;

    println!("{}", "=== Memory ===".bold());
    println!("Name:        {}", mem.meta.name);
    println!("Kind:        {}", mem.meta.kind);
    println!("Description: {}", mem.meta.description);
    println!("Priority:    {}", mem.meta.priority);

    for (k, v) in &mem.meta.extra {
        println!("{:<12} {}", format!("{}:", k), v);
    }

    println!();
    println!("{}", "\u{2500}".repeat(60).dimmed());
    println!("{}", mem.body);

    Ok(())
}

pub fn cmd_memory_create(kind: &str, body: &str, tags: Option<&str>) -> Result<()> {
    let tag_list: Vec<String> = tags
        .map(|t| t.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let name = format!("mem-{}", &uuid::Uuid::new_v4().to_string()[..8]);

    let path = memory::create_memory(&name, kind, body, &tag_list, "")?;
    println!("{} Memory created: {}", "✓".green(), name);
    println!("  Path: {}", path.display());
    Ok(())
}

pub fn cmd_memory_forget(name: &str) -> Result<()> {
    memory::forget_memory(name)?;
    println!("{} Memory '{}' deleted.", "✓".green(), name);
    Ok(())
}
