use anyhow::Result;
use colored::Colorize;

use crate::agent::memory;
use crate::config::Config;
use crate::server_client::api::ServerClient;
use crate::strategy_store::frontmatter;
use crate::strategy_store::importer;
use crate::strategy_store::registry;

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

// ── Search ──

pub async fn cmd_search(query: &str, kind: Option<&str>, prover: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    let registries_cfg = &cfg.registries;

    if registries_cfg.is_empty() {
        println!("No registries configured. Add one with: pah strategy registry add <name> <url>");
        return Ok(());
    }

    let mut total = 0;
    for reg_cfg in registries_cfg {
        match registry::fetch_registry(&reg_cfg.url).await {
            Ok(reg) => {
                let results = registry::search_registry(&reg, query, kind, prover);
                if results.is_empty() {
                    continue;
                }

                println!("\n{} ({})", reg_cfg.name.bold(), reg.description);
                println!(
                    "{:<30} {:<12} {:<10} {:<12} Description",
                    "Name", "Kind", "Prover", "Author"
                );
                println!("{}", "-".repeat(90));

                for entry in &results {
                    let desc = if entry.description.len() > 25 {
                        format!("{}…", &entry.description[..24])
                    } else {
                        entry.description.clone()
                    };
                    println!(
                        "{:<30} {:<12} {:<10} {:<12} {}",
                        entry.name, entry.kind, entry.prover, entry.author, desc
                    );
                }
                total += results.len();
            }
            Err(e) => {
                eprintln!(
                    "  {}: Could not fetch registry '{}': {}",
                    "Warning".yellow(),
                    reg_cfg.name,
                    e
                );
            }
        }
    }

    if total == 0 {
        println!("No results found for '{}'.", query);
    } else {
        println!(
            "\n{} result(s). Import with: pah strategy import <source>",
            total
        );
    }

    Ok(())
}

// ── Publish ──

pub fn cmd_publish(name: &str, _registry: &str) -> Result<()> {
    // Load the local strategy file and validate it
    let strategies_dir = crate::strategy_store::loader::strategies_dir()?;
    let path = strategies_dir.join(format!("{}.md", name));

    if !path.exists() {
        anyhow::bail!(
            "Strategy '{}' not found in {}. Import it first.",
            name,
            strategies_dir.display()
        );
    }

    let content = std::fs::read_to_string(&path)?;
    let (meta, _) = frontmatter::parse_strategy_file(&content)?;
    frontmatter::validate_for_publish(&meta)?;

    // Generate registry entry JSON
    let entry = serde_json::json!({
        "name": meta.name,
        "version": meta.version,
        "author": meta.author,
        "description": meta.description,
        "kind": meta.kind,
        "prover": meta.prover,
        "source": meta.source.unwrap_or_default(),
        "tags": [],
        "updated_at": chrono::Utc::now().to_rfc3339(),
    });

    println!("{}", "=== Strategy Registry Entry ===".bold().cyan());
    println!("{}", serde_json::to_string_pretty(&entry)?);
    println!();
    println!("To publish, add this entry to the registry's JSON file and open a PR.");
    println!("If you have the {} CLI, run:", "gh".bold());
    println!("  gh pr create --title \"Add strategy: {}\"", meta.name);

    Ok(())
}

// ── Registry management ──

pub fn cmd_registry_list() -> Result<()> {
    let cfg = Config::load_or_default();

    if cfg.registries.is_empty() {
        println!("No registries configured.");
        println!("Add one with: pah strategy registry add <name> <url>");
        return Ok(());
    }

    println!("{:<20} URL", "Name");
    println!("{}", "-".repeat(60));
    for reg in &cfg.registries {
        println!("{:<20} {}", reg.name, reg.url);
    }

    Ok(())
}

pub fn cmd_registry_add(name: &str, url: &str) -> Result<()> {
    let mut cfg = Config::load_or_default();

    // Check for duplicates
    if cfg.registries.iter().any(|r| r.name == name) {
        anyhow::bail!("Registry '{}' already exists. Remove it first.", name);
    }

    cfg.registries.push(crate::config::types::RegistryConfig {
        name: name.to_string(),
        url: url.to_string(),
    });
    cfg.save()?;

    println!("{} Registry '{}' added: {}", "✓".green(), name, url);
    Ok(())
}

pub fn cmd_registry_remove(name: &str) -> Result<()> {
    let mut cfg = Config::load_or_default();

    let before = cfg.registries.len();
    cfg.registries.retain(|r| r.name != name);

    if cfg.registries.len() == before {
        anyhow::bail!("Registry '{}' not found.", name);
    }

    cfg.save()?;
    println!("{} Registry '{}' removed.", "✓".green(), name);
    Ok(())
}
