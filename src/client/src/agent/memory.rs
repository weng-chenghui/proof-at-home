use anyhow::Result;
use std::collections::HashMap;

use crate::strategy_store::loader;

/// List memories, optionally filtered by kind and agent_id.
pub fn list_memories(
    kind: Option<&str>,
    agent: Option<&str>,
) -> Result<Vec<loader::LoadedStrategy>> {
    let all = loader::load_all_strategies()?;
    let filtered: Vec<_> = all
        .into_iter()
        .filter(|s| s.meta.kind.starts_with("memory"))
        .filter(|s| kind.is_none_or(|k| s.meta.kind == k))
        .filter(|s| {
            agent.is_none_or(|a| {
                s.meta
                    .extra
                    .get("agent_id")
                    .and_then(|v| v.as_str())
                    .map(|id| id == a)
                    .unwrap_or(false)
            })
        })
        .collect();
    Ok(filtered)
}

/// Get a specific memory by name.
pub fn get_memory(name: &str) -> Result<loader::LoadedStrategy> {
    loader::load_strategy(name)
}

/// Create a new memory file.
pub fn create_memory(
    name: &str,
    kind: &str,
    body: &str,
    tags: &[String],
    agent_id: &str,
) -> Result<std::path::PathBuf> {
    let mut extra = HashMap::new();
    if !agent_id.is_empty() {
        extra.insert(
            "agent_id".to_string(),
            toml::Value::String(agent_id.to_string()),
        );
    }
    if !tags.is_empty() {
        let tag_values: Vec<toml::Value> = tags
            .iter()
            .map(|t| toml::Value::String(t.clone()))
            .collect();
        extra.insert("tags".to_string(), toml::Value::Array(tag_values));
    }
    extra.insert(
        "created_at".to_string(),
        toml::Value::String(chrono::Utc::now().to_rfc3339()),
    );

    let description = body.lines().next().unwrap_or("").to_string();
    loader::write_memory_file(name, kind, &description, body, &extra)
}

/// Delete a memory file by name.
pub fn forget_memory(name: &str) -> Result<()> {
    let dir = loader::strategies_dir()?;
    let path = dir.join(format!("{}.md", name));
    if path.exists() {
        std::fs::remove_file(&path)?;
        Ok(())
    } else {
        anyhow::bail!("Memory '{}' not found at {}", name, path.display())
    }
}
