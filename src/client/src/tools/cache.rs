use std::collections::HashMap;
use std::path::PathBuf;

use super::registry::ToolInfo;

/// Cache file location: ~/.proof-at-home/tools.toml
fn cache_path() -> Option<PathBuf> {
    dirs::home_dir().map(|h| h.join(".proof-at-home").join("tools.toml"))
}

/// Maximum age of a cache entry before it expires (24 hours).
const CACHE_TTL_SECS: i64 = 24 * 60 * 60;

/// Load a single cached tool entry. Returns None if missing or expired.
pub fn load_cached_tool(name: &str) -> Option<ToolInfo> {
    let path = cache_path()?;
    let content = std::fs::read_to_string(&path).ok()?;
    let table: HashMap<String, ToolInfo> = toml::from_str(&content).ok()?;
    let info = table.get(name)?;

    // Check expiry
    if let Ok(detected) = chrono::DateTime::parse_from_rfc3339(&info.detected_at) {
        let age = chrono::Utc::now().signed_duration_since(detected);
        if age.num_seconds() > CACHE_TTL_SECS {
            return None;
        }
    }

    Some(info.clone())
}

/// Save a tool entry to the cache.
pub fn save_cached_tool(info: &ToolInfo) -> anyhow::Result<()> {
    let path = match cache_path() {
        Some(p) => p,
        None => return Ok(()),
    };

    // Load existing or start fresh
    let mut table: HashMap<String, ToolInfo> = if let Ok(content) = std::fs::read_to_string(&path) {
        toml::from_str(&content).unwrap_or_default()
    } else {
        HashMap::new()
    };

    table.insert(info.name.clone(), info.clone());

    let toml_str = toml::to_string_pretty(&table)?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&path, toml_str)?;
    Ok(())
}

/// Remove a single tool entry from the cache.
pub fn remove_cached_tool(name: &str) -> anyhow::Result<()> {
    let path = match cache_path() {
        Some(p) => p,
        None => return Ok(()),
    };

    let content = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return Ok(()),
    };

    let mut table: HashMap<String, ToolInfo> = toml::from_str(&content).unwrap_or_default();
    table.remove(name);

    let toml_str = toml::to_string_pretty(&table)?;
    std::fs::write(&path, toml_str)?;
    Ok(())
}

/// Clear the entire tool cache.
#[allow(dead_code)]
pub fn clear_cache() -> anyhow::Result<()> {
    if let Some(path) = cache_path() {
        if path.exists() {
            std::fs::remove_file(&path)?;
        }
    }
    Ok(())
}
