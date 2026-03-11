use anyhow::{Context, Result};
use serde::Deserialize;

/// A single entry in a strategy registry.
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct RegistryEntry {
    pub name: String,
    #[serde(default)]
    pub version: String,
    #[serde(default)]
    pub author: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub prover: String,
    /// Source reference, e.g. "github:user/repo/path/to/strategy.md"
    #[serde(default)]
    pub source: String,
    #[serde(default)]
    pub tags: Vec<String>,
    #[serde(default)]
    pub updated_at: String,
}

/// A strategy/pipeline registry (JSON file hosted in a Git repo).
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct Registry {
    /// Schema version (currently 1).
    #[serde(default = "default_schema_version")]
    pub version: u32,
    #[serde(default)]
    pub name: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub strategies: Vec<RegistryEntry>,
    #[serde(default)]
    pub pipelines: Vec<RegistryEntry>,
}

fn default_schema_version() -> u32 {
    1
}

/// Fetch a registry from a URL.
/// Supports `github:user/repo` shorthand → raw.githubusercontent.com/user/repo/main/registry.json
pub async fn fetch_registry(url: &str) -> Result<Registry> {
    let resolved = resolve_registry_url(url);

    let client = reqwest::Client::new();
    let resp = client
        .get(&resolved)
        .header("User-Agent", "pah-cli")
        .send()
        .await
        .with_context(|| format!("Failed to fetch registry from {}", resolved))?;

    if !resp.status().is_success() {
        anyhow::bail!("Registry fetch failed: {} {}", resp.status(), resolved);
    }

    let registry: Registry = resp.json().await.context("Failed to parse registry JSON")?;

    Ok(registry)
}

/// Search a registry for entries matching a query.
/// Matches against name, description, tags, and author (case-insensitive).
/// Optionally filters by kind and/or prover.
pub fn search_registry<'a>(
    registry: &'a Registry,
    query: &str,
    kind: Option<&str>,
    prover: Option<&str>,
) -> Vec<&'a RegistryEntry> {
    let q = query.to_lowercase();

    let mut results: Vec<&RegistryEntry> = registry
        .strategies
        .iter()
        .chain(registry.pipelines.iter())
        .filter(|entry| {
            if let Some(k) = kind {
                if !entry.kind.eq_ignore_ascii_case(k) {
                    return false;
                }
            }
            if let Some(p) = prover {
                if !entry.prover.eq_ignore_ascii_case(p) {
                    return false;
                }
            }

            // Fuzzy match: check if query appears in name, description, tags, or author
            entry.name.to_lowercase().contains(&q)
                || entry.description.to_lowercase().contains(&q)
                || entry.author.to_lowercase().contains(&q)
                || entry.tags.iter().any(|t| t.to_lowercase().contains(&q))
        })
        .collect();

    // Sort by name for deterministic output
    results.sort_by(|a, b| a.name.cmp(&b.name));
    results
}

/// Resolve a registry URL, expanding `github:user/repo` shorthand.
fn resolve_registry_url(url: &str) -> String {
    if let Some(rest) = url.strip_prefix("github:") {
        format!(
            "https://raw.githubusercontent.com/{}/main/registry.json",
            rest
        )
    } else {
        url.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_registry_json() -> &'static str {
        r#"{
            "version": 1,
            "name": "PAH Official",
            "description": "Official strategy registry",
            "strategies": [
                {
                    "name": "prove-lean-lemma",
                    "version": "1.0.0",
                    "author": "alice",
                    "description": "Default Lean 4 proving strategy",
                    "kind": "prove",
                    "prover": "lean",
                    "source": "github:pah/strategies/prove-lean-lemma.md",
                    "tags": ["lean", "default"],
                    "updated_at": "2026-01-01T00:00:00Z"
                },
                {
                    "name": "prove-rocq-auto",
                    "version": "1.0.0",
                    "author": "bob",
                    "description": "Rocq auto-proving strategy",
                    "kind": "prove",
                    "prover": "rocq",
                    "source": "github:pah/strategies/prove-rocq-auto.md",
                    "tags": ["rocq", "auto"],
                    "updated_at": "2026-01-01T00:00:00Z"
                },
                {
                    "name": "compose-lesson",
                    "version": "1.0.0",
                    "author": "alice",
                    "description": "Compose a lesson from conjectures",
                    "kind": "lesson",
                    "prover": "",
                    "source": "github:pah/strategies/compose-lesson.md",
                    "tags": ["lesson", "compose"],
                    "updated_at": "2026-01-01T00:00:00Z"
                }
            ],
            "pipelines": [
                {
                    "name": "lesson-default",
                    "version": "1.0.0",
                    "author": "alice",
                    "description": "Default lesson generation pipeline",
                    "kind": "pipeline",
                    "prover": "",
                    "source": "github:pah/pipelines/lesson-default.toml",
                    "tags": ["lesson", "default"],
                    "updated_at": "2026-01-01T00:00:00Z"
                }
            ]
        }"#
    }

    #[test]
    fn test_deserialize_registry() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        assert_eq!(registry.version, 1);
        assert_eq!(registry.name, "PAH Official");
        assert_eq!(registry.strategies.len(), 3);
        assert_eq!(registry.pipelines.len(), 1);
    }

    #[test]
    fn test_search_by_name() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "lean", None, None);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "prove-lean-lemma");
    }

    #[test]
    fn test_search_by_kind() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "", Some("prove"), None);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_search_by_prover() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "", None, Some("rocq"));
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "prove-rocq-auto");
    }

    #[test]
    fn test_search_by_tag() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "auto", None, None);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "prove-rocq-auto");
    }

    #[test]
    fn test_search_by_author() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "bob", None, None);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_search_no_results() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "nonexistent", None, None);
        assert!(results.is_empty());
    }

    #[test]
    fn test_search_includes_pipelines() {
        let registry: Registry = serde_json::from_str(sample_registry_json()).unwrap();
        let results = search_registry(&registry, "lesson-default", None, None);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].kind, "pipeline");
    }

    #[test]
    fn test_resolve_github_shorthand() {
        let url = resolve_registry_url("github:alice/strategies");
        assert_eq!(
            url,
            "https://raw.githubusercontent.com/alice/strategies/main/registry.json"
        );
    }

    #[test]
    fn test_resolve_full_url() {
        let url = resolve_registry_url("https://example.com/registry.json");
        assert_eq!(url, "https://example.com/registry.json");
    }
}
