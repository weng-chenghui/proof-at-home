use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::HashMap;

/// Metadata parsed from TOML frontmatter in a strategy `.md` file.
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct StrategyMeta {
    pub name: String,
    /// Strategy kind: "prove", "certify-compare", "certify-rollup"
    #[serde(default = "default_kind")]
    pub kind: String,
    /// Prover type (for prove strategies): "lean", "rocq", etc.
    #[serde(default)]
    pub prover: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub priority: i32,
    /// Sharing metadata (optional, for registry/publish)
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub author: Option<String>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default)]
    pub source: Option<String>,
    #[serde(default)]
    pub extra: HashMap<String, toml::Value>,
}

/// Errors when a strategy is missing required fields for publishing.
pub fn validate_for_publish(meta: &StrategyMeta) -> Result<()> {
    let mut missing = Vec::new();
    if meta.name.is_empty() {
        missing.push("name");
    }
    if meta.version.is_none() || meta.version.as_deref() == Some("") {
        missing.push("version");
    }
    if meta.author.is_none() || meta.author.as_deref() == Some("") {
        missing.push("author");
    }
    if meta.description.is_empty() {
        missing.push("description");
    }
    if !missing.is_empty() {
        anyhow::bail!(
            "Strategy missing required fields for publish: {}",
            missing.join(", ")
        );
    }
    Ok(())
}

fn default_kind() -> String {
    "prove".to_string()
}

/// Parse a strategy file's TOML frontmatter (delimited by `+++`) and body.
/// Returns `(meta, body)` where body is the markdown content after the closing `+++`.
pub fn parse_strategy_file(content: &str) -> Result<(StrategyMeta, String)> {
    let trimmed = content.trim_start();

    if !trimmed.starts_with("+++") {
        anyhow::bail!("Strategy file missing TOML frontmatter (expected +++ delimiter)");
    }

    let after_open = &trimmed[3..];
    let close_pos = after_open
        .find("+++")
        .context("Strategy file missing closing +++ delimiter")?;

    let frontmatter = &after_open[..close_pos];
    let body = after_open[close_pos + 3..].trim_start_matches('\n');

    let meta: StrategyMeta =
        toml::from_str(frontmatter).context("Failed to parse strategy frontmatter as TOML")?;

    Ok((meta, body.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_frontmatter() {
        let content = r#"+++
name = "prove-lean-lemma"
kind = "prove"
prover = "lean"
description = "Default Lean 4 proving strategy"
priority = 0
+++
# Prove a Lean 4 lemma

Some body content here with $ARGUMENTS.
"#;
        let (meta, body) = parse_strategy_file(content).unwrap();
        assert_eq!(meta.name, "prove-lean-lemma");
        assert_eq!(meta.kind, "prove");
        assert_eq!(meta.prover, "lean");
        assert_eq!(meta.priority, 0);
        assert!(body.starts_with("# Prove a Lean 4 lemma"));
        assert!(body.contains("$ARGUMENTS"));
    }

    #[test]
    fn test_default_kind() {
        let content = r#"+++
name = "legacy-command"
prover = "lean"
+++
Body here.
"#;
        let (meta, _) = parse_strategy_file(content).unwrap();
        assert_eq!(meta.kind, "prove");
    }

    #[test]
    fn test_missing_frontmatter() {
        let content = "# Just markdown\nNo frontmatter here.";
        assert!(parse_strategy_file(content).is_err());
    }

    #[test]
    fn test_parse_with_sharing_fields() {
        let content = r#"+++
name = "my-strategy"
version = "1.0.0"
author = "alice"
license = "MIT"
source = "github:alice/strategies/my-strategy.md"
description = "A shared strategy"
+++
Body here.
"#;
        let (meta, _) = parse_strategy_file(content).unwrap();
        assert_eq!(meta.version.as_deref(), Some("1.0.0"));
        assert_eq!(meta.author.as_deref(), Some("alice"));
        assert_eq!(meta.license.as_deref(), Some("MIT"));
        assert_eq!(
            meta.source.as_deref(),
            Some("github:alice/strategies/my-strategy.md")
        );
    }

    #[test]
    fn test_parse_without_sharing_fields() {
        let content = r#"+++
name = "legacy-strategy"
kind = "prove"
+++
Body.
"#;
        let (meta, _) = parse_strategy_file(content).unwrap();
        assert!(meta.version.is_none());
        assert!(meta.author.is_none());
        assert!(meta.license.is_none());
        assert!(meta.source.is_none());
    }

    #[test]
    fn test_validate_for_publish_ok() {
        let meta = StrategyMeta {
            name: "test".to_string(),
            kind: "prove".to_string(),
            prover: String::new(),
            description: "A test strategy".to_string(),
            priority: 0,
            version: Some("1.0.0".to_string()),
            author: Some("alice".to_string()),
            license: None,
            source: None,
            extra: HashMap::new(),
        };
        assert!(validate_for_publish(&meta).is_ok());
    }

    #[test]
    fn test_validate_for_publish_missing_version() {
        let meta = StrategyMeta {
            name: "test".to_string(),
            kind: "prove".to_string(),
            prover: String::new(),
            description: "A test strategy".to_string(),
            priority: 0,
            version: None,
            author: Some("alice".to_string()),
            license: None,
            source: None,
            extra: HashMap::new(),
        };
        let err = validate_for_publish(&meta).unwrap_err();
        assert!(err.to_string().contains("version"));
    }

    #[test]
    fn test_validate_for_publish_missing_multiple() {
        let meta = StrategyMeta {
            name: String::new(),
            kind: "prove".to_string(),
            prover: String::new(),
            description: String::new(),
            priority: 0,
            version: None,
            author: None,
            license: None,
            source: None,
            extra: HashMap::new(),
        };
        let err = validate_for_publish(&meta).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("name"));
        assert!(msg.contains("version"));
        assert!(msg.contains("author"));
        assert!(msg.contains("description"));
    }

    #[test]
    fn test_parse_extra() {
        let content = r#"+++
name = "mem-test"
kind = "memory-lesson"
description = "test memory"
priority = 50

[extra]
agent_id = "lesson-agent"
confidence = 0.8
tags = ["group-theory", "pacing"]
+++
Body here.
"#;
        let (meta, _) = parse_strategy_file(content).unwrap();
        assert_eq!(meta.kind, "memory-lesson");
        assert_eq!(
            meta.extra.get("agent_id").unwrap().as_str().unwrap(),
            "lesson-agent"
        );
    }
}
