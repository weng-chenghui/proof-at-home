use anyhow::{Context, Result};
use serde::Deserialize;

/// Metadata parsed from TOML frontmatter in a command `.md` file.
#[derive(Debug, Clone, Deserialize)]
pub struct CommandMeta {
    pub name: String,
    /// Command kind: "prove", "certify-compare", "certify-rollup"
    #[serde(default = "default_kind")]
    pub kind: String,
    /// Prover type (for prove commands): "lean", "rocq", etc.
    #[serde(default)]
    pub prover: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub priority: i32,
}

fn default_kind() -> String {
    "prove".to_string()
}

/// Parse a command file's TOML frontmatter (delimited by `+++`) and body.
/// Returns `(meta, body)` where body is the markdown content after the closing `+++`.
pub fn parse_command_file(content: &str) -> Result<(CommandMeta, String)> {
    let trimmed = content.trim_start();

    if !trimmed.starts_with("+++") {
        anyhow::bail!("Command file missing TOML frontmatter (expected +++ delimiter)");
    }

    let after_open = &trimmed[3..];
    let close_pos = after_open
        .find("+++")
        .context("Command file missing closing +++ delimiter")?;

    let frontmatter = &after_open[..close_pos];
    let body = after_open[close_pos + 3..].trim_start_matches('\n');

    let meta: CommandMeta =
        toml::from_str(frontmatter).context("Failed to parse command frontmatter as TOML")?;

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
        let (meta, body) = parse_command_file(content).unwrap();
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
        let (meta, _) = parse_command_file(content).unwrap();
        assert_eq!(meta.kind, "prove");
    }

    #[test]
    fn test_missing_frontmatter() {
        let content = "# Just markdown\nNo frontmatter here.";
        assert!(parse_command_file(content).is_err());
    }
}
