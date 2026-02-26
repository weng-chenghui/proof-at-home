use anyhow::{Context, Result};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::config::Config;
use crate::server_client::api::Conjecture;
use crate::strategy_store::frontmatter::{parse_strategy_file, StrategyMeta};

const BUILTIN_LEAN: &str = include_str!("builtins/prove-lean-lemma.md");
const BUILTIN_ROCQ: &str = include_str!("builtins/prove-coq-lemma.md");
const BUILTIN_CERTIFY_COMPARE: &str = include_str!("builtins/certify-compare.md");
const BUILTIN_CERTIFY_ROLLUP: &str = include_str!("builtins/certify-rollup.md");

const ALL_BUILTINS: &[&str] = &[
    BUILTIN_LEAN,
    BUILTIN_ROCQ,
    BUILTIN_CERTIFY_COMPARE,
    BUILTIN_CERTIFY_ROLLUP,
];

/// A loaded strategy ready for rendering.
#[derive(Debug, Clone)]
pub struct LoadedStrategy {
    pub meta: StrategyMeta,
    pub body: String,
}

/// Directory where user strategies are stored.
pub fn strategies_dir() -> Result<PathBuf> {
    let dir = Config::config_dir()?.join("strategies");
    Ok(dir)
}

/// Ensure builtins exist on disk (written on first use).
pub fn ensure_builtins() -> Result<()> {
    let dir = strategies_dir()?;
    std::fs::create_dir_all(&dir)?;

    for content in ALL_BUILTINS {
        if let Ok((meta, _)) = parse_strategy_file(content) {
            let path = dir.join(format!("{}.md", meta.name));
            if !path.exists() {
                std::fs::write(&path, content)?;
            }
        }
    }

    Ok(())
}

/// Load all strategies from disk and builtins.
/// Strategies on disk override builtins with the same name.
pub fn load_all_strategies() -> Result<Vec<LoadedStrategy>> {
    let mut strategies: HashMap<String, LoadedStrategy> = HashMap::new();

    // Load builtins first
    for content in ALL_BUILTINS {
        if let Ok((meta, body)) = parse_strategy_file(content) {
            strategies.insert(meta.name.clone(), LoadedStrategy { meta, body });
        }
    }

    // Load user strategies (override builtins)
    let dir = strategies_dir()?;
    if dir.exists() {
        if let Ok(entries) = std::fs::read_dir(&dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) == Some("md") {
                    if let Ok(content) = std::fs::read_to_string(&path) {
                        match parse_strategy_file(&content) {
                            Ok((meta, body)) => {
                                strategies.insert(meta.name.clone(), LoadedStrategy { meta, body });
                            }
                            Err(e) => {
                                eprintln!("Warning: Skipping {}: {}", path.display(), e);
                            }
                        }
                    }
                }
            }
        }
    }

    let mut result: Vec<LoadedStrategy> = strategies.into_values().collect();
    result.sort_by(|a, b| {
        a.meta
            .priority
            .cmp(&b.meta.priority)
            .then(a.meta.name.cmp(&b.meta.name))
    });
    Ok(result)
}

/// Load a specific strategy by name.
pub fn load_strategy(name: &str) -> Result<LoadedStrategy> {
    let strategies = load_all_strategies()?;
    strategies
        .into_iter()
        .find(|c| c.meta.name == name)
        .with_context(|| format!("Strategy '{}' not found", name))
}

/// Auto-select the best prove strategy for a given prover type.
/// Picks the strategy with the lowest priority value for the matching prover.
pub fn auto_select_strategy(prover: &str) -> Result<LoadedStrategy> {
    let lowered = prover.to_lowercase();
    let normalized = match lowered.as_str() {
        "lean" | "lean4" => "lean",
        "rocq" | "coq" => "rocq",
        _ => &lowered,
    };

    let strategies = load_all_strategies()?;
    strategies
        .into_iter()
        .find(|c| c.meta.kind == "prove" && c.meta.prover == normalized)
        .with_context(|| format!("No prove strategy found for prover '{}'", prover))
}

/// Auto-select the best strategy for a given kind (e.g. "certify-compare", "certify-rollup").
pub fn auto_select_by_kind(kind: &str) -> Result<LoadedStrategy> {
    let strategies = load_all_strategies()?;
    strategies
        .into_iter()
        .find(|c| c.meta.kind == kind)
        .with_context(|| format!("No strategy found for kind '{}'", kind))
}

/// Render a prove strategy body by substituting variables.
pub fn render_strategy(
    strategy: &LoadedStrategy,
    conjecture: &Conjecture,
    vars: &StrategyVars,
) -> String {
    let arguments = build_arguments_block(conjecture);

    strategy
        .body
        .replace("$ARGUMENTS", &arguments)
        .replace("$LEAN_PATH", &vars.lean_path)
        .replace("$LAKE_PATH", &vars.lake_path)
        .replace("$ROCQ", &vars.rocq)
        .replace("$COQ_INCLUDE", &vars.coq_include)
        .replace("$SCRATCH_DIR", &vars.scratch_dir)
        .replace("$LEMMA_FILE", &vars.lemma_file)
}

/// Render a certify strategy body by substituting variables.
pub fn render_certify_strategy(strategy: &LoadedStrategy, vars: &CertifyStrategyVars) -> String {
    strategy
        .body
        .replace("$PROVER", &vars.prover)
        .replace("$CONJECTURE_TITLE", &vars.conjecture_title)
        .replace("$PROOFS", &vars.proofs)
        .replace("$PACKAGE_RANKINGS", &vars.package_rankings)
}

/// Variables available for substitution in prove strategy templates.
pub struct StrategyVars {
    pub lean_path: String,
    pub lake_path: String,
    pub rocq: String,
    pub coq_include: String,
    pub scratch_dir: String,
    pub lemma_file: String,
}

/// Variables available for substitution in certify strategy templates.
pub struct CertifyStrategyVars {
    pub prover: String,
    pub conjecture_title: String,
    pub proofs: String,
    pub package_rankings: String,
}

/// Build the $ARGUMENTS block from conjecture data.
fn build_arguments_block(conjecture: &Conjecture) -> String {
    let mut parts = Vec::new();

    parts.push(format!("**Title:** {}", conjecture.title));
    parts.push(format!("**Prover:** {}", conjecture.prover));
    parts.push(format!("**Difficulty:** {}", conjecture.difficulty));

    if !conjecture.preamble.is_empty() {
        parts.push(format!(
            "\n**Preamble (imports/setup):**\n```\n{}\n```",
            conjecture.preamble
        ));
    }

    parts.push(format!(
        "\n**Lemma to prove:**\n```\n{}\n```",
        conjecture.lemma_statement
    ));

    if !conjecture.hints.is_empty() {
        let hints = conjecture
            .hints
            .iter()
            .map(|h| format!("- {}", h))
            .collect::<Vec<_>>()
            .join("\n");
        parts.push(format!("\n**Hints:**\n{}", hints));
    }

    if !conjecture.skeleton.is_empty() {
        parts.push(format!(
            "\n**Skeleton (if provided):**\n```\n{}\n```",
            conjecture.skeleton
        ));
    }

    parts.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_builtins() {
        let strategies = load_all_strategies().unwrap();
        assert!(strategies.len() >= 4);
        let names: Vec<&str> = strategies.iter().map(|c| c.meta.name.as_str()).collect();
        assert!(names.contains(&"prove-lean-lemma"));
        assert!(names.contains(&"prove-coq-lemma"));
        assert!(names.contains(&"certify-compare"));
        assert!(names.contains(&"certify-rollup"));
    }

    #[test]
    fn test_auto_select_lean() {
        let cmd = auto_select_strategy("lean").unwrap();
        assert_eq!(cmd.meta.prover, "lean");
        assert_eq!(cmd.meta.kind, "prove");
    }

    #[test]
    fn test_auto_select_rocq() {
        let cmd = auto_select_strategy("rocq").unwrap();
        assert_eq!(cmd.meta.prover, "rocq");
        assert_eq!(cmd.meta.kind, "prove");
    }

    #[test]
    fn test_auto_select_certify_compare() {
        let cmd = auto_select_by_kind("certify-compare").unwrap();
        assert_eq!(cmd.meta.kind, "certify-compare");
    }

    #[test]
    fn test_auto_select_certify_rollup() {
        let cmd = auto_select_by_kind("certify-rollup").unwrap();
        assert_eq!(cmd.meta.kind, "certify-rollup");
    }
}
