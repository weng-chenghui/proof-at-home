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
const BUILTIN_PARSE: &str = include_str!("builtins/parse-proof.md");
const BUILTIN_PARSE_TREE: &str = include_str!("builtins/parse-proof-tree.md");
const BUILTIN_VISUALIZE_DEFAULT: &str = include_str!("builtins/visualize-default.md");
const BUILTIN_VISUALIZE_GROUP_THEORY: &str = include_str!("builtins/visualize-group-theory.md");
const BUILTIN_VISUALIZE_INFO_THEORY: &str =
    include_str!("builtins/visualize-information-theory.md");
const BUILTIN_EXPOSITION_DEFAULT: &str = include_str!("builtins/exposition-default.md");
const BUILTIN_COMPOSE_LESSON: &str = include_str!("builtins/compose-lesson.md");
const BUILTIN_COMPOSE_SERIES: &str = include_str!("builtins/compose-series.md");

const ALL_BUILTINS: &[&str] = &[
    BUILTIN_LEAN,
    BUILTIN_ROCQ,
    BUILTIN_CERTIFY_COMPARE,
    BUILTIN_CERTIFY_ROLLUP,
    BUILTIN_PARSE,
    BUILTIN_PARSE_TREE,
    BUILTIN_VISUALIZE_DEFAULT,
    BUILTIN_VISUALIZE_GROUP_THEORY,
    BUILTIN_VISUALIZE_INFO_THEORY,
    BUILTIN_EXPOSITION_DEFAULT,
    BUILTIN_COMPOSE_LESSON,
    BUILTIN_COMPOSE_SERIES,
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

/// Variables available for substitution in parse strategy templates.
pub struct ParseStrategyVars {
    pub proof_script: String,
    pub conjecture_title: String,
    pub lemma_statement: String,
    pub prover: String,
}

/// Render a parse strategy body by substituting variables.
pub fn render_parse_strategy(strategy: &LoadedStrategy, vars: &ParseStrategyVars) -> String {
    strategy
        .body
        .replace("$PROOF_SCRIPT", &vars.proof_script)
        .replace("$CONJECTURE_TITLE", &vars.conjecture_title)
        .replace("$LEMMA_STATEMENT", &vars.lemma_statement)
        .replace("$PROVER", &vars.prover)
}

/// Variables available for substitution in certify strategy templates.
pub struct CertifyStrategyVars {
    pub prover: String,
    pub conjecture_title: String,
    pub proofs: String,
    pub package_rankings: String,
}

/// Variables available for substitution in exposition strategy templates.
pub struct ExpositionStrategyVars {
    pub resource_arguments: String,
}

/// Render an exposition strategy body by substituting variables.
pub fn render_exposition_strategy(
    strategy: &LoadedStrategy,
    vars: &ExpositionStrategyVars,
) -> String {
    strategy
        .body
        .replace("$RESOURCE_ARGUMENTS", &vars.resource_arguments)
}

/// Variables for lesson/series strategy templates (same shape as exposition).
pub struct LessonStrategyVars {
    pub resource_arguments: String,
}

/// Render a lesson composition strategy body by substituting variables.
pub fn render_lesson_strategy(strategy: &LoadedStrategy, vars: &LessonStrategyVars) -> String {
    strategy
        .body
        .replace("$RESOURCE_ARGUMENTS", &vars.resource_arguments)
}

/// Build a resource arguments block from a conjecture (for exposition).
pub fn build_resource_arguments_for_conjecture(conjecture: &Conjecture) -> String {
    let mut parts = Vec::new();
    parts.push("**Resource type:** Conjecture".to_string());
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

/// Build a resource arguments block from a contribution.
pub fn build_resource_arguments_for_contribution(
    contribution: &crate::server_client::api::Contribution,
    proofs: &[crate::server_client::api::Proof],
) -> String {
    let mut parts = Vec::new();
    parts.push("**Resource type:** Contribution".to_string());
    parts.push(format!(
        "**Contribution ID:** {}",
        contribution.contribution_id
    ));
    parts.push(format!("**Author:** {}", contribution.username));
    parts.push(format!(
        "**Conjectures proved/attempted:** {}/{}",
        contribution.conjectures_proved, contribution.conjectures_attempted
    ));
    parts.push(format!("**Cost:** ${:.4}", contribution.total_cost_usd));
    parts.push(format!("**Status:** {}", contribution.proof_status));

    for proof in proofs {
        parts.push(format!(
            "\n### Proof for {}\n**Success:** {}\n```\n{}\n```",
            proof.conjecture_id, proof.success, proof.proof_script
        ));
    }

    parts.join("\n")
}

/// Build the $ARGUMENTS block from conjecture data.
pub fn build_arguments_block(conjecture: &Conjecture) -> String {
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
        assert!(strategies.len() >= 5);
        let names: Vec<&str> = strategies.iter().map(|c| c.meta.name.as_str()).collect();
        assert!(names.contains(&"prove-lean-lemma"));
        assert!(names.contains(&"prove-coq-lemma"));
        assert!(names.contains(&"certify-compare"));
        assert!(names.contains(&"certify-rollup"));
        assert!(names.contains(&"parse-proof"));
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

    #[test]
    fn test_auto_select_parse() {
        let cmd = auto_select_by_kind("parse").unwrap();
        assert_eq!(cmd.meta.name, "parse-proof");
        assert_eq!(cmd.meta.kind, "parse");
    }

    #[test]
    fn test_render_parse_strategy() {
        let strategy = load_strategy("parse-proof").unwrap();
        let vars = ParseStrategyVars {
            proof_script: "Proof. auto. Qed.".into(),
            conjecture_title: "Sum of two naturals".into(),
            lemma_statement: "forall n m, n + m = m + n".into(),
            prover: "rocq".into(),
        };
        let rendered = render_parse_strategy(&strategy, &vars);
        assert!(rendered.contains("Proof. auto. Qed."));
        assert!(rendered.contains("Sum of two naturals"));
        assert!(rendered.contains("forall n m, n + m = m + n"));
        assert!(rendered.contains("rocq"));
        // Template variables should be replaced
        assert!(!rendered.contains("$PROOF_SCRIPT"));
        assert!(!rendered.contains("$CONJECTURE_TITLE"));
        assert!(!rendered.contains("$LEMMA_STATEMENT"));
        assert!(!rendered.contains("$PROVER"));
    }

    #[test]
    fn test_auto_select_visualize_default() {
        let cmd = auto_select_by_kind("visualize").unwrap();
        assert_eq!(cmd.meta.name, "visualize-default");
        assert_eq!(cmd.meta.kind, "visualize");
    }

    #[test]
    fn test_auto_select_visualize_group_theory() {
        let cmd = auto_select_by_kind("visualize-group-theory").unwrap();
        assert_eq!(cmd.meta.name, "visualize-group-theory");
    }

    #[test]
    fn test_auto_select_visualize_info_theory() {
        let cmd = auto_select_by_kind("visualize-information-theory").unwrap();
        assert_eq!(cmd.meta.name, "visualize-information-theory");
    }
}
