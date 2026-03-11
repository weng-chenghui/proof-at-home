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
const BUILTIN_AGENT_LESSON_PLAN: &str = include_str!("builtins/agent-lesson-plan.md");
const BUILTIN_AGENT_LESSON_ASSESS: &str = include_str!("builtins/agent-lesson-assess.md");
const BUILTIN_AGENT_LESSON_ITERATE: &str = include_str!("builtins/agent-lesson-iterate.md");
const BUILTIN_AGENT_LESSON_REFLECT: &str = include_str!("builtins/agent-lesson-reflect.md");

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
    BUILTIN_AGENT_LESSON_PLAN,
    BUILTIN_AGENT_LESSON_ASSESS,
    BUILTIN_AGENT_LESSON_ITERATE,
    BUILTIN_AGENT_LESSON_REFLECT,
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

/// Variables for agent strategy templates.
pub struct AgentStrategyVars {
    pub resource_arguments: String,
    pub agent_memories: String,
    pub agent_state: String,
}

/// Render an agent strategy body by substituting variables.
pub fn render_agent_strategy(strategy: &LoadedStrategy, vars: &AgentStrategyVars) -> String {
    strategy
        .body
        .replace("$RESOURCE_ARGUMENTS", &vars.resource_arguments)
        .replace("$AGENT_MEMORIES", &vars.agent_memories)
        .replace("$AGENT_STATE", &vars.agent_state)
}

/// Load all memories (strategies with kind starting with "memory") for a given agent.
/// Optionally filter by tags in extra.tags.
pub fn load_memories_for_agent(
    agent_id: &str,
    tags: &[&str],
    _char_limit: usize,
) -> Result<Vec<LoadedStrategy>> {
    let all = load_all_strategies()?;
    let mut memories: Vec<LoadedStrategy> = all
        .into_iter()
        .filter(|s| s.meta.kind.starts_with("memory"))
        .filter(|s| {
            s.meta
                .extra
                .get("agent_id")
                .and_then(|v| v.as_str())
                .map(|id| id == agent_id)
                .unwrap_or(true) // include memories without agent_id
        })
        .filter(|s| {
            if tags.is_empty() {
                return true;
            }
            let mem_tags: Vec<String> = s
                .meta
                .extra
                .get("tags")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|t| t.as_str().map(|s| s.to_string()))
                        .collect()
                })
                .unwrap_or_default();
            tags.iter().any(|t| mem_tags.iter().any(|mt| mt == t))
        })
        .collect();
    memories.sort_by(|a, b| b.meta.priority.cmp(&a.meta.priority));
    Ok(memories)
}

/// Write a new memory file to ~/.proof-at-home/strategies/
pub fn write_memory_file(
    name: &str,
    kind: &str,
    description: &str,
    body: &str,
    extra: &HashMap<String, toml::Value>,
) -> Result<PathBuf> {
    let dir = strategies_dir()?;
    std::fs::create_dir_all(&dir)?;
    let path = dir.join(format!("{}.md", name));

    let mut frontmatter =
        format!("name = {name:?}\nkind = {kind:?}\ndescription = {description:?}\npriority = 50\n");
    if !extra.is_empty() {
        frontmatter.push_str("\n[extra]\n");
        for (k, v) in extra {
            frontmatter.push_str(&format!("{} = {}\n", k, v));
        }
    }

    let content = format!("+++\n{}+++\n{}", frontmatter, body);
    std::fs::write(&path, &content)?;
    Ok(path)
}

/// Concatenate memory bodies up to char_limit
pub fn concatenate_memories(memories: &[LoadedStrategy], char_limit: usize) -> String {
    let mut result = String::new();
    for mem in memories {
        let entry = format!(
            "### Memory: {} ({})\n{}\n\n",
            mem.meta.name, mem.meta.description, mem.body
        );
        if result.len() + entry.len() > char_limit {
            break;
        }
        result.push_str(&entry);
    }
    result
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

    #[test]
    fn test_load_agent_builtins() {
        let names = [
            "agent-lesson-plan",
            "agent-lesson-assess",
            "agent-lesson-iterate",
            "agent-lesson-reflect",
        ];
        for name in &names {
            let s = load_strategy(name).unwrap();
            assert_eq!(s.meta.name, *name);
            assert!(
                s.meta.kind.starts_with("agent"),
                "kind should start with 'agent' for {}",
                name
            );
        }
    }

    #[test]
    fn test_render_agent_strategy() {
        let strategy = load_strategy("agent-lesson-plan").unwrap();
        let vars = AgentStrategyVars {
            resource_arguments: "TOPIC_HERE".to_string(),
            agent_memories: "MEM_HERE".to_string(),
            agent_state: "STATE_HERE".to_string(),
        };
        let rendered = render_agent_strategy(&strategy, &vars);
        assert!(rendered.contains("TOPIC_HERE"));
        assert!(rendered.contains("MEM_HERE"));
        assert!(rendered.contains("STATE_HERE"));
        assert!(!rendered.contains("$RESOURCE_ARGUMENTS"));
        assert!(!rendered.contains("$AGENT_MEMORIES"));
        assert!(!rendered.contains("$AGENT_STATE"));
    }

    #[test]
    fn test_concatenate_memories_respects_limit() {
        let mem1 = LoadedStrategy {
            meta: StrategyMeta {
                name: "mem-a".to_string(),
                kind: "memory-lesson".to_string(),
                prover: String::new(),
                description: "desc-a".to_string(),
                priority: 50,
                version: None,
                author: None,
                license: None,
                source: None,
                extra: HashMap::new(),
            },
            body: "A".repeat(100),
        };
        let mem2 = LoadedStrategy {
            meta: StrategyMeta {
                name: "mem-b".to_string(),
                kind: "memory-lesson".to_string(),
                prover: String::new(),
                description: "desc-b".to_string(),
                priority: 50,
                version: None,
                author: None,
                license: None,
                source: None,
                extra: HashMap::new(),
            },
            body: "B".repeat(100),
        };
        // Set limit so only first memory fits
        let result = concatenate_memories(&[mem1, mem2], 150);
        assert!(result.contains("mem-a"));
        assert!(!result.contains("mem-b"));
    }

    #[test]
    fn test_concatenate_memories_format() {
        let mem = LoadedStrategy {
            meta: StrategyMeta {
                name: "mem-test".to_string(),
                kind: "memory-lesson".to_string(),
                prover: String::new(),
                description: "test desc".to_string(),
                priority: 50,
                version: None,
                author: None,
                license: None,
                source: None,
                extra: HashMap::new(),
            },
            body: "Some body text".to_string(),
        };
        let result = concatenate_memories(&[mem], 10000);
        assert!(result.contains("### Memory: mem-test (test desc)"));
        assert!(result.contains("Some body text"));
    }

    #[test]
    fn test_write_and_read_memory() {
        let dir = tempfile::tempdir().unwrap();
        // Override HOME so strategies_dir points to our temp dir
        let name = format!(
            "test-mem-{}",
            uuid::Uuid::new_v4().to_string().get(..8).unwrap()
        );
        let kind = "memory-lesson";
        let desc = "round-trip test";
        let body = "This is the memory body.\nLine two.";

        let mut extra = HashMap::new();
        extra.insert(
            "agent_id".to_string(),
            toml::Value::String("lesson-agent".to_string()),
        );

        // Write directly to temp dir
        let strat_dir = dir.path().join("strategies");
        std::fs::create_dir_all(&strat_dir).unwrap();
        let path = strat_dir.join(format!("{}.md", name));

        let mut frontmatter =
            format!("name = {name:?}\nkind = {kind:?}\ndescription = {desc:?}\npriority = 50\n");
        frontmatter.push_str("\n[extra]\nagent_id = \"lesson-agent\"\n");
        let content = format!("+++\n{}+++\n{}", frontmatter, body);
        std::fs::write(&path, &content).unwrap();

        // Read back
        let read_content = std::fs::read_to_string(&path).unwrap();
        let (meta, read_body) = parse_strategy_file(&read_content).unwrap();
        assert_eq!(meta.name, name);
        assert_eq!(meta.kind, "memory-lesson");
        assert_eq!(meta.description, "round-trip test");
        assert_eq!(
            meta.extra.get("agent_id").unwrap().as_str().unwrap(),
            "lesson-agent"
        );
        assert!(read_body.contains("This is the memory body."));
        assert!(read_body.contains("Line two."));
    }
}
