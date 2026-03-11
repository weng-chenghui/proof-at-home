use anyhow::{Context, Result};
use colored::Colorize;
use serde_json::Value;
use std::collections::HashMap;

use crate::ai::{self, AiProvider};
use crate::budget::BudgetTracker;
use crate::config::Config;
use crate::server_client::api::ServerClient;
use crate::strategy_store::loader::{
    self, concatenate_memories, load_memories_for_agent, render_agent_strategy, AgentStrategyVars,
};

#[derive(Debug, Clone)]
pub struct AgentStep {
    pub name: String,
    #[allow(dead_code)]
    pub strategy_name: String,
    pub cost_usd: f64,
    pub input_tokens: u64,
    pub output_tokens: u64,
}

pub struct AgentOrchestrator {
    config: Config,
    provider: Box<dyn AiProvider>,
    client: ServerClient,
    agent_id: String,
    run_id: String,
    budget: BudgetTracker,
    steps: Vec<AgentStep>,
    total_cost: f64,
}

impl AgentOrchestrator {
    pub fn new(config: Config) -> Result<Self> {
        let provider = ai::create_provider(&config)?;
        let client = ServerClient::new(&config.server_url(), &config.api.auth_token);
        let run_id = format!("run-{}", &uuid::Uuid::new_v4().to_string()[..8]);
        let budget_usd = config.budget_usd();

        Ok(Self {
            config,
            provider,
            client,
            agent_id: "lesson-agent".to_string(),
            run_id,
            budget: BudgetTracker::new(budget_usd),
            steps: Vec::new(),
            total_cost: 0.0,
        })
    }

    /// Set a custom agent ID (default is "lesson-agent").
    pub fn with_agent_id(mut self, id: &str) -> Self {
        self.agent_id = id.to_string();
        self
    }

    /// Share a budget tracker with child orchestrators.
    pub fn with_budget(mut self, budget: BudgetTracker) -> Self {
        self.budget = budget;
        self
    }

    pub fn run_id(&self) -> &str {
        &self.run_id
    }

    #[allow(dead_code)]
    pub fn budget(&self) -> &BudgetTracker {
        &self.budget
    }

    pub fn steps(&self) -> &[AgentStep] {
        &self.steps
    }

    pub fn total_cost(&self) -> f64 {
        self.total_cost
    }

    /// Execute a single agent step using the named strategy.
    pub async fn execute_step(
        &mut self,
        step_name: &str,
        strategy_name: &str,
        resource_arguments: &str,
        agent_state: &str,
        tags: &[&str],
    ) -> Result<String> {
        if self.budget.is_exhausted() {
            anyhow::bail!("Budget exhausted after spending ${:.4}", self.total_cost);
        }

        let strategy = loader::load_strategy(strategy_name)
            .with_context(|| format!("Loading strategy '{}'", strategy_name))?;

        // Load and inject memories
        let memories = load_memories_for_agent(&self.agent_id, tags, 8000)?;
        let memory_text = concatenate_memories(&memories, 8000);

        let vars = AgentStrategyVars {
            resource_arguments: resource_arguments.to_string(),
            agent_memories: if memory_text.is_empty() {
                "(No memories yet)".to_string()
            } else {
                memory_text
            },
            agent_state: agent_state.to_string(),
        };

        let prompt = render_agent_strategy(&strategy, &vars);
        let model = self.config.model();
        let response = self.provider.complete(&prompt, &model, 16384).await?;

        self.budget.add_cost(response.cost_usd);
        self.total_cost += response.cost_usd;

        let step = AgentStep {
            name: step_name.to_string(),
            strategy_name: strategy_name.to_string(),
            cost_usd: response.cost_usd,
            input_tokens: response.usage.input_tokens,
            output_tokens: response.usage.output_tokens,
        };

        println!(
            "  {} {} (${:.4}, {}+{} tokens)",
            "✓".green(),
            step_name,
            response.cost_usd,
            response.usage.input_tokens,
            response.usage.output_tokens,
        );

        self.steps.push(step);
        Ok(response.text)
    }

    /// Run the full lesson agent pipeline.
    pub async fn run_lesson(
        &mut self,
        topic: Option<&str>,
        conjecture_ids: &[String],
        difficulty: Option<&str>,
    ) -> Result<String> {
        println!("{}", "Lesson Agent".bold().cyan());
        println!("Run ID: {}", self.run_id.dimmed());
        println!();

        // Build resource arguments from conjectures
        let mut resource_parts = Vec::new();
        resource_parts.push(format!(
            "**Topic:** {}",
            topic.unwrap_or("general mathematics")
        ));
        resource_parts.push(format!(
            "**Difficulty:** {}",
            difficulty.unwrap_or("medium")
        ));

        if !conjecture_ids.is_empty() {
            resource_parts.push(format!("**Conjecture IDs:** {}", conjecture_ids.join(", ")));
            for cid in conjecture_ids {
                match self.client.fetch_conjecture(cid).await {
                    Ok(conj) => {
                        let args = loader::build_resource_arguments_for_conjecture(&conj);
                        resource_parts.push(format!("\n### Conjecture: {}\n{}", cid, args));
                    }
                    Err(e) => {
                        eprintln!("  {}: Could not fetch {}: {}", "Warning".yellow(), cid, e);
                    }
                }
            }
        }

        let resource_args = resource_parts.join("\n");

        // Collect tags for memory retrieval
        let topic_str = topic.unwrap_or("").to_string();
        let tags: Vec<&str> = if topic_str.is_empty() {
            vec![]
        } else {
            vec![&topic_str]
        };

        // Step 1: PLAN
        println!("{}", "Step 1: Planning...".dimmed());
        let plan_result = self
            .execute_step("plan", "agent-lesson-plan", &resource_args, "{}", &tags)
            .await?;

        // Step 2: ASSESS
        println!("{}", "Step 2: Assessing resources...".dimmed());
        let assess_result = self
            .execute_step(
                "assess",
                "agent-lesson-assess",
                &resource_args,
                &plan_result,
                &tags,
            )
            .await?;

        // Step 3: GENERATE — use the existing compose-lesson strategy
        println!("{}", "Step 3: Generating lesson...".dimmed());
        let enriched_args = format!(
            "{}\n\n## Plan\n{}\n\n## Assessment\n{}",
            resource_args, plan_result, assess_result
        );

        let strategy = loader::auto_select_by_kind("lesson")
            .unwrap_or_else(|_| loader::load_strategy("compose-lesson").unwrap());

        let _memories = load_memories_for_agent(&self.agent_id, &tags, 8000)?;

        // Use the lesson strategy with enriched context
        let vars = loader::LessonStrategyVars {
            resource_arguments: enriched_args.clone(),
        };
        let prompt = loader::render_lesson_strategy(&strategy, &vars);
        let model = self.config.model();
        let response = self.provider.complete(&prompt, &model, 16384).await?;
        self.budget.add_cost(response.cost_usd);
        self.total_cost += response.cost_usd;

        self.steps.push(AgentStep {
            name: "generate".to_string(),
            strategy_name: strategy.meta.name.clone(),
            cost_usd: response.cost_usd,
            input_tokens: response.usage.input_tokens,
            output_tokens: response.usage.output_tokens,
        });

        println!(
            "  {} generate (${:.4}, {}+{} tokens)",
            "✓".green(),
            response.cost_usd,
            response.usage.input_tokens,
            response.usage.output_tokens,
        );

        let mut lesson_md = response.text.trim().to_string();

        // Step 4: ITERATE — self-review, up to 2 rounds
        for round in 0..2 {
            println!(
                "{}",
                format!("Step 4: Reviewing (round {})...", round + 1).dimmed()
            );
            let state = serde_json::json!({
                "round": round + 1,
                "plan": plan_result,
                "assessment": assess_result,
            });

            let review_result = self
                .execute_step(
                    &format!("iterate-{}", round + 1),
                    "agent-lesson-iterate",
                    &lesson_md,
                    &state.to_string(),
                    &tags,
                )
                .await?;

            // Parse review response
            if let Ok(review) = extract_json_from_response(&review_result) {
                let score = review.get("score").and_then(|v| v.as_i64()).unwrap_or(8);
                println!("  Score: {}/10", score);

                if score >= 7 {
                    break;
                }

                // Use revised lesson if provided
                if let Some(revised) = review.get("revised_lesson").and_then(|v| v.as_str()) {
                    if !revised.is_empty() && revised != "null" {
                        lesson_md = revised.to_string();
                        println!("  {}", "Lesson revised".yellow());
                    }
                }
            } else {
                break; // Can't parse review, stop iterating
            }
        }

        // Step 5: REFLECT — extract memories
        println!("{}", "Step 5: Reflecting...".dimmed());
        let run_summary = serde_json::json!({
            "run_id": self.run_id,
            "topic": topic,
            "conjecture_ids": conjecture_ids,
            "difficulty": difficulty,
            "total_cost": self.total_cost,
            "steps": self.steps.iter().map(|s| {
                serde_json::json!({
                    "name": s.name,
                    "cost": s.cost_usd,
                })
            }).collect::<Vec<_>>(),
        });

        let reflect_result = self
            .execute_step(
                "reflect",
                "agent-lesson-reflect",
                &format!("## Lesson\n{}", lesson_md),
                &run_summary.to_string(),
                &tags,
            )
            .await?;

        // Parse and save memories
        if let Ok(reflection) = extract_json_from_response(&reflect_result) {
            if let Some(memories) = reflection.get("memories").and_then(|v| v.as_array()) {
                let mut count = 0;
                for mem in memories {
                    let name = match mem.get("name").and_then(|v| v.as_str()) {
                        Some(n) => n,
                        None => continue,
                    };
                    let kind = mem
                        .get("kind")
                        .and_then(|v| v.as_str())
                        .unwrap_or("memory-lesson");
                    let body = mem.get("body").and_then(|v| v.as_str()).unwrap_or("");
                    let mem_tags: Vec<String> = mem
                        .get("tags")
                        .and_then(|v| v.as_array())
                        .map(|arr| {
                            arr.iter()
                                .filter_map(|t| t.as_str().map(String::from))
                                .collect()
                        })
                        .unwrap_or_default();
                    let confidence = mem
                        .get("confidence")
                        .and_then(|v| v.as_f64())
                        .unwrap_or(0.5);

                    let mut extra = HashMap::new();
                    extra.insert(
                        "agent_id".to_string(),
                        toml::Value::String(self.agent_id.clone()),
                    );
                    extra.insert(
                        "source_run_id".to_string(),
                        toml::Value::String(self.run_id.clone()),
                    );
                    extra.insert("confidence".to_string(), toml::Value::Float(confidence));
                    let tag_values: Vec<toml::Value> = mem_tags
                        .iter()
                        .map(|t| toml::Value::String(t.clone()))
                        .collect();
                    extra.insert("tags".to_string(), toml::Value::Array(tag_values));
                    extra.insert(
                        "created_at".to_string(),
                        toml::Value::String(chrono::Utc::now().to_rfc3339()),
                    );

                    let desc = body.lines().next().unwrap_or("Agent memory");
                    if let Ok(path) = loader::write_memory_file(name, kind, desc, body, &extra) {
                        println!("  {} Memory: {} -> {}", "✓".green(), name, path.display());
                        count += 1;
                    }
                }
                if count > 0 {
                    println!("  Created {} new memories", count);
                }
            }
        }

        println!();
        Ok(lesson_md)
    }

    /// Run the full series agent pipeline: PLAN -> ASSESS -> GENERATE -> lesson children -> AUDIT -> REFLECT.
    #[allow(dead_code)]
    pub async fn run_series(
        &mut self,
        topic: &str,
        depth: Option<u32>,
        difficulty: Option<&str>,
    ) -> Result<String> {
        println!("{}", "Series Agent".bold().cyan());
        println!("Run ID: {}", self.run_id.dimmed());
        println!();

        let resource_args = build_series_resource_args(topic, depth, difficulty);
        let tags: Vec<&str> = vec![topic];

        // Step 1: PLAN
        println!("{}", "Step 1: Planning series...".dimmed());
        let plan_result = self
            .execute_step("plan", "agent-series-plan", &resource_args, "{}", &tags)
            .await?;

        // Step 2: ASSESS
        println!("{}", "Step 2: Assessing series...".dimmed());
        let assess_result = self
            .execute_step(
                "assess",
                "agent-series-assess",
                &resource_args,
                &plan_result,
                &tags,
            )
            .await?;

        // Step 3: GENERATE manifest
        println!("{}", "Step 3: Generating series manifest...".dimmed());
        let enriched_args = format!(
            "{}\n\n## Plan\n{}\n\n## Assessment\n{}",
            resource_args, plan_result, assess_result
        );
        let manifest_result = self
            .execute_step(
                "generate",
                "agent-series-generate",
                &enriched_args,
                "{}",
                &tags,
            )
            .await?;

        // Parse manifest and generate each lesson
        let manifest = extract_json_from_response(&manifest_result)
            .unwrap_or_else(|_| serde_json::json!({"lessons": []}));

        let lessons_arr = manifest
            .get("lessons")
            .and_then(|v| v.as_array())
            .cloned()
            .unwrap_or_default();

        println!(
            "{}",
            format!("Step 4: Generating {} lessons...", lessons_arr.len()).dimmed()
        );

        let mut generated_lessons = Vec::new();
        for (i, lesson_spec) in lessons_arr.iter().enumerate() {
            let lesson_topic = lesson_spec
                .get("topic")
                .and_then(|v| v.as_str())
                .unwrap_or(topic);
            let lesson_difficulty = lesson_spec
                .get("difficulty")
                .and_then(|v| v.as_str())
                .or(difficulty);
            let lesson_conjectures: Vec<String> = lesson_spec
                .get("conjecture_ids")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|c| c.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default();

            println!(
                "{}",
                format!(
                    "  Lesson {}/{}: {}...",
                    i + 1,
                    lessons_arr.len(),
                    lesson_topic
                )
                .dimmed()
            );

            // Spawn child orchestrator sharing the same budget
            let mut child = AgentOrchestrator::new(self.config.clone())?
                .with_agent_id("lesson-agent")
                .with_budget(self.budget.clone());

            match child
                .run_lesson(Some(lesson_topic), &lesson_conjectures, lesson_difficulty)
                .await
            {
                Ok(lesson_md) => {
                    self.total_cost += child.total_cost();
                    for step in child.steps() {
                        self.steps.push(step.clone());
                    }
                    generated_lessons.push(serde_json::json!({
                        "topic": lesson_topic,
                        "difficulty": lesson_difficulty.unwrap_or("medium"),
                        "content": lesson_md,
                    }));
                }
                Err(e) => {
                    eprintln!(
                        "  {}: Lesson generation failed for '{}': {}",
                        "Warning".yellow(),
                        lesson_topic,
                        e
                    );
                }
            }
        }

        // Build combined content for audit
        let mut all_lessons_text = String::new();
        for (i, lesson) in generated_lessons.iter().enumerate() {
            all_lessons_text.push_str(&format!(
                "\n\n## Lesson {} — {}\n{}",
                i + 1,
                lesson["topic"].as_str().unwrap_or(""),
                lesson["content"].as_str().unwrap_or(""),
            ));
        }

        // Step 5: AUDIT
        println!("{}", "Step 5: Auditing series...".dimmed());
        let audit_args = format!(
            "{}\n\n## Series Manifest\n{}\n\n## Generated Lessons\n{}",
            resource_args, manifest_result, all_lessons_text
        );
        let _audit_result = self
            .execute_step("audit", "agent-series-audit", &audit_args, "{}", &tags)
            .await?;

        // Step 6: REFLECT
        println!("{}", "Step 6: Reflecting...".dimmed());
        let run_summary = serde_json::json!({
            "run_id": self.run_id,
            "topic": topic,
            "depth": depth,
            "difficulty": difficulty,
            "total_cost": self.total_cost,
            "lessons_generated": generated_lessons.len(),
            "steps": self.steps.iter().map(|s| {
                serde_json::json!({
                    "name": s.name,
                    "cost": s.cost_usd,
                })
            }).collect::<Vec<_>>(),
        });

        let _reflect_result = self
            .execute_step(
                "reflect",
                "agent-lesson-reflect",
                &format!("## Series\n{}", all_lessons_text),
                &run_summary.to_string(),
                &tags,
            )
            .await?;

        // Build final series JSON with all generated content
        let result = serde_json::json!({
            "manifest": manifest,
            "lessons": generated_lessons,
        });

        println!();
        Ok(result.to_string())
    }

    /// Run the series pipeline starting from an existing plan (skipping the PLAN step).
    pub async fn run_series_from_plan(&mut self, plan: &serde_json::Value) -> Result<String> {
        let topic = plan
            .get("topic")
            .and_then(|v| v.as_str())
            .unwrap_or("mathematics");
        let depth = plan.get("depth").and_then(|v| v.as_u64()).map(|d| d as u32);
        let difficulty = plan.get("difficulty").and_then(|v| v.as_str());

        println!("{}", "Series Agent (from plan)".bold().cyan());
        println!("Run ID: {}", self.run_id.dimmed());
        println!();

        let resource_args = build_series_resource_args(topic, depth, difficulty);
        let tags: Vec<&str> = vec![topic];
        let plan_str = serde_json::to_string_pretty(plan)?;

        // Step 1: ASSESS
        println!("{}", "Step 1: Assessing series...".dimmed());
        let assess_result = self
            .execute_step(
                "assess",
                "agent-series-assess",
                &resource_args,
                &plan_str,
                &tags,
            )
            .await?;

        // Step 2: GENERATE manifest
        println!("{}", "Step 2: Generating series manifest...".dimmed());
        let enriched_args = format!(
            "{}\n\n## Plan\n{}\n\n## Assessment\n{}",
            resource_args, plan_str, assess_result
        );
        let manifest_result = self
            .execute_step(
                "generate",
                "agent-series-generate",
                &enriched_args,
                "{}",
                &tags,
            )
            .await?;

        // Parse manifest and generate each lesson
        let manifest = extract_json_from_response(&manifest_result)
            .unwrap_or_else(|_| serde_json::json!({"lessons": []}));

        let lessons_arr = manifest
            .get("lessons")
            .and_then(|v| v.as_array())
            .cloned()
            .unwrap_or_default();

        println!(
            "{}",
            format!("Step 3: Generating {} lessons...", lessons_arr.len()).dimmed()
        );

        let mut generated_lessons = Vec::new();
        for (i, lesson_spec) in lessons_arr.iter().enumerate() {
            let lesson_topic = lesson_spec
                .get("topic")
                .and_then(|v| v.as_str())
                .unwrap_or(topic);
            let lesson_difficulty = lesson_spec
                .get("difficulty")
                .and_then(|v| v.as_str())
                .or(difficulty);
            let lesson_conjectures: Vec<String> = lesson_spec
                .get("conjecture_ids")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|c| c.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default();

            println!(
                "{}",
                format!(
                    "  Lesson {}/{}: {}...",
                    i + 1,
                    lessons_arr.len(),
                    lesson_topic
                )
                .dimmed()
            );

            let mut child = AgentOrchestrator::new(self.config.clone())?
                .with_agent_id("lesson-agent")
                .with_budget(self.budget.clone());

            match child
                .run_lesson(Some(lesson_topic), &lesson_conjectures, lesson_difficulty)
                .await
            {
                Ok(lesson_md) => {
                    self.total_cost += child.total_cost();
                    for step in child.steps() {
                        self.steps.push(step.clone());
                    }
                    generated_lessons.push(serde_json::json!({
                        "topic": lesson_topic,
                        "difficulty": lesson_difficulty.unwrap_or("medium"),
                        "content": lesson_md,
                    }));
                }
                Err(e) => {
                    eprintln!(
                        "  {}: Lesson generation failed for '{}': {}",
                        "Warning".yellow(),
                        lesson_topic,
                        e
                    );
                }
            }
        }

        // Build combined content for audit
        let mut all_lessons_text = String::new();
        for (i, lesson) in generated_lessons.iter().enumerate() {
            all_lessons_text.push_str(&format!(
                "\n\n## Lesson {} — {}\n{}",
                i + 1,
                lesson["topic"].as_str().unwrap_or(""),
                lesson["content"].as_str().unwrap_or(""),
            ));
        }

        // Step 4: AUDIT
        println!("{}", "Step 4: Auditing series...".dimmed());
        let audit_args = format!(
            "{}\n\n## Series Manifest\n{}\n\n## Generated Lessons\n{}",
            resource_args, manifest_result, all_lessons_text
        );
        let _audit_result = self
            .execute_step("audit", "agent-series-audit", &audit_args, "{}", &tags)
            .await?;

        let result = serde_json::json!({
            "manifest": manifest,
            "lessons": generated_lessons,
        });

        println!();
        Ok(result.to_string())
    }

    /// Run an audit on existing series content.
    pub async fn run_audit(&mut self, series_content: &str) -> Result<String> {
        println!("{}", "Series Audit".bold().cyan());
        println!("Run ID: {}", self.run_id.dimmed());
        println!();

        println!("{}", "Auditing series...".dimmed());
        let result = self
            .execute_step("audit", "agent-series-audit", series_content, "{}", &[])
            .await?;

        println!();
        Ok(result)
    }
}

/// Build resource arguments string for series operations.
fn build_series_resource_args(topic: &str, depth: Option<u32>, difficulty: Option<&str>) -> String {
    let mut parts = Vec::new();
    parts.push(format!("**Topic:** {}", topic));
    parts.push(format!("**Depth:** {} lessons", depth.unwrap_or(3)));
    parts.push(format!(
        "**Difficulty:** {}",
        difficulty.unwrap_or("easy-medium")
    ));
    parts.join("\n")
}

/// Extract a JSON object from an AI response that may contain markdown code blocks.
fn extract_json_from_response(text: &str) -> Result<Value> {
    // Try direct parse first
    if let Ok(v) = serde_json::from_str(text) {
        return Ok(v);
    }

    // Try to find JSON in code blocks
    let trimmed = text.trim();
    for block_start in ["```json", "```"] {
        if let Some(start) = trimmed.find(block_start) {
            let after = &trimmed[start + block_start.len()..];
            if let Some(end) = after.find("```") {
                let json_str = after[..end].trim();
                if let Ok(v) = serde_json::from_str(json_str) {
                    return Ok(v);
                }
            }
        }
    }

    anyhow::bail!("Could not extract JSON from response")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_json_direct() {
        let input = r#"{"score": 8, "feedback": "good"}"#;
        let v = extract_json_from_response(input).unwrap();
        assert_eq!(v["score"], 8);
    }

    #[test]
    fn test_extract_json_code_block() {
        let input = "```json\n{\"score\": 8}\n```";
        let v = extract_json_from_response(input).unwrap();
        assert_eq!(v["score"], 8);
    }

    #[test]
    fn test_extract_json_with_preamble() {
        let input = "Here is my review:\n\n```json\n{\"score\": 9}\n```\n\nDone.";
        let v = extract_json_from_response(input).unwrap();
        assert_eq!(v["score"], 9);
    }

    #[test]
    fn test_extract_json_plain_block() {
        let input = "```\n{\"score\": 7}\n```";
        let v = extract_json_from_response(input).unwrap();
        assert_eq!(v["score"], 7);
    }

    #[test]
    fn test_extract_json_invalid() {
        let input = "not json at all";
        assert!(extract_json_from_response(input).is_err());
    }
}
