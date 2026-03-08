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

    pub fn run_id(&self) -> &str {
        &self.run_id
    }

    pub fn steps(&self) -> &[AgentStep] {
        &self.steps
    }

    pub fn total_cost(&self) -> f64 {
        self.total_cost
    }

    /// Execute a single agent step using the named strategy.
    async fn execute_step(
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
