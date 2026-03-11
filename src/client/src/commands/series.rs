use anyhow::{bail, Context, Result};
use colored::Colorize;

use crate::agent::orchestrator::AgentOrchestrator;
use crate::budget::BudgetTracker;
use crate::config::Config;
use crate::server_client::api::{CreateLessonRequest, CreateSeriesRequest, ServerClient};
use crate::strategy_store::loader;

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load_or_default();
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let series_list = client.fetch_all_series().await?;

    if series_list.is_empty() {
        println!("No series found.");
        return Ok(());
    }

    println!(
        "{:<30} {:<40} {:<15} {:<6}",
        "Series ID", "Title", "Difficulty", "Lessons"
    );
    println!("{}", "-".repeat(91));

    for s in &series_list {
        let title = if s.title.len() > 38 {
            format!("{}...", &s.title[..35])
        } else {
            s.title.clone()
        };
        println!(
            "{:<30} {:<40} {:<15} {:<6}",
            s.series_id,
            title,
            s.difficulty,
            s.lesson_ids.len(),
        );
    }

    println!("\nTotal: {}", series_list.len());
    Ok(())
}

pub async fn cmd_get(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let s = client.fetch_series(id).await?;

    println!("{}", "=== Series ===".bold());
    println!("ID:          {}", s.series_id);
    println!("Title:       {}", s.title);
    println!("Author:      {}", s.author_username);
    println!("Difficulty:  {}", s.difficulty);
    println!("Published:   {}", s.published);
    println!("Lessons:     {}", s.lesson_ids.join(", "));

    if !s.description.is_empty() {
        println!("Description: {}", s.description);
    }

    if !s.content.is_empty() {
        println!();
        println!("{}", "─".repeat(60).dimmed());
        println!("{}", s.content);
    }

    Ok(())
}

pub async fn cmd_create(
    lessons: Option<&str>,
    output: Option<&str>,
    stdin: bool,
    method: &str,
) -> Result<()> {
    let valid_methods = ["api-assisted", "pair-proved", "manual"];
    if !valid_methods.contains(&method) {
        bail!(
            "Invalid method '{}'. Must be one of: {}",
            method,
            valid_methods.join(", ")
        );
    }

    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let lesson_ids: Vec<String> = lessons
        .map(|l| l.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let (series_md, cost) = if stdin {
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input)
            .context("Failed to read from stdin")?;
        (input.trim().to_string(), 0.0)
    } else if method == "manual" {
        bail!("Manual method requires --stdin to provide series.md content");
    } else {
        // Build resource arguments from lessons
        let mut resource_parts = Vec::new();
        resource_parts.push(format!("**Lesson IDs:** {}", lesson_ids.join(", ")));

        for lid in &lesson_ids {
            match client.fetch_lesson(lid).await {
                Ok(lesson) => {
                    resource_parts.push(format!(
                        "\n### Lesson: {}\n**Title:** {}\n**Topic:** {}\n**Difficulty:** {}\n**Conjectures:** {}",
                        lid, lesson.title, lesson.topic, lesson.difficulty,
                        lesson.conjecture_ids.join(", "),
                    ));
                }
                Err(e) => {
                    eprintln!(
                        "{}: Could not fetch lesson {}: {}",
                        "Warning".yellow(),
                        lid,
                        e
                    );
                }
            }
        }

        let resource_args = resource_parts.join("\n");

        let has_api_key = !cfg.api_key().is_empty();
        if !has_api_key {
            eprintln!(
                "{}: No AI provider configured. Exporting prompt instead.",
                "Info".cyan()
            );
            let strategy = loader::auto_select_by_kind("series")
                .unwrap_or_else(|_| loader::load_strategy("compose-series").unwrap());
            let vars = loader::LessonStrategyVars {
                resource_arguments: resource_args,
            };
            let prompt = loader::render_lesson_strategy(&strategy, &vars);
            print!("{}", prompt);
            return Ok(());
        }

        let strategy = loader::auto_select_by_kind("series")
            .unwrap_or_else(|_| loader::load_strategy("compose-series").unwrap());
        let vars = loader::LessonStrategyVars {
            resource_arguments: resource_args,
        };
        let prompt = loader::render_lesson_strategy(&strategy, &vars);

        println!("{}", "Generating series...".cyan());
        let provider = crate::ai::create_provider(&cfg)?;
        let model = cfg.model();
        let ai_response = provider.complete(&prompt, &model, 8192).await?;
        (ai_response.text.trim().to_string(), ai_response.cost_usd)
    };

    if let Some(path) = output {
        std::fs::write(path, &series_md).with_context(|| format!("Failed to write to {}", path))?;
        println!("  Written to: {}", path.green());
    }

    // Parse series frontmatter
    let (series_id, title, parsed_lesson_ids) = parse_series_frontmatter(&series_md);
    let final_lesson_ids = if parsed_lesson_ids.is_empty() {
        lesson_ids
    } else {
        parsed_lesson_ids
    };

    let req = CreateSeriesRequest {
        series_id: series_id.clone(),
        title: title.clone(),
        author_username: cfg.identity.username.clone(),
        difficulty: String::new(),
        description: String::new(),
        lesson_ids: final_lesson_ids,
        published: true,
        content: series_md,
    };

    print!("Submitting series to server... ");
    match client.create_series(&req).await {
        Ok(resp) => {
            println!("{}", "OK".green());
            println!("  Commit: {}", resp.commit_sha.cyan());
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not submit to server: {}", "Warning".yellow(), e);
        }
    }

    println!();
    println!("{}", "=".repeat(60).dimmed());
    println!("{}", " Series Created".bold());
    println!("{}", "=".repeat(60).dimmed());
    println!();
    println!("  Series ID: {}", series_id.cyan());
    println!("  Title:     {}", title);
    println!("  Method:    {}", method);
    println!("  Cost:      ${:.4}", cost);
    println!();

    Ok(())
}

pub async fn cmd_export(lessons: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let lesson_ids: Vec<String> = lessons
        .map(|l| l.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let mut resource_parts = Vec::new();
    resource_parts.push(format!("**Lesson IDs:** {}", lesson_ids.join(", ")));

    for lid in &lesson_ids {
        if let Ok(lesson) = client.fetch_lesson(lid).await {
            resource_parts.push(format!(
                "\n### Lesson: {}\n**Title:** {}\n**Topic:** {}\n**Difficulty:** {}",
                lid, lesson.title, lesson.topic, lesson.difficulty,
            ));
        }
    }

    let resource_args = resource_parts.join("\n");

    let strategy = loader::auto_select_by_kind("series")
        .unwrap_or_else(|_| loader::load_strategy("compose-series").unwrap());
    let vars = loader::LessonStrategyVars {
        resource_arguments: resource_args,
    };
    let prompt = loader::render_lesson_strategy(&strategy, &vars);
    print!("{}", prompt);

    Ok(())
}

/// Parse YAML frontmatter from series.md to extract key fields.
fn parse_series_frontmatter(content: &str) -> (String, String, Vec<String>) {
    let mut series_id = String::new();
    let mut title = String::new();
    let mut lesson_ids = Vec::new();

    if !content.starts_with("---") {
        return (
            format!("series-{}", &uuid::Uuid::new_v4().to_string()[..8]),
            "Untitled Series".to_string(),
            vec![],
        );
    }

    let rest = &content[3..];
    if let Some(end_idx) = rest.find("\n---") {
        let frontmatter = &rest[..end_idx];
        let mut in_lesson_ids = false;

        for line in frontmatter.lines() {
            let trimmed = line.trim();
            if let Some(val) = trimmed.strip_prefix("series_id:") {
                series_id = val.trim().trim_matches('"').to_string();
                in_lesson_ids = false;
            } else if let Some(val) = trimmed.strip_prefix("title:") {
                title = val.trim().trim_matches('"').to_string();
                in_lesson_ids = false;
            } else if trimmed.starts_with("lesson_ids:") {
                let val = trimmed.strip_prefix("lesson_ids:").unwrap().trim();
                if val.starts_with('[') {
                    let inner = val.trim_start_matches('[').trim_end_matches(']');
                    lesson_ids = inner
                        .split(',')
                        .map(|s| s.trim().trim_matches('"').to_string())
                        .filter(|s| !s.is_empty())
                        .collect();
                    in_lesson_ids = false;
                } else {
                    in_lesson_ids = true;
                }
            } else if in_lesson_ids && trimmed.starts_with("- ") {
                let val = trimmed.strip_prefix("- ").unwrap().trim().trim_matches('"');
                if !val.is_empty() {
                    lesson_ids.push(val.to_string());
                }
            } else if !trimmed.starts_with('-') && !trimmed.is_empty() {
                in_lesson_ids = false;
            }
        }
    }

    if series_id.is_empty() {
        series_id = format!("series-{}", &uuid::Uuid::new_v4().to_string()[..8]);
    }
    if title.is_empty() {
        title = "Untitled Series".to_string();
    }

    (series_id, title, lesson_ids)
}

/// Plan a new series from a topic. If no API key is configured, exports the
/// planning prompt for pair-proved mode instead.
pub async fn cmd_plan(
    topic: &str,
    depth: u32,
    difficulty: &str,
    budget: Option<f64>,
    output: Option<&str>,
) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    let has_api_key = !cfg.api_key().is_empty();

    // Build resource arguments
    let resource_args = format!(
        "**Topic:** {}\n**Depth:** {} lessons\n**Difficulty:** {}",
        topic, depth, difficulty
    );

    if !has_api_key {
        // Pair-proved mode: export the planning prompt
        println!(
            "{}: No AI provider configured. Exporting planning prompt for pair-proved mode.",
            "Info".cyan()
        );
        println!();

        let strategy = loader::load_strategy("agent-series-plan")
            .context("Loading agent-series-plan strategy")?;
        let vars = loader::AgentStrategyVars {
            resource_arguments: resource_args,
            agent_memories: "(No memories yet)".to_string(),
            agent_state: "{}".to_string(),
        };
        let prompt = loader::render_agent_strategy(&strategy, &vars);
        println!("{}", prompt);

        println!();
        println!("{}", "─".repeat(60).dimmed());
        println!(
            "{}",
            "Copy the above prompt to your AI assistant, then pipe the result:".bold()
        );
        println!();
        println!(
            "  {}",
            "cat plan.json | pah series generate --from -".cyan()
        );
        println!();
        return Ok(());
    }

    // API-assisted mode
    let base = if let Some(b) = budget {
        AgentOrchestrator::new(cfg.clone())?.with_budget(BudgetTracker::new(b))
    } else {
        AgentOrchestrator::new(cfg.clone())?
    };
    let mut agent = base.with_agent_id("series-agent");

    println!("{}", "Series Plan".bold().cyan());
    println!("Run ID: {}", agent.run_id().dimmed());
    println!();

    println!("{}", "Planning series...".dimmed());
    let plan_result = agent
        .execute_step("plan", "agent-series-plan", &resource_args, "{}", &[topic])
        .await?;

    // Build plan JSON
    let plan_json = serde_json::json!({
        "topic": topic,
        "depth": depth,
        "difficulty": difficulty,
        "plan": plan_result,
    });

    let plan_str = serde_json::to_string_pretty(&plan_json)?;

    let out_path = output.unwrap_or("series-plan.json");
    std::fs::write(out_path, &plan_str)
        .with_context(|| format!("Failed to write plan to {}", out_path))?;

    println!();
    println!("{}", "=".repeat(60).dimmed());
    println!("{}", " Series Plan Complete".bold());
    println!("{}", "=".repeat(60).dimmed());
    println!("  Topic:      {}", topic.cyan());
    println!("  Depth:      {} lessons", depth);
    println!("  Difficulty: {}", difficulty);
    println!("  Output:     {}", out_path.green());
    println!("  Cost:       ${:.4}", agent.total_cost());
    println!();
    println!("Next step:");
    println!(
        "  {}",
        format!("pah series generate --from {}", out_path).cyan()
    );
    println!();

    Ok(())
}

/// Generate lessons from an existing plan file. Reads from a file or stdin.
pub async fn cmd_generate(from: &str, budget: Option<f64>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    // Read plan JSON
    let plan_str = if from == "-" {
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input)
            .context("Failed to read plan from stdin")?;
        input
    } else {
        std::fs::read_to_string(from)
            .with_context(|| format!("Failed to read plan file: {}", from))?
    };

    let plan: serde_json::Value =
        serde_json::from_str(&plan_str).context("Failed to parse plan JSON")?;

    let base = if let Some(b) = budget {
        AgentOrchestrator::new(cfg.clone())?.with_budget(BudgetTracker::new(b))
    } else {
        AgentOrchestrator::new(cfg.clone())?
    };
    let mut agent = base.with_agent_id("series-agent");

    let series_result = agent.run_series_from_plan(&plan).await?;
    let result: serde_json::Value = serde_json::from_str(&series_result).unwrap_or_default();

    // Submit generated lessons and collect IDs
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let mut lesson_ids = Vec::new();

    if let Some(lessons) = result.get("lessons").and_then(|v| v.as_array()) {
        for lesson_val in lessons {
            let lesson_md = lesson_val
                .get("content")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            if lesson_md.is_empty() {
                continue;
            }

            let parsed = crate::commands::lesson::parse_lesson_frontmatter(lesson_md);

            let final_topic = parsed
                .topic
                .or_else(|| {
                    lesson_val
                        .get("topic")
                        .and_then(|v| v.as_str())
                        .map(String::from)
                })
                .unwrap_or_default();
            let final_difficulty = parsed
                .difficulty
                .or_else(|| {
                    lesson_val
                        .get("difficulty")
                        .and_then(|v| v.as_str())
                        .map(String::from)
                })
                .unwrap_or_default();

            let req = CreateLessonRequest {
                lesson_id: parsed.lesson_id.clone(),
                author_username: cfg.identity.username.clone(),
                title: parsed.title.clone(),
                topic: final_topic,
                difficulty: final_difficulty,
                description: String::new(),
                prerequisites: String::new(),
                conjecture_ids: parsed.conjecture_ids,
                published: true,
                content: lesson_md.to_string(),
                ai_annotations: vec![],
                references: parsed.references,
            };

            let lid = parsed.lesson_id.clone();
            print!("  Submitting lesson {}... ", lid);
            match client.create_lesson(&req).await {
                Ok(resp) => {
                    println!("{}", "OK".green());
                    println!("    Commit: {}", resp.commit_sha.dimmed());
                    lesson_ids.push(lid);
                }
                Err(e) => {
                    println!("{}", "FAILED".red());
                    eprintln!("    {}: {}", "Warning".yellow(), e);
                }
            }
        }
    }

    // Create the series itself
    if !lesson_ids.is_empty() {
        let topic = plan
            .get("topic")
            .and_then(|v| v.as_str())
            .unwrap_or("Untitled");
        let difficulty = plan
            .get("difficulty")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        let series_id = format!("series-{}", &uuid::Uuid::new_v4().to_string()[..8]);

        let req = CreateSeriesRequest {
            series_id: series_id.clone(),
            title: topic.to_string(),
            author_username: cfg.identity.username.clone(),
            difficulty: difficulty.to_string(),
            description: String::new(),
            lesson_ids: lesson_ids.clone(),
            published: true,
            content: String::new(),
        };

        print!("Submitting series to server... ");
        match client.create_series(&req).await {
            Ok(resp) => {
                println!("{}", "OK".green());
                println!("  Commit: {}", resp.commit_sha.cyan());
            }
            Err(e) => {
                println!("{}", "FAILED".red());
                eprintln!("{}: {}", "Warning".yellow(), e);
            }
        }

        println!();
        println!("{}", "=".repeat(60).dimmed());
        println!("{}", " Series Generated".bold());
        println!("{}", "=".repeat(60).dimmed());
        println!("  Series ID: {}", series_id.cyan());
        println!("  Lessons:   {}", lesson_ids.len());
        println!("  Cost:      ${:.4}", agent.total_cost());
        println!();

        for lid in &lesson_ids {
            println!("    {}", lid);
        }
        println!();
    } else {
        println!();
        println!(
            "{}: No lessons were generated or submitted.",
            "Warning".yellow()
        );
    }

    Ok(())
}

/// Audit an existing series for quality.
pub async fn cmd_audit(id: &str, output: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    // Fetch the series
    let series = client
        .fetch_series(id)
        .await
        .with_context(|| format!("Failed to fetch series '{}'", id))?;

    // Fetch all lessons
    let mut content_parts = Vec::new();
    content_parts.push(format!(
        "# Series: {}\n**ID:** {}\n**Difficulty:** {}\n**Lessons:** {}",
        series.title,
        series.series_id,
        series.difficulty,
        series.lesson_ids.len()
    ));

    for lid in &series.lesson_ids {
        match client.fetch_lesson(lid).await {
            Ok(lesson) => {
                content_parts.push(format!(
                    "\n## Lesson: {} — {}\n**Topic:** {}\n**Difficulty:** {}\n\n{}",
                    lid, lesson.title, lesson.topic, lesson.difficulty, lesson.content,
                ));
            }
            Err(e) => {
                eprintln!(
                    "{}: Could not fetch lesson {}: {}",
                    "Warning".yellow(),
                    lid,
                    e
                );
            }
        }
    }

    let series_content = content_parts.join("\n");

    let mut agent = AgentOrchestrator::new(cfg)?.with_agent_id("series-agent");
    let audit_report = agent.run_audit(&series_content).await?;

    if let Some(path) = output {
        std::fs::write(path, &audit_report)
            .with_context(|| format!("Failed to write audit report to {}", path))?;
        println!("  Written to: {}", path.green());
    } else {
        println!("{}", audit_report);
    }

    println!();
    println!("{}", "=".repeat(60).dimmed());
    println!("{}", " Audit Complete".bold());
    println!("{}", "=".repeat(60).dimmed());
    println!("  Series:  {}", id.cyan());
    println!("  Lessons: {}", series.lesson_ids.len());
    println!("  Cost:    ${:.4}", agent.total_cost());
    println!();

    Ok(())
}
