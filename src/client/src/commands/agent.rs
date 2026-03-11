use anyhow::Result;
use colored::Colorize;

use crate::agent::orchestrator::AgentOrchestrator;
use crate::config::Config;
use crate::server_client::api::{CreateLessonRequest, ServerClient};

pub async fn cmd_run_lesson(
    topic: Option<&str>,
    conjectures: Option<&str>,
    difficulty: Option<&str>,
    output: Option<&str>,
) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;

    let conjecture_ids: Vec<String> = conjectures
        .map(|c| c.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let mut agent = AgentOrchestrator::new(cfg.clone())?;
    let lesson_md = agent.run_lesson(topic, &conjecture_ids, difficulty).await?;

    // Write to output file if requested
    if let Some(path) = output {
        std::fs::write(path, &lesson_md)?;
        println!("Written to: {}", path.green());
    }

    // Parse and submit
    let parsed = crate::commands::lesson::parse_lesson_frontmatter(&lesson_md);

    let final_topic = parsed
        .topic
        .or_else(|| topic.map(|s| s.to_string()))
        .unwrap_or_default();
    let final_difficulty = parsed
        .difficulty
        .or_else(|| difficulty.map(|s| s.to_string()))
        .unwrap_or_default();
    let final_conjecture_ids = if parsed.conjecture_ids.is_empty() {
        conjecture_ids
    } else {
        parsed.conjecture_ids
    };

    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let req = CreateLessonRequest {
        lesson_id: parsed.lesson_id.clone(),
        author_username: cfg.identity.username.clone(),
        title: parsed.title.clone(),
        topic: final_topic,
        difficulty: final_difficulty,
        description: String::new(),
        prerequisites: String::new(),
        conjecture_ids: final_conjecture_ids,
        published: true,
        content: lesson_md,
        ai_annotations: vec![],
        references: parsed.references,
    };

    print!("Submitting lesson to server... ");
    match client.create_lesson(&req).await {
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
    println!("{}", " Agent Run Complete".bold());
    println!("{}", "=".repeat(60).dimmed());
    println!("  Run ID:    {}", agent.run_id());
    println!("  Lesson:    {}", req.lesson_id.cyan());
    println!("  Title:     {}", req.title);
    println!("  Steps:     {}", agent.steps().len());
    println!("  Cost:      ${:.4}", agent.total_cost());
    println!();

    for step in agent.steps() {
        println!(
            "    {:<20} ${:.4}  ({}+{} tokens)",
            step.name, step.cost_usd, step.input_tokens, step.output_tokens,
        );
    }

    Ok(())
}

pub fn cmd_status(run_id: Option<&str>) -> Result<()> {
    // For now, just show that status tracking is per-session
    println!("Agent status tracking is session-based.");
    if let Some(id) = run_id {
        println!("Run ID: {}", id);
    }
    println!("Use `pah agent run lesson` to start a new run.");
    Ok(())
}
