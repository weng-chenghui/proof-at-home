use anyhow::{bail, Context, Result};
use colored::Colorize;

use crate::config::Config;
use crate::server_client::api::{CreateLessonRequest, ServerClient};
use crate::strategy_store::loader;

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load_or_default();
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let lessons = client.fetch_lessons().await?;

    if lessons.is_empty() {
        println!("No lessons found.");
        return Ok(());
    }

    println!(
        "{:<30} {:<40} {:<15} {:<10}",
        "Lesson ID", "Title", "Topic", "Difficulty"
    );
    println!("{}", "-".repeat(95));

    for l in &lessons {
        let title = if l.title.len() > 38 {
            format!("{}...", &l.title[..35])
        } else {
            l.title.clone()
        };
        println!(
            "{:<30} {:<40} {:<15} {:<10}",
            l.lesson_id, title, l.topic, l.difficulty,
        );
    }

    println!("\nTotal: {}", lessons.len());
    Ok(())
}

pub async fn cmd_get(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let l = client.fetch_lesson(id).await?;

    println!("{}", "=== Lesson ===".bold());
    println!("ID:            {}", l.lesson_id);
    println!("Title:         {}", l.title);
    println!("Author:        {}", l.author_username);
    println!("Topic:         {}", l.topic);
    println!("Difficulty:    {}", l.difficulty);
    println!("Published:     {}", l.published);
    println!("Conjectures:   {}", l.conjecture_ids.join(", "));

    if !l.description.is_empty() {
        println!("Description:   {}", l.description);
    }

    if !l.content.is_empty() {
        println!();
        println!("{}", "─".repeat(60).dimmed());
        println!("{}", l.content);
    }

    Ok(())
}

pub async fn cmd_create(
    topic: Option<&str>,
    conjectures: Option<&str>,
    difficulty: Option<&str>,
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

    // Parse conjecture IDs
    let conjecture_ids: Vec<String> = conjectures
        .map(|c| c.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    // Get lesson content — either from stdin or AI
    let (lesson_md, cost) = if stdin {
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input)
            .context("Failed to read from stdin")?;
        (input.trim().to_string(), 0.0)
    } else if method == "manual" {
        bail!("Manual method requires --stdin to provide lesson.md content");
    } else {
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

            // Fetch each conjecture for context
            for cid in &conjecture_ids {
                match client.fetch_conjecture(cid).await {
                    Ok(conj) => {
                        let args = loader::build_resource_arguments_for_conjecture(&conj);
                        resource_parts.push(format!("\n### Conjecture: {}\n{}", cid, args));
                    }
                    Err(e) => {
                        eprintln!(
                            "{}: Could not fetch conjecture {}: {}",
                            "Warning".yellow(),
                            cid,
                            e
                        );
                    }
                }
            }
        }

        let resource_args = resource_parts.join("\n");

        // Check for API key
        let has_api_key = !cfg.api_key().is_empty();

        if !has_api_key {
            // Auto-fallback to export mode
            eprintln!(
                "{}: No AI provider configured. Exporting prompt instead.",
                "Info".cyan()
            );
            eprintln!("Paste the output into Claude, then pipe the result back:");
            eprintln!(
                "  cat lesson.md | pah lesson create --stdin --method pair-proved --conjectures {}",
                conjecture_ids.join(",")
            );
            eprintln!();

            let strategy = loader::auto_select_by_kind("lesson")
                .unwrap_or_else(|_| loader::load_strategy("compose-lesson").unwrap());
            let vars = loader::LessonStrategyVars {
                resource_arguments: resource_args,
            };
            let prompt = loader::render_lesson_strategy(&strategy, &vars);
            print!("{}", prompt);
            return Ok(());
        }

        let strategy = loader::auto_select_by_kind("lesson")
            .unwrap_or_else(|_| loader::load_strategy("compose-lesson").unwrap());
        let vars = loader::LessonStrategyVars {
            resource_arguments: resource_args,
        };
        let prompt = loader::render_lesson_strategy(&strategy, &vars);

        println!("{}", "Generating lesson...".cyan());
        let provider = crate::ai::create_provider(&cfg)?;
        let model = cfg.model();
        let ai_response = provider.complete(&prompt, &model, 16384).await?;
        (ai_response.text.trim().to_string(), ai_response.cost_usd)
    };

    // Write to output file if requested
    if let Some(path) = output {
        std::fs::write(path, &lesson_md).with_context(|| format!("Failed to write to {}", path))?;
        println!("  Written to: {}", path.green());
    }

    // Parse the lesson.md to extract metadata
    let (lesson_id, title, parsed_topic, parsed_difficulty, parsed_conjecture_ids) =
        parse_lesson_frontmatter(&lesson_md);

    let final_topic = parsed_topic
        .or_else(|| topic.map(|s| s.to_string()))
        .unwrap_or_default();
    let final_difficulty = parsed_difficulty
        .or_else(|| difficulty.map(|s| s.to_string()))
        .unwrap_or_default();
    let final_conjecture_ids = if parsed_conjecture_ids.is_empty() {
        conjecture_ids
    } else {
        parsed_conjecture_ids
    };

    let req = CreateLessonRequest {
        lesson_id: lesson_id.clone(),
        author_username: cfg.identity.username.clone(),
        title: title.clone(),
        topic: final_topic,
        difficulty: final_difficulty,
        description: String::new(),
        prerequisites: String::new(),
        conjecture_ids: final_conjecture_ids,
        published: true,
        content: lesson_md.clone(),
        ai_annotations: vec![],
    };

    print!("Submitting lesson to server... ");
    match client.create_lesson(&req).await {
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
    println!("{}", " Lesson Created".bold());
    println!("{}", "=".repeat(60).dimmed());
    println!();
    println!("  Lesson ID: {}", lesson_id.cyan());
    println!("  Title:     {}", title);
    println!("  Method:    {}", method);
    println!("  Cost:      ${:.4}", cost);
    println!();

    Ok(())
}

pub async fn cmd_export(conjectures: Option<&str>, topic: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let conjecture_ids: Vec<String> = conjectures
        .map(|c| c.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();

    let mut resource_parts = Vec::new();
    resource_parts.push(format!(
        "**Topic:** {}",
        topic.unwrap_or("general mathematics")
    ));

    if !conjecture_ids.is_empty() {
        resource_parts.push(format!("**Conjecture IDs:** {}", conjecture_ids.join(", ")));

        for cid in &conjecture_ids {
            if let Ok(conj) = client.fetch_conjecture(cid).await {
                let args = loader::build_resource_arguments_for_conjecture(&conj);
                resource_parts.push(format!("\n### Conjecture: {}\n{}", cid, args));
            }
        }
    }

    let resource_args = resource_parts.join("\n");

    let strategy = loader::auto_select_by_kind("lesson")
        .unwrap_or_else(|_| loader::load_strategy("compose-lesson").unwrap());
    let vars = loader::LessonStrategyVars {
        resource_arguments: resource_args,
    };
    let prompt = loader::render_lesson_strategy(&strategy, &vars);
    print!("{}", prompt);

    Ok(())
}

/// Parse YAML frontmatter from lesson.md to extract key fields.
/// Simple parser — doesn't require a YAML library.
fn parse_lesson_frontmatter(
    content: &str,
) -> (String, String, Option<String>, Option<String>, Vec<String>) {
    let mut lesson_id = String::new();
    let mut title = String::new();
    let mut topic = None;
    let mut difficulty = None;
    let mut conjecture_ids = Vec::new();

    if !content.starts_with("---") {
        // No frontmatter — generate an ID
        return (
            format!("lesson-{}", &uuid::Uuid::new_v4().to_string()[..8]),
            "Untitled Lesson".to_string(),
            None,
            None,
            vec![],
        );
    }

    let rest = &content[3..];
    let end = rest.find("\n---");
    if let Some(end_idx) = end {
        let frontmatter = &rest[..end_idx];
        for line in frontmatter.lines() {
            let line = line.trim();
            if let Some(val) = line.strip_prefix("lesson_id:") {
                lesson_id = val.trim().trim_matches('"').to_string();
            } else if let Some(val) = line.strip_prefix("title:") {
                title = val.trim().trim_matches('"').to_string();
            } else if let Some(val) = line.strip_prefix("topic:") {
                topic = Some(val.trim().trim_matches('"').to_string());
            } else if let Some(val) = line.strip_prefix("difficulty:") {
                difficulty = Some(val.trim().trim_matches('"').to_string());
            } else if let Some(val) = line.strip_prefix("conjecture_ids:") {
                // Parse inline array: [id1, id2]
                let val = val.trim();
                if val.starts_with('[') {
                    let inner = val.trim_start_matches('[').trim_end_matches(']');
                    conjecture_ids = inner
                        .split(',')
                        .map(|s| s.trim().trim_matches('"').to_string())
                        .filter(|s| !s.is_empty())
                        .collect();
                }
            } else if line.starts_with("- ") && conjecture_ids.is_empty() && lesson_id.is_empty() {
                // YAML list item under conjecture_ids
                // Skip — we handle inline arrays above
            }
        }
    }

    if lesson_id.is_empty() {
        lesson_id = format!("lesson-{}", &uuid::Uuid::new_v4().to_string()[..8]);
    }
    if title.is_empty() {
        title = "Untitled Lesson".to_string();
    }

    (lesson_id, title, topic, difficulty, conjecture_ids)
}
