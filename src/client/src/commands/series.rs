use anyhow::{bail, Context, Result};
use colored::Colorize;

use crate::config::Config;
use crate::server_client::api::{CreateSeriesRequest, ServerClient};
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
