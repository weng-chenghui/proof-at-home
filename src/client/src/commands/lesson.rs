use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::collections::HashMap;

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
    let parsed = parse_lesson_frontmatter(&lesson_md);

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
        content: lesson_md.clone(),
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
            eprintln!("{}: Could not submit to server: {}", "Warning".yellow(), e);
        }
    }

    let lesson_id = parsed.lesson_id;
    let title = parsed.title;

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

pub async fn cmd_notes_list(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let notes = client.fetch_notes(id).await?;

    if notes.is_empty() {
        println!("No notes found for lesson {}.", id);
        return Ok(());
    }

    println!(
        "{:<38} {:<30} {:<12} {:<10} {:<8}",
        "Note ID", "Anchor Text", "Author", "Status", "Color"
    );
    println!("{}", "\u{2500}".repeat(98));

    for n in &notes {
        let anchor = if n.anchor_text.len() > 28 {
            format!("{}...", &n.anchor_text[..25])
        } else {
            n.anchor_text.clone()
        };
        println!(
            "{:<38} {:<30} {:<12} {:<10} {:<8}",
            n.note_id, anchor, n.username, n.status, n.highlight_color,
        );
    }

    println!("\nTotal: {}", notes.len());
    Ok(())
}

pub async fn cmd_notes_revise(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let lesson = client.fetch_lesson(id).await?;
    let notes = client.fetch_notes(id).await?;

    if notes.is_empty() {
        println!("No notes found for lesson {}. Nothing to revise.", id);
        return Ok(());
    }

    // Build prompt
    let mut notes_text = String::new();
    for n in &notes {
        notes_text.push_str(&format!(
            "- [{}] \"{}\" \u{2192} {}\n",
            n.highlight_color, n.anchor_text, n.content
        ));
    }

    let prompt = format!(
        "Here is lesson content:\n\n{}\n\nUser notes and highlights:\n{}\n\nBased on these notes, suggest specific revisions to improve the lesson. For each suggestion, reference the relevant section and explain the improvement.",
        lesson.content, notes_text
    );

    let has_api_key = !cfg.api_key().is_empty();
    if !has_api_key {
        eprintln!(
            "{}: No AI provider configured. Printing prompt instead.",
            "Info".cyan()
        );
        println!("{}", prompt);
        return Ok(());
    }

    println!("{}", "Generating revision suggestions...".cyan());
    let provider = crate::ai::create_provider(&cfg)?;
    let model = cfg.model();
    let response = provider.complete(&prompt, &model, 8192).await?;
    println!("{}", response.text);
    println!("\nCost: ${:.4}", response.cost_usd);

    Ok(())
}

pub async fn cmd_notes_merge(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let lesson = client.fetch_lesson(id).await?;
    let notes = client.fetch_notes(id).await?;

    if notes.is_empty() {
        println!("No notes found for lesson {}. Nothing to merge.", id);
        return Ok(());
    }

    // Build prompt
    let mut notes_text = String::new();
    for n in &notes {
        notes_text.push_str(&format!(
            "- [{}] \"{}\" \u{2192} {}\n",
            n.highlight_color, n.anchor_text, n.content
        ));
    }

    let prompt = format!(
        "Here is lesson content:\n\n{}\n\nUser notes and highlights:\n{}\n\nMerge these notes into the lesson content. Output the complete revised lesson content in the same format (with YAML frontmatter). Incorporate the feedback naturally into the text.",
        lesson.content, notes_text
    );

    let has_api_key = !cfg.api_key().is_empty();
    if !has_api_key {
        eprintln!(
            "{}: No AI provider configured. Printing prompt instead.",
            "Info".cyan()
        );
        println!("{}", prompt);
        return Ok(());
    }

    println!("{}", "Merging notes into lesson content...".cyan());
    let provider = crate::ai::create_provider(&cfg)?;
    let model = cfg.model();
    let response = provider.complete(&prompt, &model, 16384).await?;

    println!("{}", response.text);
    println!("\nCost: ${:.4}", response.cost_usd);

    // Mark merged notes as 'merged'
    for n in &notes {
        if let Err(e) = client.update_note_status(&n.note_id, "merged").await {
            eprintln!(
                "{}: Could not mark note {} as merged: {}",
                "Warning".yellow(),
                n.note_id,
                e
            );
        }
    }
    println!(
        "{} {} notes marked as merged.",
        "\u{2713}".green(),
        notes.len()
    );

    Ok(())
}

/// Parsed lesson frontmatter fields.
pub struct ParsedLessonFrontmatter {
    pub lesson_id: String,
    pub title: String,
    pub topic: Option<String>,
    pub difficulty: Option<String>,
    pub conjecture_ids: Vec<String>,
    pub references: Vec<serde_json::Value>,
}

/// Parse YAML frontmatter from lesson.md to extract key fields.
/// Uses serde_yaml for full nested structure support (references, etc.).
pub fn parse_lesson_frontmatter(content: &str) -> ParsedLessonFrontmatter {
    let default = || ParsedLessonFrontmatter {
        lesson_id: format!("lesson-{}", &uuid::Uuid::new_v4().to_string()[..8]),
        title: "Untitled Lesson".to_string(),
        topic: None,
        difficulty: None,
        conjecture_ids: vec![],
        references: vec![],
    };

    if !content.starts_with("---") {
        return default();
    }

    let rest = &content[3..];
    let end_idx = match rest.find("\n---") {
        Some(idx) => idx,
        None => return default(),
    };
    let frontmatter = &rest[..end_idx];

    // Parse with serde_yaml into a generic map
    let map: HashMap<String, serde_yaml::Value> = match serde_yaml::from_str(frontmatter) {
        Ok(m) => m,
        Err(_) => return default(),
    };

    let get_str = |key: &str| -> Option<String> {
        map.get(key).and_then(|v| match v {
            serde_yaml::Value::String(s) => Some(s.clone()),
            _ => None,
        })
    };

    let lesson_id = get_str("lesson_id")
        .unwrap_or_else(|| format!("lesson-{}", &uuid::Uuid::new_v4().to_string()[..8]));
    let title = get_str("title").unwrap_or_else(|| "Untitled Lesson".to_string());
    let topic = get_str("topic");
    let difficulty = get_str("difficulty");

    let conjecture_ids = map
        .get("conjecture_ids")
        .and_then(|v| match v {
            serde_yaml::Value::Sequence(seq) => Some(
                seq.iter()
                    .filter_map(|item| match item {
                        serde_yaml::Value::String(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default();

    // Parse references as generic JSON values (CSL-JSON compatible)
    let references = map
        .get("references")
        .and_then(|v| {
            // Convert serde_yaml::Value -> serde_json::Value via serialization round-trip
            let json_str = serde_json::to_string(
                &serde_yaml::from_value::<serde_json::Value>(v.clone()).ok()?,
            )
            .ok()?;
            serde_json::from_str::<Vec<serde_json::Value>>(&json_str).ok()
        })
        .unwrap_or_default();

    ParsedLessonFrontmatter {
        lesson_id,
        title,
        topic,
        difficulty,
        conjecture_ids,
        references,
    }
}
