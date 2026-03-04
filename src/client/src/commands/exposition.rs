use anyhow::{bail, Context, Result};
use colored::Colorize;

use crate::config::Config;
use crate::nft::metadata::{generate_exposition_nft_metadata, ExpositionInfo};
use crate::server_client::api::{ServerClient, SubmitExpositionRequest};
use crate::strategy_store::loader;

pub async fn cmd_create(
    for_id: &str,
    domain: Option<&str>,
    strategy_name: Option<&str>,
    output: Option<&str>,
    stdin: bool,
    method: &str,
) -> Result<()> {
    // Validate method
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

    // 1. Auto-detect resource type and fetch data
    let (resource_args, conjecture_id, contribution_id, prover, proof_script) =
        fetch_resource_context(&client, for_id).await?;

    // 2. Get exposition JSON — either from stdin or AI
    let (response_text, cost) = if stdin {
        // Pair prover mode: read pre-generated JSON from stdin
        let mut input = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut input)
            .context("Failed to read from stdin")?;
        (input.trim().to_string(), 0.0)
    } else if method == "manual" {
        bail!("Manual method requires --stdin to provide exposition JSON");
    } else {
        // API-assisted mode: call AI provider
        let strategy = select_strategy(strategy_name, domain)?;
        let vars = loader::ExpositionStrategyVars {
            resource_arguments: resource_args,
        };
        let prompt = loader::render_exposition_strategy(&strategy, &vars);

        println!("{}", "Generating exposition...".cyan());
        let provider = crate::ai::create_provider(&cfg)?;
        let model = cfg.model();
        let ai_response = provider.complete(&prompt, &model, 8192).await?;
        (ai_response.text.trim().to_string(), ai_response.cost_usd)
    };

    // 3. Generate HTML from response
    let default_name = format!("{}-exposition.html", for_id);
    let output_path = std::path::PathBuf::from(output.unwrap_or(&default_name));
    let viz_json_str = crate::conjecture_viz::build_from_response(&response_text, &output_path)?;

    // 4. Submit to server
    let expo_id = format!(
        "expo-{}-{}",
        for_id,
        uuid::Uuid::new_v4()
            .to_string()
            .split('-')
            .next()
            .unwrap_or("0000")
    );

    let strategy_used = if stdin {
        method.to_string()
    } else {
        strategy_name.unwrap_or("exposition-default").to_string()
    };

    // Extract title, domain, summary from the JSON response if present
    let viz_json: serde_json::Value = serde_json::from_str(&viz_json_str)
        .unwrap_or(serde_json::Value::Object(serde_json::Map::new()));
    let expo_title = viz_json
        .get("title")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let expo_summary = viz_json
        .get("summary")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();
    let expo_domain = viz_json
        .get("domain")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string();

    let submit_req = SubmitExpositionRequest {
        exposition_id: expo_id.clone(),
        author_username: cfg.identity.username.clone(),
        contribution_id: contribution_id.clone(),
        conjecture_id: conjecture_id.clone(),
        prover: prover.clone(),
        proof_script,
        exposition_text: viz_json_str,
        cost_usd: cost,
        strategy_used: strategy_used.clone(),
        domain: expo_domain,
        title: expo_title,
        summary: expo_summary,
    };

    print!("Submitting exposition to server... ");
    let commit_sha = match client.submit_exposition(&submit_req).await {
        Ok(resp) => {
            println!("{}", "OK".green());
            println!("  Commit: {}", resp.commit_sha.cyan());
            resp.commit_sha
        }
        Err(e) => {
            println!("{}", "FAILED".red());
            eprintln!("{}: Could not submit to server: {}", "Warning".yellow(), e);
            String::new()
        }
    };

    // 5. Sign and seal with NFT metadata
    if !commit_sha.is_empty() {
        let (public_key, commit_signature) = super::conjecture::sign_if_possible(&cfg, &commit_sha);

        let nft_info = ExpositionInfo {
            author_username: cfg.identity.username.clone(),
            exposition_id: expo_id.clone(),
            conjecture_id: conjecture_id.clone(),
            contribution_id,
            prover,
            cost_usd: cost,
            strategy_used: strategy_used.clone(),
            git_commit: commit_sha,
            git_repository: cfg.server_url(),
            public_key,
            commit_signature,
        };

        let nft_metadata = generate_exposition_nft_metadata(&nft_info);

        print!("Sealing exposition (creating PR)... ");
        match client.seal_exposition(&expo_id, &nft_metadata).await {
            Ok(seal_resp) => {
                println!("{}", "OK".green());
                if !seal_resp.pr_url.is_empty() {
                    println!("  PR: {}", seal_resp.pr_url.cyan());
                }
            }
            Err(e) => {
                println!("{}", "FAILED".red());
                eprintln!("{}: Could not seal on server: {}", "Warning".yellow(), e);
            }
        }
    }

    // 6. Print summary
    println!();
    println!("{}", "═".repeat(60).dimmed());
    println!("{}", " Exposition Generated".bold());
    println!("{}", "═".repeat(60).dimmed());
    println!();
    println!("  Output:   {}", output_path.display().to_string().green());
    println!("  Expo ID:  {}", expo_id.cyan());
    println!("  For:      {}", for_id);
    println!("  Method:   {}", method);
    println!("  Open in browser to view the mixed text+visual exposition.");
    println!();
    println!("{}", "─".repeat(60).dimmed());
    println!(
        "  Strategy: {}  |  Cost: ${:.4}",
        strategy_used.cyan(),
        cost,
    );
    println!("{}", "─".repeat(60).dimmed());

    Ok(())
}

pub async fn cmd_export(for_id: &str, domain: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    // Fetch resource context
    let (resource_args, _conjecture_id, _contribution_id, _prover, _proof_script) =
        fetch_resource_context(&client, for_id).await?;

    // Select strategy
    let strategy = select_strategy(None, domain)?;
    let vars = loader::ExpositionStrategyVars {
        resource_arguments: resource_args,
    };
    let prompt = loader::render_exposition_strategy(&strategy, &vars);

    // Print clean prompt to stdout (no spinners, suitable for piping)
    print!("{}", prompt);

    Ok(())
}

pub async fn cmd_list() -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let expositions = client.fetch_expositions().await?;

    if expositions.is_empty() {
        println!("No expositions found.");
        return Ok(());
    }

    println!(
        "{:<40} {:<20} {:<20} {:<10}",
        "Exposition ID", "Author", "Conjecture", "Cost"
    );
    println!("{}", "-".repeat(90));

    for e in &expositions {
        let display_id = if e.exposition_id.len() > 36 {
            &e.exposition_id[..36]
        } else {
            &e.exposition_id
        };
        println!(
            "{:<40} {:<20} {:<20} ${:<9.4}",
            display_id, e.author_username, e.conjecture_id, e.cost_usd,
        );
    }

    println!("\nTotal: {}", expositions.len());
    Ok(())
}

pub async fn cmd_get(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let e = client.fetch_exposition(id).await?;

    println!("{}", "=== Exposition ===".bold());
    println!("ID:           {}", e.exposition_id);
    println!("Author:       {}", e.author_username);
    println!("Conjecture:   {}", e.conjecture_id);
    println!("Contribution: {}", e.contribution_id);
    println!("Cost:         ${:.4}", e.cost_usd);
    println!("Strategy:     {}", e.strategy_used);

    Ok(())
}

// ── Helpers ──

/// Auto-detect resource type by prefix and fetch context.
/// Returns (resource_arguments, conjecture_id, contribution_id, prover, proof_script).
async fn fetch_resource_context(
    client: &ServerClient,
    for_id: &str,
) -> Result<(String, String, String, String, String)> {
    if for_id.starts_with("prob_") || for_id.starts_with("conj_") {
        // Conjecture
        let conjecture = client.fetch_conjecture(for_id).await?;
        let args = loader::build_resource_arguments_for_conjecture(&conjecture);
        Ok((
            args,
            for_id.to_string(),
            String::new(),
            conjecture.prover.clone(),
            String::new(),
        ))
    } else if for_id.starts_with("contrib_") {
        // Contribution
        let contribution = client.fetch_contribution(for_id).await?;
        let proofs = client.fetch_proofs(for_id).await.unwrap_or_default();
        let args = loader::build_resource_arguments_for_contribution(&contribution, &proofs);
        let prover = proofs
            .first()
            .map(|p| p.conjecture_id.clone())
            .unwrap_or_default();
        let proof_script = proofs
            .iter()
            .filter(|p| p.success)
            .map(|p| format!("(* {} *)\n{}", p.conjecture_id, p.proof_script))
            .collect::<Vec<_>>()
            .join("\n\n");
        Ok((
            args,
            String::new(),
            for_id.to_string(),
            prover,
            proof_script,
        ))
    } else if for_id.starts_with("cert_") {
        // Certificate — fetch as contribution review context
        let args = format!(
            "**Resource type:** Certificate\n**Certificate ID:** {}",
            for_id
        );
        Ok((
            args,
            String::new(),
            String::new(),
            String::new(),
            String::new(),
        ))
    } else {
        // Try conjecture first, then contribution
        if let Ok(conjecture) = client.fetch_conjecture(for_id).await {
            let args = loader::build_resource_arguments_for_conjecture(&conjecture);
            return Ok((
                args,
                for_id.to_string(),
                String::new(),
                conjecture.prover.clone(),
                String::new(),
            ));
        }
        if let Ok(contribution) = client.fetch_contribution(for_id).await {
            let proofs = client.fetch_proofs(for_id).await.unwrap_or_default();
            let args = loader::build_resource_arguments_for_contribution(&contribution, &proofs);
            return Ok((
                args,
                String::new(),
                for_id.to_string(),
                String::new(),
                String::new(),
            ));
        }
        bail!(
            "Could not find resource '{}'. Use a prefix to specify type: prob_*, contrib_*, cert_*",
            for_id
        );
    }
}

/// Select the appropriate exposition strategy.
fn select_strategy(
    strategy_name: Option<&str>,
    domain: Option<&str>,
) -> Result<loader::LoadedStrategy> {
    if let Some(name) = strategy_name {
        loader::load_strategy(name)
    } else {
        let kind = match domain {
            Some(d) => format!("exposition-{}", d),
            None => "exposition".to_string(),
        };
        loader::auto_select_by_kind(&kind).with_context(|| {
            format!(
                "No exposition strategy found for kind '{}'. Try omitting --domain or use --by to specify a strategy.",
                kind
            )
        })
    }
}
