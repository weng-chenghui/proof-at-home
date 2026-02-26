use anyhow::Result;
use colored::Colorize;

use crate::config::Config;
use crate::server_client::api::ServerClient;

pub async fn cmd_list(contribution_id: &str) -> Result<()> {
    let cfg = Config::load()?;
    let client = ServerClient::new(&cfg.api.server_url, &cfg.api.auth_token);
    let proofs = client.fetch_proofs(contribution_id).await?;

    if proofs.is_empty() {
        println!("No proofs found for contribution {}.", contribution_id);
        return Ok(());
    }

    println!(
        "{:<40} {:<20} {:<10} {:<10} {:<10}",
        "Conjecture ID", "Username", "Success", "Attempts", "Cost"
    );
    println!("{}", "-".repeat(90));

    for p in &proofs {
        let display_id = if p.conjecture_id.len() > 36 {
            &p.conjecture_id[..36]
        } else {
            &p.conjecture_id
        };
        let success_str = if p.success {
            "✓".green().to_string()
        } else {
            "✗".red().to_string()
        };
        println!(
            "{:<40} {:<20} {:<10} {:<10} ${:<9.4}",
            display_id, p.username, success_str, p.attempts, p.cost_usd
        );
    }

    println!("\nTotal: {}", proofs.len());
    Ok(())
}
