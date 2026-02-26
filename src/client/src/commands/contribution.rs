use anyhow::Result;
use colored::Colorize;

use crate::config::Config;
use crate::server_client::api::ServerClient;

pub async fn cmd_list(status: Option<&str>) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let contributions = client.fetch_contributions().await?;

    let filtered: Vec<_> = if let Some(s) = status {
        contributions
            .iter()
            .filter(|c| c.proof_status == s)
            .collect()
    } else {
        contributions.iter().collect()
    };

    if filtered.is_empty() {
        println!("No contributions found.");
        return Ok(());
    }

    println!(
        "{:<40} {:<20} {:<8} {:<8} {:<10} {:<10}",
        "ID", "Username", "Proved", "Total", "Cost", "Status"
    );
    println!("{}", "-".repeat(96));

    for c in &filtered {
        let display_id = if c.contribution_id.len() > 36 {
            &c.contribution_id[..36]
        } else {
            &c.contribution_id
        };
        println!(
            "{:<40} {:<20} {:<8} {:<8} ${:<9.4} {:<10}",
            display_id,
            c.username,
            c.conjectures_proved,
            c.conjectures_attempted,
            c.total_cost_usd,
            c.proof_status
        );
    }

    println!("\nTotal: {}", filtered.len());
    Ok(())
}

pub async fn cmd_get(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);
    let c = client.fetch_contribution(id).await?;

    println!("{}", "=== Contribution ===".bold());
    println!("ID:        {}", c.contribution_id);
    println!("Username:  {}", c.username);
    println!(
        "Proved:    {}/{}",
        c.conjectures_proved, c.conjectures_attempted
    );
    println!("Cost:      ${:.4}", c.total_cost_usd);
    println!("Status:    {}", c.proof_status);

    Ok(())
}

pub async fn cmd_archive(id: &str) -> Result<()> {
    let cfg = Config::load_or_default();
    cfg.require_login()?;
    let client = ServerClient::new(&cfg.server_url(), &cfg.api.auth_token);

    let dest = std::path::PathBuf::from(format!("{}.tar.gz", id));
    print!("Downloading archive... ");
    client.download_package(id, &dest).await?;
    println!("{}", "OK".green());
    println!("Saved to: {}", dest.display());

    Ok(())
}
