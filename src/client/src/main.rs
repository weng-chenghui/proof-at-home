mod archive;
mod budget;
mod commands;
mod config;
mod nft;
mod prover;
mod reviewer;
mod server_client;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(
    name = "proof-at-home",
    about = "Donate unused Claude budget to prove mathematical lemmas",
    version
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Interactive setup wizard
    Init,
    /// Set donation budget (legal agreement required)
    Donate,
    /// Start a proof-mining session
    Run,
    /// Show configuration and lifetime stats
    Status,
    /// Review and compare proof packages from provers
    Review {
        #[command(subcommand)]
        action: commands::review::ReviewAction,
    },
    /// Submit a problem package (directory, tar.gz, or git URL)
    SubmitPackage {
        /// Path to directory, .tar.gz file, or git URL
        source: String,
    },
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Init => commands::init::run_init(),
        Commands::Donate => commands::donate::run_donate(),
        Commands::Run => commands::run::run_session().await,
        Commands::Status => commands::status::run_status(),
        Commands::Review { action } => commands::review::run_review(action).await,
        Commands::SubmitPackage { source } => {
            commands::submit_package::run_submit_package(&source).await
        }
    };

    if let Err(e) = result {
        eprintln!("{}: {:#}", "Error".red(), e);
        std::process::exit(1);
    }
}

use colored::Colorize;
