mod archive;
mod budget;
mod certifier;
mod commands;
mod config;
mod ipfs;
mod nft;
mod prover;
mod server_client;
mod signing;

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
    /// Interactive setup wizard (deprecated: register at the web UI instead)
    #[command(hide = true)]
    Init,
    /// Log in with your auth token from the web UI
    Login,
    /// Configure CLI settings (API key, server URL, prover)
    Setup,
    /// Set donation budget (legal agreement required)
    Donate,
    /// Start a proof contribution
    Prove,
    /// Show configuration and lifetime stats
    Status,
    /// Certify and compare proof packages from provers
    Certify {
        #[command(subcommand)]
        action: commands::certify::CertifyAction,
    },
    /// Submit a conjecture package (directory, tar.gz, or git URL)
    SubmitPackage {
        /// Path to directory, .tar.gz file, or git URL
        source: String,
    },
    /// Publish NFT metadata and archive to IPFS for on-chain minting
    Publish {
        /// Type: "contribution" or "certificate"
        kind: String,
        /// Contribution or certificate ID
        id: String,
    },
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Init => commands::init::run_init(),
        Commands::Login => commands::login::run_login().await,
        Commands::Setup => commands::setup::run_setup(),
        Commands::Donate => commands::donate::run_donate(),
        Commands::Prove => commands::run::run_prove().await,
        Commands::Status => commands::status::run_status(),
        Commands::Certify { action } => commands::certify::run_certify(action).await,
        Commands::SubmitPackage { source } => {
            commands::submit_package::run_submit_package(&source).await
        }
        Commands::Publish { kind, id } => commands::publish::run_publish(&kind, &id).await,
    };

    if let Err(e) = result {
        eprintln!("{}: {:#}", "Error".red(), e);
        std::process::exit(1);
    }
}

use colored::Colorize;
