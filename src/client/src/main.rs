mod archive;
mod budget;
mod certifier;
mod commands;
mod commands_store;
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
    Setup {
        /// Import command files from paths, directories, .tar.gz, or GitHub URLs
        #[arg(long = "add-commands")]
        add_commands: Vec<String>,
    },
    /// Set donation budget (legal agreement required)
    Donate,
    /// Prove conjectures or re-seal contributions
    Prove {
        #[command(subcommand)]
        action: Option<ProveAction>,
        /// Use a specific proving strategy command (by name)
        #[arg(long = "by", global = true)]
        by: Option<String>,
    },
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

#[derive(Subcommand)]
enum ProveAction {
    /// Start a proof contribution (default when no subcommand given)
    Run {
        /// Use a specific proving strategy command (by name)
        #[arg(long = "by")]
        by: Option<String>,
    },
    /// Re-seal an existing proof contribution (regenerate archive, signature, NFT metadata)
    Seal {
        /// Contribution ID to re-seal
        contribution_id: String,
    },
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Init => commands::init::run_init(),
        Commands::Login => commands::login::run_login().await,
        Commands::Setup { add_commands } => commands::setup::run_setup(add_commands),
        Commands::Donate => commands::donate::run_donate(),
        Commands::Prove { action, by } => match action {
            Some(ProveAction::Run { by: run_by }) => {
                commands::run::run_prove(run_by.as_deref().or(by.as_deref())).await
            }
            Some(ProveAction::Seal { contribution_id }) => {
                commands::run::run_prove_seal(&contribution_id).await
            }
            // Default: `prove` with no subcommand runs the proof contribution
            None => commands::run::run_prove(by.as_deref()).await,
        },
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
