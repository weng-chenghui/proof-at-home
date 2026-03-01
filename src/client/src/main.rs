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
mod strategy_store;

use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "pah",
    about = "Proof@Home — donate spare AI budget to prove mathematical theorems.\nProofs are compiler-verified, git-archived, and permanently credited to you.",
    version
)]
struct Cli {
    #[command(subcommand)]
    resource: Resource,
}

#[derive(Subcommand)]
enum Resource {
    /// Manage conjectures (list, get, create, seal)
    Conjecture {
        #[command(subcommand)]
        action: ConjectureAction,
    },
    /// Manage contributions (list, get, run, seal, publish, archive).
    /// Typical workflow: run → get → publish
    Contribution {
        #[command(subcommand)]
        action: ContributionAction,
    },
    /// View proofs or submit hand-written proofs
    Proof {
        #[command(subcommand)]
        action: ProofAction,
    },
    /// Manage certificates (list, create, import, compare, report, seal, publish).
    /// Typical workflow: create → import → compare → report → seal → publish
    Certificate {
        #[command(subcommand)]
        action: CertificateAction,
    },
    /// Manage proving strategies (list, get, import)
    Strategy {
        #[command(subcommand)]
        action: StrategyAction,
    },
    /// View or change CLI settings (get, set)
    Setting {
        #[command(subcommand)]
        action: SettingAction,
    },
    /// Authentication (login, status, logout)
    Auth {
        #[command(subcommand)]
        action: AuthAction,
    },
}

// ── Conjecture ──

#[derive(Subcommand)]
enum ConjectureAction {
    /// List all conjectures
    List,
    /// Get details for a specific conjecture
    Get {
        /// Conjecture ID
        id: String,
    },
    /// Create conjectures from a directory, .tar.gz, or git URL
    Create {
        /// Path to directory, .tar.gz file, or git URL
        source: String,
    },
    /// Seal a conjecture batch with NFT metadata
    Seal {
        /// Batch ID to seal
        batch_id: String,
    },
    /// Generate conjectures from Lean sources using LeanConjecturer
    /// (https://github.com/auto-res/LeanConjecturer by auto-res, MIT license)
    Generate {
        /// Path to a Lean source file or directory
        source: String,
        /// Path to LeanConjecturer executable (default: searches PATH)
        #[arg(long)]
        bin: Option<String>,
        /// Extra arguments passed through to LeanConjecturer
        #[arg(long, num_args = 1..)]
        args: Vec<String>,
        /// Difficulty tag for generated conjectures
        #[arg(long, default_value = "auto")]
        difficulty: String,
        /// Only write converted JSON files, do not submit
        #[arg(long)]
        dry_run: bool,
        /// Output directory for converted files (default: temp dir)
        #[arg(long)]
        output_dir: Option<String>,
    },
    /// Import LeanConjecturer grpo_problem.jsonl as conjectures
    /// (https://github.com/auto-res/LeanConjecturer by auto-res, MIT license)
    Import {
        /// Path to grpo_problem.jsonl
        jsonl_path: String,
        /// Difficulty tag
        #[arg(long, default_value = "auto")]
        difficulty: String,
        /// Only write converted JSON files, do not submit
        #[arg(long)]
        dry_run: bool,
        /// Output directory for converted files (default: temp dir)
        #[arg(long)]
        output_dir: Option<String>,
    },
}

// ── Contribution ──

#[derive(Subcommand)]
enum ContributionAction {
    /// List contributions
    List {
        /// Filter by status (e.g. proved, incomplete, unproved)
        #[arg(long)]
        status: Option<String>,
    },
    /// Get details for a specific contribution
    Get {
        /// Contribution ID
        id: String,
    },
    /// Start an AI-assisted proof contribution
    Run {
        /// Use a specific proving strategy (by name)
        #[arg(long = "by")]
        by: Option<String>,
    },
    /// Re-seal an existing contribution (regenerate archive, signature, NFT metadata)
    Seal {
        /// Contribution ID to re-seal
        id: String,
    },
    /// Publish a contribution to IPFS and generate mint script
    Publish {
        /// Contribution ID
        id: String,
    },
    /// Download the proof archive for a contribution
    Archive {
        /// Contribution ID
        id: String,
    },
}

// ── Proof ──

#[derive(Subcommand)]
enum ProofAction {
    /// List proofs for a contribution
    List {
        /// Contribution ID
        #[arg(long)]
        contribution: String,
    },
    /// Submit hand-written proofs for verification and sealing
    Submit {
        /// Conjecture ID (single-file mode)
        conjecture_id: Option<String>,
        /// Path to proof file (single-file mode)
        proof_file: Option<String>,
        /// Directory of proof files named <conjecture-id>.v or .lean (batch mode)
        #[arg(long = "dir")]
        dir: Option<String>,
    },
}

// ── Certificate ──

#[derive(Subcommand)]
enum CertificateAction {
    /// List certificates from the server
    List,
    /// Start a new certification session (fetch packages from server)
    Create,
    /// Import a local proof archive into the active certification session
    Import {
        /// Path to a proof archive (.tar.gz)
        path: PathBuf,
    },
    /// AI-compare proofs across packages
    Compare {
        /// Use a specific comparison strategy (by name)
        #[arg(long = "by")]
        by: Option<String>,
    },
    /// Generate or validate a certification report
    Report {
        /// Template variant: default, minimal, detailed
        #[arg(long, default_value = "default")]
        template: String,
    },
    /// Seal certification package with NFT metadata
    Seal,
    /// Publish a certificate to IPFS and generate mint script
    Publish {
        /// Certificate ID
        id: String,
    },
}

// ── Strategy ──

#[derive(Subcommand)]
enum StrategyAction {
    /// List strategies from the server
    List,
    /// Get details for a specific strategy
    Get {
        /// Strategy name
        name: String,
    },
    /// Import strategy files from paths, directories, .tar.gz, or GitHub URLs
    Import {
        /// Paths to import
        paths: Vec<String>,
    },
}

// ── Setting ──

#[derive(Subcommand)]
enum SettingAction {
    /// Show settings (all or a specific key)
    Get {
        /// Setting key (omit for full status)
        key: Option<String>,
    },
    /// Set a setting value (no args for interactive wizard)
    Set {
        /// Setting key (use 'budget' for donation wizard)
        key: Option<String>,
        /// New value
        value: Option<String>,
    },
}

// ── Auth ──

#[derive(Subcommand)]
enum AuthAction {
    /// Log in with your auth token from the web UI
    Login,
    /// Show current auth status
    Status,
    /// Clear saved auth token
    Logout,
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    let result = match cli.resource {
        Resource::Conjecture { action } => match action {
            ConjectureAction::List => commands::conjecture::cmd_list().await,
            ConjectureAction::Get { id } => commands::conjecture::cmd_get(&id).await,
            ConjectureAction::Create { source } => commands::conjecture::cmd_create(&source).await,
            ConjectureAction::Seal { batch_id } => commands::conjecture::cmd_seal(&batch_id).await,
            ConjectureAction::Generate {
                source,
                bin,
                args,
                difficulty,
                dry_run,
                output_dir,
            } => {
                commands::conjecture::cmd_generate(
                    &source,
                    bin.as_deref(),
                    &args,
                    &difficulty,
                    dry_run,
                    output_dir.as_deref(),
                )
                .await
            }
            ConjectureAction::Import {
                jsonl_path,
                difficulty,
                dry_run,
                output_dir,
            } => {
                commands::conjecture::cmd_import(
                    &jsonl_path,
                    &difficulty,
                    dry_run,
                    output_dir.as_deref(),
                )
                .await
            }
        },
        Resource::Contribution { action } => match action {
            ContributionAction::List { status } => {
                commands::contribution::cmd_list(status.as_deref()).await
            }
            ContributionAction::Get { id } => commands::contribution::cmd_get(&id).await,
            ContributionAction::Run { by } => commands::run::run_prove(by.as_deref()).await,
            ContributionAction::Seal { id } => commands::run::run_prove_seal(&id).await,
            ContributionAction::Publish { id } => {
                commands::publish::run_publish("contribution", &id).await
            }
            ContributionAction::Archive { id } => commands::contribution::cmd_archive(&id).await,
        },
        Resource::Proof { action } => match action {
            ProofAction::List { contribution } => commands::proof::cmd_list(&contribution).await,
            ProofAction::Submit {
                conjecture_id,
                proof_file,
                dir,
            } => {
                commands::run::run_prove_submit(
                    conjecture_id.as_deref(),
                    proof_file.as_deref(),
                    dir.as_deref(),
                )
                .await
            }
        },
        Resource::Certificate { action } => match action {
            CertificateAction::List => commands::certificate::cmd_list().await,
            CertificateAction::Create => commands::certificate::cmd_create().await,
            CertificateAction::Import { path } => commands::certificate::cmd_import(&path).await,
            CertificateAction::Compare { by } => {
                commands::certificate::cmd_compare(by.as_deref()).await
            }
            CertificateAction::Report { template } => commands::certificate::cmd_report(&template),
            CertificateAction::Seal => commands::certificate::cmd_seal().await,
            CertificateAction::Publish { id } => commands::certificate::cmd_publish(&id).await,
        },
        Resource::Strategy { action } => match action {
            StrategyAction::List => commands::strategy::cmd_list().await,
            StrategyAction::Get { name } => commands::strategy::cmd_get(&name).await,
            StrategyAction::Import { paths } => commands::strategy::cmd_import(&paths),
        },
        Resource::Setting { action } => match action {
            SettingAction::Get { key } => commands::setting::cmd_get(key.as_deref()),
            SettingAction::Set { key, value } => {
                commands::setting::cmd_set(key.as_deref(), value.as_deref())
            }
        },
        Resource::Auth { action } => match action {
            AuthAction::Login => commands::auth::cmd_login().await,
            AuthAction::Status => commands::auth::cmd_status(),
            AuthAction::Logout => commands::auth::cmd_logout(),
        },
    };

    if let Err(e) = result {
        eprintln!("{}: {:#}", "Error".red(), e);
        std::process::exit(1);
    }
}

use colored::Colorize;
