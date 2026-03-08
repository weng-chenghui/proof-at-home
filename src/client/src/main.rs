mod agent;
mod ai;
mod archive;
mod budget;
mod certifier;
mod commands;
mod config;
mod conjecture_viz;
mod ipfs;
mod nft;
mod proof_tree;
mod prover;
mod server_client;
mod signing;
mod strategy_store;
mod tools;

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
    /// Manage proving strategies (list, get, import, memory)
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
    /// Check, list, or install external tool dependencies
    Tools {
        #[command(subcommand)]
        action: ToolsAction,
    },
    /// Query AI provider info (list, get, quota)
    Provider {
        #[command(subcommand)]
        action: ProviderAction,
    },
    /// Manage the shared data pool (clone, pull, push, status)
    Pool {
        #[command(subcommand)]
        action: PoolAction,
    },
    /// Create and manage expositions (mixed text+visual explanations)
    Exposition {
        #[command(subcommand)]
        action: ExpositionAction,
    },
    /// Create and manage lessons (educational content with conjectures)
    Lesson {
        #[command(subcommand)]
        action: LessonAction,
    },
    /// Create and manage lesson series (curriculum packaging)
    Series {
        #[command(subcommand)]
        action: SeriesAction,
    },
    /// Run AI agents
    Agent {
        #[command(subcommand)]
        action: AgentAction,
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
    /// Export a conjecture in a format suitable for AI assistant chat
    Export {
        /// Conjecture ID
        id: String,
        /// Output format: prompt (default), json, source
        #[arg(long, default_value = "prompt")]
        format: String,
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
        /// Read proof from stdin instead of a file
        #[arg(long)]
        stdin: bool,
        /// Proof method: manual (default), pair-proved, api-assisted
        #[arg(long, default_value = "manual")]
        method: String,
    },
    /// Parse a proof and generate a human-readable explanation (exposition)
    Parse {
        /// Path to a local proof file (.v or .lean)
        proof_file: Option<String>,
        /// Contribution ID (to fetch proof from server)
        #[arg(long)]
        contribution: Option<String>,
        /// Conjecture ID (to fetch proof from server)
        #[arg(long)]
        conjecture: Option<String>,
        /// Use a specific parse strategy (by name)
        #[arg(long = "by")]
        by: Option<String>,
        /// Output format: text (default) or tree (interactive HTML proof tree)
        #[arg(long, default_value = "text")]
        format: String,
        /// Output file path for tree format (default: proof-tree.html)
        #[arg(long, short)]
        output: Option<String>,
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
    List {
        /// Filter by kind (e.g. prove, certify-compare, memory-lesson)
        #[arg(long)]
        kind: Option<String>,
    },
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
    /// Manage agent memories (strategies with kind=memory-*)
    Memory {
        #[command(subcommand)]
        action: MemoryAction,
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

// ── Tools ──

#[derive(Subcommand)]
enum ToolsAction {
    /// Check all tool dependencies and show their status
    Check,
    /// List all tools in a table
    List,
    /// Install a tool dependency (if auto-install is supported)
    Install {
        /// Tool name (e.g. elan, claude)
        name: String,
    },
}

// ── Provider ──

#[derive(Subcommand)]
enum ProviderAction {
    /// List available AI providers
    List,
    /// Show current provider configuration
    Get,
    /// Query remaining credits/requests from the provider
    Quota,
}

// ── Lesson ──

#[derive(Subcommand)]
enum LessonAction {
    /// List all lessons
    List,
    /// Get details for a specific lesson
    Get {
        /// Lesson ID
        id: String,
    },
    /// Create a lesson (api-assisted, pair-proved, or manual)
    Create {
        /// Topic for the lesson
        #[arg(long)]
        topic: Option<String>,
        /// Comma-separated conjecture IDs to include
        #[arg(long)]
        conjectures: Option<String>,
        /// Difficulty level: easy, medium, hard
        #[arg(long)]
        difficulty: Option<String>,
        /// Output file path for the generated lesson.md
        #[arg(long, short)]
        output: Option<String>,
        /// Read lesson.md from stdin
        #[arg(long)]
        stdin: bool,
        /// Creation method: api-assisted (default), pair-proved, manual
        #[arg(long, default_value = "api-assisted")]
        method: String,
    },
    /// Export lesson prompt for use with an AI assistant
    Export {
        /// Comma-separated conjecture IDs
        #[arg(long)]
        conjectures: Option<String>,
        /// Topic for the lesson
        #[arg(long)]
        topic: Option<String>,
    },
}

// ── Series ──

#[derive(Subcommand)]
enum SeriesAction {
    /// List all series
    List,
    /// Get details for a specific series
    Get {
        /// Series ID
        id: String,
    },
    /// Create a series (api-assisted, pair-proved, or manual)
    Create {
        /// Comma-separated lesson IDs to include
        #[arg(long)]
        lessons: Option<String>,
        /// Output file path
        #[arg(long, short)]
        output: Option<String>,
        /// Read series.md from stdin
        #[arg(long)]
        stdin: bool,
        /// Creation method: api-assisted (default), pair-proved, manual
        #[arg(long, default_value = "api-assisted")]
        method: String,
    },
    /// Export series prompt for use with an AI assistant
    Export {
        /// Comma-separated lesson IDs
        #[arg(long)]
        lessons: Option<String>,
    },
}

// ── Exposition ──

#[derive(Subcommand)]
enum ExpositionAction {
    /// Create an exposition for a resource (conjecture, contribution, certificate)
    Create {
        /// Resource ID (auto-detected: prob_xxx=conjecture, contrib_xxx=contribution, cert_xxx=certificate)
        #[arg(long)]
        r#for: String,
        /// Mathematical domain for specialized strategy
        #[arg(long)]
        domain: Option<String>,
        /// Use a specific strategy (by name)
        #[arg(long = "by")]
        by: Option<String>,
        /// Output file path
        #[arg(long, short)]
        output: Option<String>,
        /// Read pre-generated exposition JSON from stdin (for pair provers)
        #[arg(long)]
        stdin: bool,
        /// Creation method: api-assisted (default), pair-proved, manual
        #[arg(long, default_value = "api-assisted")]
        method: String,
    },
    /// Export the exposition prompt for use with an AI coding assistant
    Export {
        /// Resource ID
        #[arg(long)]
        r#for: String,
        /// Mathematical domain for specialized strategy
        #[arg(long)]
        domain: Option<String>,
    },
    /// List expositions
    List,
    /// Get an exposition by ID
    Get {
        /// Exposition ID
        id: String,
    },
}

// ── Pool ──

#[derive(Subcommand)]
enum PoolAction {
    /// Clone the shared data pool
    Clone {
        /// Custom directory for the pool
        #[arg(long)]
        dir: Option<String>,
    },
    /// Pull latest changes from the pool
    Pull,
    /// Push local changes to the pool
    Push,
    /// Show pool git status
    Status,
}

// ── Agent ──

#[derive(Subcommand)]
enum AgentAction {
    /// Run an agent task
    Run {
        #[command(subcommand)]
        task: AgentTask,
    },
    /// Show agent run status
    Status {
        /// Run ID to query
        run_id: Option<String>,
    },
}

#[derive(Subcommand)]
enum AgentTask {
    /// Run the lesson agent (multi-step lesson generation with memory)
    Lesson {
        /// Topic for the lesson
        #[arg(long)]
        topic: Option<String>,
        /// Comma-separated conjecture IDs
        #[arg(long)]
        conjectures: Option<String>,
        /// Difficulty level: easy, medium, hard
        #[arg(long)]
        difficulty: Option<String>,
        /// Output file path
        #[arg(long, short)]
        output: Option<String>,
    },
}

#[derive(Subcommand)]
enum MemoryAction {
    /// List agent memories
    List {
        /// Filter by kind (e.g. memory-lesson)
        #[arg(long)]
        kind: Option<String>,
        /// Filter by agent ID
        #[arg(long)]
        agent: Option<String>,
    },
    /// Get details for a specific memory
    Get {
        /// Memory name
        name: String,
    },
    /// Create a memory manually
    Create {
        /// Memory kind (e.g. memory-lesson)
        #[arg(long)]
        kind: String,
        /// Memory body text
        #[arg(long)]
        body: String,
        /// Comma-separated tags
        #[arg(long)]
        tags: Option<String>,
    },
    /// Delete a memory
    Forget {
        /// Memory name
        name: String,
    },
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
            ConjectureAction::Export { id, format } => {
                commands::conjecture::cmd_export(&id, &format).await
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
                stdin,
                method,
            } => {
                commands::run::run_prove_submit(
                    conjecture_id.as_deref(),
                    proof_file.as_deref(),
                    dir.as_deref(),
                    stdin,
                    &method,
                )
                .await
            }
            ProofAction::Parse {
                proof_file,
                contribution,
                conjecture,
                by,
                format,
                output,
            } => {
                commands::proof::cmd_parse(
                    proof_file.as_deref(),
                    contribution.as_deref(),
                    conjecture.as_deref(),
                    by.as_deref(),
                    &format,
                    output.as_deref(),
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
            StrategyAction::List { kind } => commands::strategy::cmd_list(kind.as_deref()).await,
            StrategyAction::Get { name } => commands::strategy::cmd_get(&name).await,
            StrategyAction::Import { paths } => commands::strategy::cmd_import(&paths),
            StrategyAction::Memory { action: mem_action } => match mem_action {
                MemoryAction::List { kind, agent } => {
                    commands::strategy::cmd_memory_list(kind.as_deref(), agent.as_deref())
                }
                MemoryAction::Get { name } => commands::strategy::cmd_memory_get(&name),
                MemoryAction::Create { kind, body, tags } => {
                    commands::strategy::cmd_memory_create(&kind, &body, tags.as_deref())
                }
                MemoryAction::Forget { name } => commands::strategy::cmd_memory_forget(&name),
            },
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
        Resource::Tools { action } => match action {
            ToolsAction::Check => commands::tools::cmd_check(),
            ToolsAction::List => commands::tools::cmd_list(),
            ToolsAction::Install { name } => commands::tools::cmd_install(&name),
        },
        Resource::Provider { action } => match action {
            ProviderAction::List => commands::provider::cmd_list(),
            ProviderAction::Get => commands::provider::cmd_get(),
            ProviderAction::Quota => commands::provider::cmd_quota().await,
        },
        Resource::Pool { action } => match action {
            PoolAction::Clone { dir } => commands::pool::cmd_clone(dir.as_deref()).await,
            PoolAction::Pull => commands::pool::cmd_pull().await,
            PoolAction::Push => commands::pool::cmd_push().await,
            PoolAction::Status => commands::pool::cmd_status().await,
        },
        Resource::Lesson { action } => match action {
            LessonAction::List => commands::lesson::cmd_list().await,
            LessonAction::Get { id } => commands::lesson::cmd_get(&id).await,
            LessonAction::Create {
                topic,
                conjectures,
                difficulty,
                output,
                stdin,
                method,
            } => {
                commands::lesson::cmd_create(
                    topic.as_deref(),
                    conjectures.as_deref(),
                    difficulty.as_deref(),
                    output.as_deref(),
                    stdin,
                    &method,
                )
                .await
            }
            LessonAction::Export { conjectures, topic } => {
                commands::lesson::cmd_export(conjectures.as_deref(), topic.as_deref()).await
            }
        },
        Resource::Series { action } => match action {
            SeriesAction::List => commands::series::cmd_list().await,
            SeriesAction::Get { id } => commands::series::cmd_get(&id).await,
            SeriesAction::Create {
                lessons,
                output,
                stdin,
                method,
            } => {
                commands::series::cmd_create(lessons.as_deref(), output.as_deref(), stdin, &method)
                    .await
            }
            SeriesAction::Export { lessons } => {
                commands::series::cmd_export(lessons.as_deref()).await
            }
        },
        Resource::Agent { action } => match action {
            AgentAction::Run { task } => match task {
                AgentTask::Lesson {
                    topic,
                    conjectures,
                    difficulty,
                    output,
                } => {
                    commands::agent::cmd_run_lesson(
                        topic.as_deref(),
                        conjectures.as_deref(),
                        difficulty.as_deref(),
                        output.as_deref(),
                    )
                    .await
                }
            },
            AgentAction::Status { run_id } => commands::agent::cmd_status(run_id.as_deref()),
        },
        Resource::Exposition { action } => match action {
            ExpositionAction::Create {
                r#for,
                domain,
                by,
                output,
                stdin,
                method,
            } => {
                commands::exposition::cmd_create(
                    &r#for,
                    domain.as_deref(),
                    by.as_deref(),
                    output.as_deref(),
                    stdin,
                    &method,
                )
                .await
            }
            ExpositionAction::Export { r#for, domain } => {
                commands::exposition::cmd_export(&r#for, domain.as_deref()).await
            }
            ExpositionAction::List => commands::exposition::cmd_list().await,
            ExpositionAction::Get { id } => commands::exposition::cmd_get(&id).await,
        },
    };

    if let Err(e) = result {
        eprintln!("{}: {:#}", "Error".red(), e);
        std::process::exit(1);
    }
}

use colored::Colorize;
