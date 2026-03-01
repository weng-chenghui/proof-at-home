# Proof@Home

**Donate unused AI budget to prove mathematical lemmas — verified, archived, and NFT-stamped.**

Proof@Home turns mathematical contributions into formally verified, NFT-stamped public goods. A Rust CLI fetches open conjectures from a Go server, uses Claude to generate formal proofs, verifies them with Rocq or Lean, and seals the results with NFT metadata. Two paths: **AI-assisted** (allocate API budget, LLM generates proofs) or **manual** (write proofs by hand, submit for verification).

## How It Works

1. **Browse** open conjectures on the web UI or CLI
2. **Prove** — AI generates proofs (or you write them by hand), then the compiler verifies correctness
3. **Seal** — verified proofs are archived with SHA-256 hashes, signed, and committed to a git-backed data repo
4. **Credit** — NFT metadata records who funded and verified the work
5. **Publish** (optional) — pin to IPFS and mint an on-chain NFT

## Cost per Proof

| Model | Typical cost per proof | Speed |
|---|---|---|
| Haiku | ~$0.05 | Fast |
| Sonnet | ~$0.50 | Balanced |
| Opus | ~$2.00 | Most capable |

A $2 budget can prove dozens of easy conjectures with Haiku.

## Quick Start

### Prerequisites

- [Rust](https://rustup.rs/) (1.70+)
- An [Anthropic API key](https://console.anthropic.com/) (AI-assisted mode only)
- [Rocq](https://rocq-prover.org/) for Rocq proofs, or [Lean 4](https://leanprover.github.io/) for Lean proofs

### 1. Build the CLI

```bash
git clone https://github.com/pah-org/proof-at-home.git
cd proof-at-home
cargo build --release
```

### 2. Configure

```bash
./target/release/proof-at-home setting set          # Interactive setup wizard
./target/release/proof-at-home auth login            # Paste token from web UI
./target/release/proof-at-home setting set budget    # Set your API budget
```

### 3. Prove

**AI-assisted** (LLM generates proofs, compiler verifies):

```bash
pah contribution run        # Start proving
pah contribution list       # Check your contributions
```

**Manual** (you write proofs, compiler verifies):

```bash
pah proof submit prob_001 ./my_proof.v               # Single proof
pah proof submit --dir ./my-proofs/                   # Batch of .v/.lean files
```

No API key or budget needed for manual mode.

### 4. Publish (optional)

```bash
pah contribution publish <id>    # Pin to IPFS, generate mint script
./mint.sh                        # Mint on-chain NFT
```

See the [Publishing Guide](docs/publishing-guide.md) for full details.

## User Roles

| Role | What you do | What you need |
|---|---|---|
| **Prover** | Run AI proofs or submit hand-written proofs | API key (AI mode) or proof assistant (manual mode) |
| **Certifier** | Compare and rank proof packages from multiple provers | CLI + server access |
| **Author** | Submit open conjectures for others to prove | CLI + domain knowledge |

Pick one role or do all three.

## Certifying Proofs

Certifiers evaluate and compare proof packages submitted by different provers:

```bash
pah certificate create           # Fetch packages from server
pah certificate import ./proofs.tar.gz  # Or import local archives
pah certificate compare          # AI-compare proofs across packages
pah certificate report           # Generate certification report
pah certificate seal             # Seal with NFT metadata + PR
```

### AI comparison scoring

Each proof is scored on five dimensions (1-10) plus an overall score:

| Dimension | What it measures |
|---|---|
| **Succinctness** | Shorter, cleaner proofs with no unnecessary steps |
| **Library reuse** | Use of existing library lemmas (mathlib, mathcomp) |
| **Generality** | General results vs overly specific ones |
| **Modularity** | Decomposition into reusable lemmas/structures |
| **Math strategy** | Elegance of the proof approach |

## Why NFTs?

The NFT is not about ownership — proofs are public domain (CC0). The NFT records *who funded and verified* the work, like a donor's name on a university building.

- **Digital patronage** — "this theorem was formalized because of my financial and computational support"
- **Curation credit** — certifiers invest human judgment to compare, rank, and approve proofs
- **Provenance, not ownership** — the proofs themselves are CC0, the NFT captures attribution

<details>
<summary>NFT metadata details</summary>

Three types of NFTs are generated:

| Role | Key attributes |
|---|---|
| **Contributor** | Username, Problems Proved/Attempted, Cost Donated (USD), Proof Assistant, Proof Status, Proof Mode (`manual` or `ai-assisted`) |
| **Certifier** | Reviewer, Packages Reviewed, Problems Compared, Top Contributor, Recommendation, Archive SHA-256, AI Comparison Cost (USD) |
| **Submitter** | Username, Batch ID, Conjectures Submitted, Conjecture IDs, Difficulties, Proof Assistants, Git Commit |

NFT metadata is OpenSea-compatible JSON, generated locally and committed to the data repository when a contribution or certificate is sealed.

</details>

## Deployment

See the [Deployment Guide](docs/deployment.md) for full instructions. The recommended path:

```bash
# Build PocketBase server
go build -o pah-pocketbase ./cmd/pocketbase

# Try locally
CONJECTURES_DIR=./conjectures ./pah-pocketbase serve

# Deploy to Fly.io
fly launch --copy-config --no-deploy
fly volumes create pb_data --size 1 --region nrt
fly deploy
```

Estimated time: ~15 minutes. Fly.io free tier covers a single instance with 1 GB storage.

## Local Development

```bash
make dev-setup        # Set up local dev environment with example data
make dev-run          # Run standalone server (port 8080)
make run-pocketbase   # Or run PocketBase server (port 8090, includes admin UI at /_/)
```

<details>
<summary>Server API reference</summary>

| Method | Path | Description |
|---|---|---|
| `GET` | `/health` | Health check |
| `GET` | `/conjectures` | List conjectures (summary) |
| `GET` | `/conjectures/{id}` | Full conjecture details |
| `GET` | `/contributions` | List contributions |
| `GET` | `/contributions/{id}` | Get contribution details |
| `GET` | `/contributions/{id}/proofs` | List results for a contribution |
| `POST` | `/contributions` | Create a new contribution |
| `POST` | `/contributions/{id}/proofs` | Submit a proof result |
| `PATCH` | `/contributions/{id}` | Finalize a contribution |
| `POST` | `/contributions/{id}/seal` | Seal contribution (archive + NFT + PR) |
| `GET` | `/certificates` | List certificates |
| `GET` | `/contribution-reviews` | List proof packages available for certification |
| `GET` | `/contribution-reviews/{id}/archive` | Download a prover's archive |
| `POST` | `/certificates` | Submit a certificate |
| `POST` | `/certificates/{id}/seal` | Seal certificate (archive + NFT + PR) |
| `POST` | `/conjectures` | Submit conjecture package (tar.gz or git URL) |
| `POST` | `/conjectures/{batchId}/seal` | Seal conjecture package (submitter NFT + PR) |
| `POST` | `/webhooks/git` | Git webhook (signature-verified) |

</details>

<details>
<summary>Project structure</summary>

```
proof-at-home/
├── Cargo.toml                          # Rust workspace
├── go.mod                              # Go module (chi, sqlite, jwt)
├── src/
│   ├── client/                         # Rust CLI
│   │   └── src/
│   │       ├── main.rs                 # clap entry point
│   │       ├── commands/               # Subcommands (prove, certify, seal, publish, ...)
│   │       ├── prover/                 # LLM invocation + rocq/lean verification
│   │       ├── certifier/              # AI comparison, report templates, sealing
│   │       ├── server_client/          # HTTP client for the server API
│   │       ├── budget/                 # Cost tracking and budget enforcement
│   │       ├── archive/                # tar.gz + SHA-256
│   │       ├── config/                 # TOML config (~/.proof-at-home/config.toml)
│   │       ├── nft/                    # OpenSea-compatible NFT metadata generation
│   │       └── signing.rs              # Ed25519 signatures for git commits
│   └── server/                         # Go HTTP server
│       ├── main.go                     # Entry point (chi router, forge init, SQLite)
│       ├── config/                     # Environment-based configuration
│       ├── handlers/                   # Route handlers (contributions, certificates, webhooks)
│       ├── store/                      # Store interface + git-backed / SQLite / Postgres impls
│       ├── middleware/                  # JWT auth (optional)
│       ├── data/                       # Shared data types
│       └── static/                     # Embedded web UI
├── cmd/pocketbase/                     # PocketBase deployment (recommended)
├── examples/                           # Example data repo, commands, review demo
├── tests/integration/                  # Integration tests
├── scripts/                            # Dev setup, server start, seed scripts
├── conjectures/                        # Starter conjecture files
└── docs/                               # Deployment guide, publishing guide
```

</details>

<details>
<summary>CLI configuration reference</summary>

Config file: `~/.proof-at-home/config.toml`

```toml
[identity]
real_name = "Ada Lovelace"
username = "ada_lovelace"
email = "ada@example.com"

[api]
anthropic_api_key = "sk-ant-..."
server_url = "http://localhost:8080"
model = "claude-sonnet-4-6"

[prover]
scratch_dir = "/tmp/proof-at-home"

[budget]
donated_usd = 5.0       # AI-assisted mode only
run_spent = 0.0
total_spent = 0.0
```

> **Note:** `[api].anthropic_api_key` and `[budget]` are only needed for AI-assisted mode. Manual proof submission requires only `[identity]`, `[api].server_url`, and `[prover]`.

</details>

## License

All verified proofs produced by this platform are donated to the **Public Domain** (CC0 1.0 Universal).
