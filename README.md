# Proof@Home

**Donate unused AI budget to prove mathematical lemmas — verified, archived, and NFT-stamped.**

Proof@Home turns your unused AI API budget into formally verified mathematical proofs. A Rust CLI fetches open conjectures from a git-backed Go server, uses an LLM to generate proof scripts, verifies them with Rocq or Lean, and seals the results into git commits with NFT metadata.

All data flows through **git as the source of truth**. The server writes contributions, certificates, and conjectures to branches, creates pull requests via GitHub/GitLab, and rebuilds a read-only SQLite cache on merge. Every artifact is traceable, forkable, and auditable by design.

## Why NFTs?

AI-generated content creates an attribution problem. When an AI writes a formal proof, even the person who prompted it faces scrutiny over whether they deserve credit — and paper reviewers may dismiss AI-generated proofs outright, assuming low quality regardless of correctness. Any result produced by AI automation is unlikely to count as a novel intellectual contribution in academia.

But any contribution to mathematics is a contribution — whether or not academia admits it. Formalizing open conjectures requires **budget, computation, and time**, and these resources are real, measurable, and chronically undervalued:

| Contribution | What it costs | Why academia ignores it |
|---|---|---|
| **Donating API budget** | Real money spent on LLM API credits to generate candidate proofs | "Just paying for a service" |
| **Certifying others' proofs** | Hours comparing, ranking, and approving proof packages from multiple provers | "Just reviewing, not creating" |
| **Tuning machine proofs** | Iterating on AI output to make it compile — fixing import paths, tactic syntax, version mismatches | "Just engineering, not mathematics" |
| **Learning math to ask better questions** | Studying enough to write good conjectures, understand proof strategies, and formulate hints | "Just learning, not contributing" |
| **Porting between provers** | Translating a Rocq proof to Lean 4 or vice versa — requires deep knowledge of both systems | "Just translation, not original work" |

None of these produce a novel theorem. All of them are necessary to grow the corpus of formally verified mathematics. The NFT is the credit mechanism for this work:

- **Digital patronage** — like a donor's name on a university building, the NFT records "this theorem was formalized because of my financial and computational support."
- **Curation credit** — certifiers invest human judgment to compare, rank, and approve AI-generated proofs. The certification NFT records that editorial work.
- **Provenance, not ownership** — the proofs themselves are public domain (CC0). The NFT captures *who funded and verified* the work, not who "owns" it.

This makes Proof@Home a form of **Retroactive Public Goods Funding** for mathematics: contributors spend real money, real compute, and real time to produce freely available formalizations, and the NFT is the permanent receipt of that contribution.

### NFT metadata

Two types of NFTs are generated:

| Role | Key attributes |
|---|---|
| **Prover** | Username, Problems Proved/Attempted, Cost Donated (USD), Proof Assistant, Archive SHA-256, Proof Status |
| **Certifier** | Reviewer, Packages Reviewed, Problems Compared, Top Prover, Recommendation, Archive SHA-256, AI Comparison Cost (USD) |

NFT metadata is OpenSea-compatible JSON, generated locally and committed to the data repository when a contribution or certificate is sealed.

## Quick Start

### Prerequisites

- [Rust](https://rustup.rs/) (1.70+)
- [Go](https://go.dev/dl/) (1.21+)
- An LLM API key ([Anthropic](https://console.anthropic.com/) supported first; other providers planned)
- **Optional:** [Rocq](https://rocq-prover.org/) for Rocq proofs, [Lean 4](https://leanprover.github.io/) for Lean proofs

### 1. Build

```bash
# Build the CLI
cargo build --release

# Build the Go server
go build -o pah-server ./src/server/...
```

The CLI binary is at `target/release/proof-at-home`.

### 2. Set up the local dev environment

```bash
# Initialize a local git data repo with example data
./scripts/dev-setup.sh

# Start the server (LocalForge auto-merges branches, no GitHub required)
./scripts/dev-server.sh
```

This creates a bare git repo at `.dev/data-repo.git` populated with sample conjectures and contributions.

Verify:

```bash
curl http://localhost:8080/health
# {"status":"ok"}

curl http://localhost:8080/conjectures
# [{"id":"prob_001","title":"Natural number addition is commutative", ...}]
```

### 3. Configure the CLI

```bash
./target/release/proof-at-home init
```

Asks for your name, username, API key, and server URL. Config is saved to `~/.proof-at-home/config.toml`.

### 4. Set your donation budget

```bash
./target/release/proof-at-home donate
```

Read and accept the legal agreement, then pick an amount ($1–$10 or custom). This caps the API cost per contribution run.

### 5. Run a proof contribution

```bash
./target/release/proof-at-home prove
```

This will:

1. Fetch available conjectures from the server
2. For each conjecture, call the LLM to generate a proof (up to 5 retries with error feedback)
3. Verify each proof with `rocq c` or `lean`
4. Submit results to the server (written to a git branch)
5. Stop when your budget is exhausted
6. Seal the contribution — archive, SHA-256 hash, Ed25519 signature, NFT metadata, and a pull request on the data repository

### 6. Check your stats

```bash
./target/release/proof-at-home status
```

## Certifying Proofs

Certifiers evaluate and compare proof packages submitted by different provers. The `certify` subcommand provides AI-assisted comparison, template-based reporting, and NFT-sealed certification.

### Workflow

```bash
# 1. Start a certification (fetches available packages from the server)
proof-at-home certify start

# 2. Or import local proof archives
proof-at-home certify import ./prover-alice-proofs.tar.gz
proof-at-home certify import ./prover-bob-proofs.tar.gz

# 3. See what's loaded
proof-at-home certify list

# 4. AI-compare proofs across provers (calls LLM, writes ai_comparison.json)
proof-at-home certify ai-compare

# 5. Generate and fill in a certification report
proof-at-home certify report                  # default template
proof-at-home certify report --template minimal
proof-at-home certify report --template detailed

# 6. Seal the certification (archive + NFT metadata + PR on data repo)
proof-at-home certify seal
```

### AI comparison scoring

Each proof is scored on five dimensions (1–10) plus an overall score:

| Dimension | What it measures |
|---|---|
| **Succinctness** | Shorter, cleaner proofs with no unnecessary steps |
| **Library reuse** | Use of existing library lemmas (mathlib, mathcomp) |
| **Generality** | General results vs overly specific ones |
| **Modularity** | Decomposition into reusable lemmas/structures |
| **Math strategy** | Elegance of the proof approach |

Per-conjecture scores are averaged into package-level rankings with AI-generated narrative summaries.

### Report templates

Three template variants are available via `--template`:

- **default** — standard template with pre-filled AI rankings
- **minimal** — ranks and one-line assessments only
- **detailed** — adds per-conjecture commentary sections with AI analysis

### Sealing

`certify seal` validates the report, archives everything, computes SHA-256, generates NFT metadata crediting the certifier, and creates a pull request on the data repository.

## How It Works

```
┌──────────────┐                          ┌──────────────┐
│  CLI client   │  REST API               │  Go server    │
│  (Rust)       │ ──────────────────────▶ │  (chi router) │
│               │ ◀────────────────────── │               │
└──────┬───────┘                          └──────┬───────┘
       │                                         │
       │  For each conjecture:                   │ Writes to git branches,
       ▼                                         │ creates PRs via forge
┌──────────────┐  prompt   ┌──────────┐          ▼
│ Anthropic API │ ───────▶ │  Claude   │  ┌─────────────────┐
│               │ ◀─────── │          │  │  Git data repo   │
└──────┬───────┘  proof    └──────────┘  │  (source of truth)│
       │                                  │  ├── conjectures/ │
       ▼                                  │  ├── contributions/│
┌──────────────┐                          │  └── certificates/ │
│  rocq c/lean │  verify                  └────────┬────────┘
└──────┬───────┘                                   │
       │                                  webhook (push to main)
       ▼                                           │
┌──────────────┐                          ┌────────▼────────┐
│  Seal:       │                          │  SQLite cache    │
│  tar.gz +    │                          │  (read-only,     │
│  SHA-256 +   │                          │   rebuilt on merge)│
│  Ed25519 +   │                          └─────────────────┘
│  NFT metadata│
└──────────────┘
```

### Data flow

1. **CLI** generates proofs and submits them via the REST API.
2. **Server** writes JSON and proof files to a **git branch** (e.g., `contrib/<uuid>`).
3. On seal, the server **pushes** the branch and creates a **pull request** via the forge API (GitHub, GitLab, or auto-merge for local dev).
4. When the PR merges to `main`, a **webhook** notifies the server, which pulls the latest `main` and **rebuilds** the SQLite cache.
5. All reads hit the **SQLite cache** for fast responses; all writes go through **git**.

### Forge backends

| Backend | Use case | PR behavior |
|---|---|---|
| **GitHub** | Production | Creates GitHub pull requests |
| **GitLab** | Production | Creates GitLab merge requests |
| **Local** | Development | Auto-merges branches into main |

## Server API

| Method | Path | Description |
|---|---|---|
| `GET` | `/health` | Health check |
| `GET` | `/conjectures` | List conjectures (summary) |
| `GET` | `/conjectures/{id}` | Full conjecture details |
| `GET` | `/contributions` | List contributions |
| `GET` | `/contributions/{id}` | Get contribution details |
| `GET` | `/contributions/{id}/results` | List results for a contribution |
| `POST` | `/contributions` | Create a new contribution |
| `POST` | `/contributions/{id}/results` | Submit a proof result |
| `PATCH` | `/contributions/{id}` | Finalize a contribution |
| `POST` | `/contributions/{id}/seal` | Seal contribution (archive + NFT + PR) |
| `GET` | `/certificates` | List certificates |
| `GET` | `/certificate-packages` | List proof packages available for certification |
| `GET` | `/certificate-packages/{id}/archive` | Download a prover's archive |
| `POST` | `/certificates` | Submit a certificate |
| `POST` | `/certificates/{id}/seal` | Seal certificate (archive + NFT + PR) |
| `POST` | `/conjecture-packages` | Submit conjecture package (tar.gz or git URL) |
| `POST` | `/webhooks/git` | Git webhook (signature-verified) |

## Sample Conjectures

| ID | Title | Prover | Difficulty |
|---|---|---|---|
| `prob_001` | Natural number addition is commutative | Rocq | Easy |
| `prob_002` | ≤ antisymmetry on naturals | Rocq | Medium |
| `prob_003` | List.reverse is involutive | Lean 4 | Medium |

Add your own by dropping JSON files into the data repository's `conjectures/` directory, or submit them at runtime:

```bash
# Submit a directory of conjecture JSON files
proof-at-home submit-package ./my-conjectures/

# Submit a tar.gz archive
proof-at-home submit-package /tmp/conjectures.tar.gz

# Submit a git repo URL (server clones it)
proof-at-home submit-package https://github.com/example/conjectures.git
```

### Conjecture JSON format

```json
{
  "id": "prob_004",
  "title": "Your conjecture title",
  "difficulty": "easy|medium|hard",
  "prover": "rocq|lean4",
  "status": "open",
  "preamble": "Require Import Arith.",
  "lemma_statement": "Lemma foo : ...",
  "hints": ["Try induction"],
  "skeleton": "Lemma foo : ...\nProof.\n  sorry\nAdmitted."
}
```

## Project Structure

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
│   │       ├── commands_store/         # Extensible command system (load from files/git)
│   │       ├── budget/                 # Cost tracking and budget enforcement
│   │       ├── archive/                # tar.gz + SHA-256
│   │       ├── config/                 # TOML config (~/.proof-at-home/config.toml)
│   │       ├── nft/                    # OpenSea-compatible NFT metadata generation
│   │       └── signing.rs              # Ed25519 signatures for git commits
│   └── server/                         # Go HTTP server
│       ├── main.go                     # Entry point (chi router, forge init, SQLite)
│       ├── config/                     # Environment-based configuration
│       ├── handlers/                   # Route handlers (contributions, certificates, webhooks)
│       ├── store/
│       │   └── gitstore/               # Git-backed source of truth
│       │       ├── gitstore.go         # Branch/commit/push operations
│       │       ├── forge.go            # ForgeClient interface (CreatePR, webhooks)
│       │       ├── github.go           # GitHub forge implementation
│       │       ├── gitlab.go           # GitLab forge implementation
│       │       └── local.go            # LocalForge (auto-merge for dev)
│       ├── sqlite/                     # Read-only SQLite cache (rebuilt from git)
│       ├── middleware/                  # JWT auth (optional)
│       ├── data/                       # Shared data types
│       ├── logging/                    # Structured logging (slog)
│       └── static/                     # Embedded web UI
├── examples/
│   ├── data-repo/                      # Example git data repo structure
│   │   ├── conjectures/                # Sample conjecture JSON
│   │   ├── contributions/              # Sample contribution with proofs and results
│   │   └── certificates/               # Sample certificate
│   ├── commands/                       # Example prover/certifier command files
│   └── review-demo/                    # Demo proofs from alice/bob/carol
├── tests/
│   └── integration/                    # Integration tests for the git-backed API
├── scripts/
│   ├── dev-setup.sh                    # Initialize local git data repo
│   ├── dev-server.sh                   # Start server with LocalForge
│   └── seed-review-demo.sh             # Seed demo certification data
├── .github/workflows/ci.yml            # CI: Rust + Go + integration tests
└── conjectures/                        # Starter conjecture files
```

## Configuration

### CLI config (`~/.proof-at-home/config.toml`)

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

[prover.rocq]
rocq_path = "rocq"

[prover.lean]
lean_path = "lean"
lake_path = "lake"

[budget]
donated_usd = 5.0
run_spent = 0.0
total_spent = 0.0
```

### Server environment variables

| Variable | Description | Default |
|---|---|---|
| `PORT` | Listen port | `8080` |
| `DATABASE_PATH` | SQLite cache file | `:memory:` |
| `GIT_DATA_REPO_URL` | URL/path of the bare data repo | — |
| `GIT_DATA_REPO_PATH` | Local clone path | — |
| `GIT_FORGE_TYPE` | `github`, `gitlab`, or `local` | — |
| `GIT_FORGE_TOKEN` | API token for GitHub/GitLab | — |
| `GIT_FORGE_PROJECT` | `owner/repo` or GitLab project ID | — |
| `AUTH_ENABLED` | Enable JWT authentication | `false` |
| `CORS_ORIGINS` | Allowed CORS origins | `*` |

## License

All verified proofs produced by this platform are donated to the **Public Domain** (CC0 1.0 Universal).
