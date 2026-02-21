# Proof@Home

**Donate unused AI budget to prove mathematical lemmas — verified, archived, and NFT-stamped.**

Proof@Home is a CLI tool that turns your Anthropic API credits into formally verified mathematical proofs. It fetches open problems from a server, uses Claude to generate proof scripts, verifies them with Coq or Lean, and archives the results with SHA-256 hashes in NFT-compatible metadata.

## Quick Start

### Prerequisites

- [Rust](https://rustup.rs/) (1.70+)
- [Go](https://go.dev/dl/) (1.21+)
- An [Anthropic API key](https://console.anthropic.com/)
- **Optional:** [Coq](https://coq.inria.fr/) for Coq proofs, [Lean 4](https://leanprover.github.io/) for Lean proofs

### 1. Build

```bash
cd proof-at-home

# Build the CLI
cargo build --release

# Verify the Go server compiles
go build ./src/server/...
```

The CLI binary is at `target/release/proof-at-home`.

### 2. Set up

```bash
# Interactive setup wizard
./target/release/proof-at-home init
```

This asks for your name, username, Anthropic API key, paths to `coqc`/`lean`, and the server URL. Config is saved to `~/.proof-at-home/config.toml`.

### 3. Set your donation budget

```bash
./target/release/proof-at-home donate
```

Read and accept the legal agreement, then pick an amount ($1–$10 or custom). This is the maximum API cost the tool will spend in a session.

### 4. Start the problem server

In a separate terminal:

```bash
./scripts/dev-server.sh
# or: PROBLEMS_DIR=problems go run ./src/server/...
```

Verify it's running:

```bash
curl http://localhost:8080/health
# {"status":"ok"}

curl http://localhost:8080/problems
# [{"id":"prob_001","title":"Natural number addition is commutative", ...}, ...]
```

### 5. Run a proof session

```bash
./target/release/proof-at-home run
```

This will:

1. Connect to the server and fetch available problems
2. For each problem, call Claude to generate a proof (up to 5 retries with error feedback)
3. Verify each proof with `coqc` or `lean`
4. Submit results to the server
5. Stop when your budget is exhausted
6. Archive all proofs to `~/.proof-at-home/sessions/<session-id>/proofs.tar.gz`
7. Generate NFT-compatible metadata with the archive's SHA-256 hash

### 6. Check your stats

```bash
./target/release/proof-at-home status
```

## Reviewing Proofs

Reviewers evaluate and compare proof packages submitted by different provers. The `review` subcommand tree provides AI-assisted comparison, template-based reporting, and NFT-compatible sealing.

### Workflow

```bash
# 1. Start a review session (fetches available packages from the server)
proof-at-home review start

# 2. Or import local proof archives
proof-at-home review import ./prover-alice-proofs.tar.gz
proof-at-home review import ./prover-bob-proofs.tar.gz

# 3. See what's loaded
proof-at-home review list

# 4. AI-compare proofs across provers (calls Claude, writes ai_comparison.json)
proof-at-home review ai-compare

# 5. Generate and fill in a review report
proof-at-home review report                  # default template
proof-at-home review report --template minimal
proof-at-home review report --template detailed

# 6. Seal the review (archive + NFT metadata + server submission)
proof-at-home review seal
```

### Review session directory

Each session lives under `~/.proof-at-home/reviews/<review-uuid>/`:

```
├── packages/
│   ├── <prover-session-uuid-1>/     # Extracted proof files
│   │   ├── proofs.tar.gz            # Original archive
│   │   └── *.v / *.lean             # Proof scripts
│   └── <prover-session-uuid-2>/
├── ai_comparison.json               # AI comparison output (per-problem + rollup)
├── review_report.toml               # Human-written review report
├── review_summary.json              # Machine-readable summary
├── review_package.tar.gz            # Sealed archive
├── review_nft_metadata.json         # NFT metadata for reviewer credit
└── review_audit.jsonl               # Audit log of AI comparison calls
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

Per-problem scores are averaged into package-level rankings with AI-generated narrative summaries.

### Report templates

Three template variants are available via `--template`:

- **default** — standard template with pre-filled AI rankings
- **minimal** — ranks and one-line assessments only
- **detailed** — adds per-problem commentary sections with AI analysis

### Sealing

`review seal` validates the report, archives everything into `review_package.tar.gz`, computes SHA-256, generates NFT metadata crediting the reviewer, and submits the summary to the server.

### Review demo with example provers

The `examples/review-demo/` directory contains dummy proved proofs from three provers (alice, bob, carol) for `prob_001` and `prob_002`, each using a different proof style:

| Prover | Style | prob_001 (add_comm) | prob_002 (le_antisym) |
|---|---|---|---|
| **alice** | Manual induction | Step-by-step induction with rewrites | Structural induction on both hypotheses |
| **bob** | Automation | One-liner via `lia` | One-liner via `lia` |
| **carol** | Library reuse | `exact Nat.add_comm` | Helper lemma + `Nat.le_antisymm` |

To run the full review demo:

```bash
# 1. Generate proof archives and seed session data
./scripts/seed-review-demo.sh

# 2. Start the server with seed data
SEED_REVIEWS=examples/review-demo/seed \
  PROBLEMS_DIR=problems \
  go run ./src/server/...

# 3. Verify packages are available
curl http://localhost:8080/review-packages | python3 -m json.tool

# 4. Run the reviewer workflow
proof-at-home review start        # select alice, bob, carol
proof-at-home review list
proof-at-home review ai-compare   # AI scores all proofs
proof-at-home review report       # fill in the TOML template
proof-at-home review seal         # archive + NFT metadata
```

You can also import archives manually without the server:

```bash
proof-at-home review start
proof-at-home review import examples/review-demo/alice-proofs.tar.gz
proof-at-home review import examples/review-demo/bob-proofs.tar.gz
proof-at-home review import examples/review-demo/carol-proofs.tar.gz
proof-at-home review ai-compare
```

## Sample Problems

The `problems/` directory includes three starter problems:

| ID | Title | Assistant | Difficulty |
|---|---|---|---|
| `prob_001` | Natural number addition is commutative | Coq | Easy |
| `prob_002` | ≤ antisymmetry on naturals | Coq | Medium |
| `prob_003` | List.reverse is involutive | Lean 4 | Medium |

Add your own by dropping JSON files into `problems/` — the server loads them at startup.

### Problem JSON format

```json
{
  "id": "prob_004",
  "title": "Your problem title",
  "difficulty": "easy|medium|hard",
  "proof_assistant": "coq|lean4",
  "status": "open",
  "preamble": "Require Import Arith.",
  "lemma_statement": "Lemma foo : ...",
  "hints": ["Try induction"],
  "skeleton": "Lemma foo : ...\nProof.\n  sorry\nAdmitted."
}
```

## How It Works

```
┌─────────────┐     GET /problems     ┌─────────────┐
│             │ ───────────────────▶  │             │
│  CLI client │                       │  Go server  │
│  (Rust)     │  POST /results        │  (in-memory)│
│             │ ◀───────────────────  │             │
└──────┬──────┘                       └─────────────┘
       │
       │  For each problem:
       │
       ▼
┌──────────────┐    prompt    ┌──────────────┐
│ Claude CLI / │ ──────────▶ │   Claude AI   │
│ Anthropic API│ ◀────────── │              │
└──────┬───────┘   proof     └──────────────┘
       │
       ▼
┌──────────────┐
│  coqc / lean │  ← verify proof compiles
└──────┬───────┘
       │
       ▼
┌──────────────┐
│  tar.gz +    │  ← archive + SHA-256 + NFT metadata
│  SHA-256     │
└──────────────┘
```

## Server API

| Method | Path | Description |
|---|---|---|
| `GET` | `/health` | Health check |
| `GET` | `/problems` | List all problems (summary) |
| `GET` | `/problems/{id}` | Full problem details |
| `POST` | `/results` | Submit one proof result |
| `POST` | `/results/batch` | Submit session summary with archive hash |
| `GET` | `/review-packages` | List available proof packages for review |
| `GET` | `/review-packages/{id}/archive` | Download a prover's archive |
| `POST` | `/reviews` | Submit review summary |

## Project Structure

```
proof-at-home/
├── Cargo.toml                      # Rust workspace
├── go.mod                          # Go module
├── src/
│   ├── client/                     # Rust CLI
│   │   └── src/
│   │       ├── main.rs             # clap entry point (init/donate/run/status/review)
│   │       ├── commands/           # CLI subcommands (including review)
│   │       ├── prover/             # Claude invocation + coqc/lean verification
│   │       ├── reviewer/           # AI comparison, report templates, review types
│   │       ├── server_client/      # HTTP client for the problem server
│   │       ├── budget/             # Cost tracking and budget enforcement
│   │       ├── archive/            # tar.gz + SHA-256
│   │       ├── config/             # TOML config (~/.proof-at-home/config.toml)
│   │       └── nft/                # OpenSea-compatible metadata generation
│   └── server/                     # Go HTTP server (stdlib only)
│       ├── main.go
│       ├── handlers/               # Route handlers (problems, results, reviews)
│       ├── store/                  # In-memory store
│       └── data/                   # Structs
├── .claude/commands/               # Parameterized prove-lemma strategies
├── problems/                       # Problem JSON files
├── examples/
│   └── review-demo/                # Demo proofs from alice/bob/carol
│       ├── alice/                  # Manual induction style
│       ├── bob/                    # Automation (lia) style
│       ├── carol/                  # Library reuse style
│       └── seed/                   # Seed session JSON for the server
└── scripts/
    ├── dev-server.sh               # Start the Go server
    └── seed-review-demo.sh         # Package demo proofs + generate seed data
```

## Configuration

Config lives at `~/.proof-at-home/config.toml`:

```toml
[identity]
real_name = "Ada Lovelace"
username = "ada_lovelace"
email = "ada@example.com"

[api]
anthropic_api_key = "sk-ant-..."
server_url = "http://localhost:8080"
model = "claude-sonnet-4-6"

[proof_assistant]
scratch_dir = "/tmp/proof-at-home"

[proof_assistant.coq]
coqc_path = "coqc"

[proof_assistant.lean]
lean_path = "lean"
lake_path = "lake"

[budget]
donated_usd = 5.0
session_spent = 0.0
total_spent = 0.0
```

## License

All verified proofs produced by this platform are donated to the **Public Domain** (CC0 1.0 Universal).
