# Architecture Overview

## System Components

### 1. Task Coordinator (Server)

The central service responsible for:
- Accepting conjecture submissions from researchers
- Decomposing conjectures into sub-lemmas (potentially using AI assistance)
- Distributing lemma tasks to proof miners
- Collecting and storing verified proofs
- Assigning DOIs and managing the public lemma library
- Tracking contributor credits

### 2. Proof Miner Client

A lightweight desktop/CLI application that:
- Connects to the user's AI subscription (Claude, ChatGPT, Gemini) via API keys
- Pulls lemma tasks from the coordinator
- Constructs prompts to generate proof scripts
- Runs a local formal verification compiler (Lean, Rocq, or Isabelle)
- Submits verified proofs back to the coordinator

### 3. Verification Pipeline

A trust-critical component that ensures every proof is sound:
- Supports multiple proof assistants (Lean 4, Coq/Rocq, Isabelle/HOL)
- Runs verification both locally (on the miner) and server-side (for double-check)
- Rejects any proof that does not compile cleanly
- Logs verification metadata (compiler version, timestamps, hash)

### 4. Researcher Portal (API + Web UI)

Interface for academic users:
- Browse and search the verified lemma library
- Submit conjectures for crowd-solving
- Export citations with DOI for papers
- Track proof progress on submitted conjectures

### 5. Public Ledger / Registry

Immutable record of all contributions:
- Timestamped proof submissions
- Contributor attribution (pseudonymous or named)
- DOI assignment for citability
- CC0 public domain dedication per entry

## Data Flow

```
Researcher submits conjecture
        │
        ▼
Task Coordinator decomposes into sub-lemmas
        │
        ▼
Lemma tasks distributed to Proof Miners
        │
        ▼
Miner's AI generates candidate proof script
        │
        ▼
Local formal verifier checks the proof
        │
        ├── FAIL → retry with modified prompt
        │
        └── PASS → submit to coordinator
                    │
                    ▼
              Server-side re-verification
                    │
                    ▼
              Stored in Lemma Library with DOI
                    │
                    ▼
              Available for researcher citation
```

## Technology Choices (Proposed)

| Component | Technology |
|---|---|
| Server | Rust or Go |
| Client | Rust (CLI) with optional Electron/Tauri GUI |
| API | REST + gRPC |
| Database | PostgreSQL + object storage for proof artifacts |
| Verification | Lean 4, Rocq, Isabelle (containerized) |
| AI Integration | OpenAI API, Anthropic API, Google AI API |
| Registry | Content-addressed storage (IPFS or similar) |
