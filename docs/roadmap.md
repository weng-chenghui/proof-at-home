# Roadmap

## Phase 1: Foundation

- [ ] Define proof task schema (input conjecture format, output proof format)
- [ ] Build minimal CLI proof miner client with single AI provider support
- [ ] Integrate Lean 4 as the first verification backend
- [ ] Build basic task coordinator server with in-memory task queue
- [ ] End-to-end demo: submit lemma → AI generates proof → verify → store

## Phase 2: Multi-Prover Support

- [ ] Add Coq/Rocq verification backend
- [ ] Add Isabelle verification backend
- [ ] Support multiple AI providers (Claude, ChatGPT, Gemini)
- [ ] Implement server-side re-verification pipeline
- [ ] PostgreSQL persistence for proofs and contributor records

## Phase 3: Researcher Portal

- [ ] REST API for browsing and searching the lemma library
- [ ] Web UI for researchers to submit conjectures
- [ ] DOI assignment system for verified proofs
- [ ] Citation export (BibTeX, etc.)
- [ ] Conjecture decomposition engine (AI-assisted sub-lemma generation)

## Phase 4: Scale & Community

- [ ] Contributor credit system and leaderboards
- [ ] Public ledger for immutable proof records
- [ ] Organization accounts for universities and research labs
- [ ] Documentation and onboarding guides
- [ ] Community governance model

## Phase 5: Ecosystem

- [ ] IDE plugins for proof assistant integration
- [ ] Formal library interop (import/export with Mathlib, MathComp, AFP)
- [ ] Patent prior-art search integration
- [ ] Conference submission helper tools
