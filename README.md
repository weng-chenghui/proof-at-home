# Proof@Home

**A Decentralized AI-Formalized Knowledge Donation Platform**

## Motivation

The current academic landscape faces a paradox: while AI can generate complex mathematical proofs and scientific content, conferences often reject these papers due to authorship and accountability concerns. Furthermore, scientific progress is hindered when major corporations "silo" AI-discovered truths.

Proof@Home aims to democratize scientific discovery by converting personal AI subscriptions and idle compute into a massive, verifiable "knowledge donation" engine for the public domain.

## Problems We Solve

- **The Accountability Gap:** AI cannot be "credited" as an author because it cannot take responsibility. Proof@Home treats AI output as *Formalized Public Knowledge*, which humans then curate and cite.
- **AI Hallucinations:** Every contribution must pass through a Formal Verification Tool (Lean, Coq, Isabelle). This ensures 100% mathematical soundness.
- **Centralization of Discovery:** Shifts the power of discovery from high-budget labs to a global network of individuals.

## How It Works

### For Researchers

1. **Verified Lemma Libraries** — Browse a vast repository of pre-proven, machine-verified lemmas as building blocks for higher-level papers.
2. **Outsourcing Proofs** — Upload a complex conjecture; the platform breaks it down into sub-problems (lemmas) for the crowd to solve.
3. **Legal "Safe Harbor"** — Cite a DOI from the platform's public domain library to legally use AI-generated content without violating conference rules.

### For Individuals (Proof "Miners")

1. **AI Service Integration** — Link existing AI subscriptions (ChatGPT Plus, Claude Pro, Gemini) via API to the Proof@Home client.
2. **Proof Mining** — The client receives a logic puzzle or mathematical lemma, uses the AI to generate a proof script, and runs a local compiler to verify it.
3. **Donation** — Once verified, the proof is uploaded and timestamped. The user receives "Academic Credit" points or digital certificates of contribution.

### For Companies & Organizations

- **Open Science Leadership** — Accelerate the digitization of all known mathematics.
- **Preventing "Patent Trolls"** — Push AI discoveries into the public domain immediately.
- **Standardization** — Establish a universal standard for how AI-generated logic should be verified and cited.

## Comparison with Existing Projects

| Feature | Traditional Distributed Science (BOINC) | Proof@Home |
|---|---|---|
| Primary Resource | Raw CPU/GPU hardware cycles | AI Model Intelligence (API/LLM) + Hardware |
| Task Nature | Numerical crunching (brute force) | Symbolic Reasoning (Logic/Proofs) |
| Output Type | Raw data / signal hits | Formalized Code (Lean/Coq/Isabelle) |
| Verification | Redundant calculation (double checking) | Logical Compilation (100% certainty) |
| Legal Standing | Data belongs to the project lab | Results donated to Public Domain |
| Human Role | Passive (providing electricity) | Active (setting up prompts / checking logic) |

## Project Structure

```
proof-at-home/
├── docs/           # Design documents, specs, and research notes
├── src/
│   ├── client/     # Proof miner client application
│   ├── server/     # Task distribution and coordination server
│   ├── verifier/   # Formal verification pipeline (Lean/Coq/Isabelle)
│   └── api/        # REST API for researcher portal and integrations
├── contracts/      # Smart contracts or licensing/legal templates
├── scripts/        # Build, deploy, and utility scripts
├── tests/          # Test suites
└── examples/       # Example conjectures, proofs, and workflows
```

## License

All verified proofs produced by this platform are donated to the **Public Domain** (CC0 1.0 Universal).

Platform source code is licensed under [TBD].
