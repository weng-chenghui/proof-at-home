# Proof@Home — Partnership Proposal to Anthropic

**From:** [Your Name], Founder, Proof@Home
**To:** Anthropic Leadership
**Date:** February 2026

---

## Executive Summary

Proof@Home is a decentralized platform that converts idle AI subscription capacity into verified mathematical proofs for the public domain. We are proposing a strategic partnership with Anthropic built on three pillars: **subscription discount incentives** for Claude Pro users who opt in, a **residual compute marketplace** that transforms wasted quota into scientific infrastructure, and **co-founding an NGO** to govern the resulting open knowledge base. Anthropic is not just a potential partner — it is *the* partner. Claude's reasoning capabilities, Anthropic's mission alignment with AI safety, and the direct connection between formal verification and safe AI make this a uniquely natural fit. We are asking Anthropic to lead the first large-scale initiative that turns consumer AI subscriptions into a public good — and to profit handsomely while doing it.

---

## 1. The Problem — Wasted Intelligence at Scale

### Millions of reasoning cycles, thrown away every month

The major AI providers collectively serve over 100 million subscribers. Conservative estimates suggest **~40% of paid subscription capacity goes unused** in any given billing cycle. That is not idle CPU time — it is idle *intelligence*. Reasoning capacity that could be solving open problems, verifying theorems, and building the mathematical infrastructure of the future is instead expiring silently at the end of each month.

### SETI@Home searched for signals. We search for *proofs*.

In the early 2000s, SETI@Home demonstrated that millions of volunteers would donate idle CPU cycles to scan radio telescope data for extraterrestrial signals. Folding@Home did the same for protein folding. These projects proved a fundamental insight: **people will contribute resources to science if you make it easy and meaningful.** But those projects donated *hardware* — raw, undifferentiated compute. Proof@Home donates something far more valuable: **structured reasoning from frontier AI models.** The resource is not electricity. It is intelligence.

### The academic bottleneck is staggering

Formal mathematics — the kind verified by proof assistants like Lean, Rocq, and Isabelle — represents humanity's most rigorous form of knowledge. Yet:

- **Less than 1% of known mathematics has been formally verified.** The gap between what mathematicians *know* and what machines can *check* is enormous.
- **Mathlib**, the largest single formalization library, contains ~150,000 theorems — the product of years of painstaking manual effort by a dedicated community.
- At current rates, formalizing even undergraduate mathematics will take decades. AI can compress this timeline from decades to years.

### The accountability gap

AI cannot be listed as an author on a paper. It cannot take responsibility for errors, respond to peer review, or be held accountable for fraud. This creates a paradox: AI can *generate* proofs but cannot *publish* them. Proof@Home resolves this by treating AI output not as authored work but as **verified public domain infrastructure** — like a bridge or a road. Anyone can use it. No one "owns" it. The proof either compiles or it doesn't. The compiler is the author.

---

## 2. The Solution — How Proof@Home Works

### Technical Overview

Proof@Home connects three things: **AI subscriptions** (the reasoning engine), **formal verification compilers** (the truth filter), and **a coordination platform** (the task distributor). The system decomposes mathematical conjectures into sub-lemmas, distributes them to participants, uses AI to generate candidate proofs, and verifies every result through a formal proof assistant before accepting it into the public library.

For full technical details, see [Architecture Overview](architecture.md).

### Data Flow

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

### The Verification Guarantee

This is not another AI product that asks you to trust the output. **Proofs compile or they don't.** A formal verification compiler (Lean, Rocq, Isabelle) provides a binary, unfakeable guarantee of correctness. There is no "mostly right." There is no hallucination risk. The compiler is the ultimate judge, and it cannot be fooled. This makes Proof@Home the only AI-powered platform where *hallucination is architecturally impossible* at the output layer.

### Six Platform Roles

| Role | What They Do | What They Get |
|---|---|---|
| **Curator / Problem Setter** | Compile, decompose, and prioritize the questions to be proved. Source problems from Mathlib gaps, open conjectures, textbook formalization targets, and researcher requests. Break high-level goals into well-scoped lemma tasks suitable for provers. The intellectual backbone of the pipeline — without good questions, proofs are aimless. | Academic recognition as domain architect, curator credit on all downstream proofs, reputation as field organizer, influence over the direction of formalization efforts |
| **Learner / Prover** | Learn math *by doing* — receive lemma tasks, use AI to generate proofs, ask questions to AI and community. The learner IS the prover; proving is the learning process. | Mathematical education, academic credit points, contribution certificates |
| **Reviewer** | Audit machine-verified proofs for *semantic meaning*. Flag results that are technically true but mathematically meaningless or over-engineered. Can overturn results. | Premium credit, reputation as domain expert, quality gatekeeper role |
| **Researcher** | Browse the public domain verified knowledge base. Submit conjectures, cite DOI results in papers. Contribute context and direction. | Free access to verified lemma library, legal safe harbor for AI-assisted work |
| **Resource Contributor** | Transfer unused subscription compute to avoid waste — either donate it (altruistic) or sell it (marketplace) to others who need proving capacity. | Discount on subscription / marketplace revenue / donation tax credit |
| **Company & NGO** | Sponsor compute, run governance, coordinate communities, promote open science. | Business opportunities, marketing ("we fund open mathematics"), industry credit, tax benefits |

### Role Lifecycle — From Question to Citable Knowledge

```
                        ┌─────────────────────────────────────────────┐
                        │         COMPANY & NGO (Pillar 3)            │
                        │  Governance · Funding · Standards · Outreach│
                        └──────────┬──────────────┬───────────────────┘
                                   │ sponsors &    │ governs
                                   │ funds         │ quality standards
                                   ▼              ▼
┌──────────────┐   conjectures   ┌──────────────────────┐
│  RESEARCHER  │ ──────────────► │  CURATOR /           │
│              │                 │  PROBLEM SETTER      │
│ Submits open │   feedback on   │                      │
│ conjectures, │ ◄────────────── │ Decomposes into      │
│ cites DOIs   │   coverage gaps │ well-scoped lemmas,  │
│ in papers    │                 │ prioritizes tasks    │
└──────┬───────┘                 └──────────┬───────────┘
       │                                    │
       │ consumes                           │ distributes
       │ verified                           │ lemma tasks
       │ library                            ▼
       │                         ┌──────────────────────┐
       │                         │  LEARNER / PROVER    │
       │                         │                      │◄─── compute
       │                         │ Receives task,       │     from
       │                         │ uses AI to generate  │     ┌───────────────┐
       │                         │ proof, learns by     │     │   RESOURCE     │
       │                         │ doing                │     │   CONTRIBUTOR  │
       │                         └──────────┬───────────┘     │               │
       │                                    │                 │ Donates or    │
       │                                    │ submits         │ sells unused  │
       │                                    │ verified proof  │ AI quota      │
       │                                    ▼                 └───────────────┘
       │                         ┌──────────────────────┐
       │                         │  FORMAL VERIFIER     │
       │                         │  (Lean/Rocq/Isabelle) │
       │                         │                      │
       │                         │  PASS ──┐  FAIL ──► retry with
       │                         │         │           modified prompt
       │                         └─────────┼───────────┘
       │                                   │
       │                                   ▼
       │                         ┌──────────────────────┐
       │                         │  REVIEWER            │
       │                         │                      │
       │                         │ Semantically valid?  │
       │                         │ Meaningful? Not      │
       │                         │ trivial/circular?    │
       │                         │                      │
       │                         │ ACCEPT ─┐  REJECT ──► back to curator
       │                         │         │             (flag + reason)
       │                         └─────────┼────────────┘
       │                                   │
       │                                   ▼
       │                         ┌──────────────────────┐
       │        consumes         │  PUBLIC DOMAIN       │
       └───────────────────────► │  LEMMA LIBRARY       │
                                 │                      │
                                 │  DOI assigned        │
                                 │  CC0 dedicated       │
                                 │  Citable forever     │
                                 └──────────────────────┘
```

**The lifecycle in one sentence:** Researchers pose questions → Curators scope them → Provers solve them (powered by Resource Contributors) → Verifiers guarantee correctness → Reviewers guarantee meaning → the Library grows → Researchers cite and pose new questions. The Company & NGO governs the whole cycle.

### Why the Reviewer Role Matters

A proof can be *correct* but *useless*. It can be trivially true, circularly dependent, over-specialized to the point of absurdity, or technically valid while being mathematically meaningless. Machines cannot detect this. The Reviewer role solves a problem that no AI can: **distinguishing the true from the trivially true.** This is the human layer that gives the library its scientific value, not just its logical soundness.

---

## 3. The Partnership Proposal — Three Pillars

### Pillar 1: Subscription Discount Incentive
*"Turn a cost center into a growth engine"*

**The ask:** Claude Pro users who opt into Proof@Home receive a **$2–5/month discount** on their subscription.

**Why this works for Anthropic:**

- **Acquisition driver.** "Subscribe to Claude and help prove mathematics" is a marketing message no competitor can match. It transforms a commodity subscription into a mission-driven membership.
- **Retention engine.** Users who accumulate academic credits, contribution certificates, and community reputation have social capital tied to their subscription. Churn drops when leaving means losing your proof record.
- **Usage smoothing.** Proof@Home tasks run through the **Batch API** — off-peak, latency-tolerant, low-priority. They fill idle capacity without competing with interactive users. The discount effectively pays users to smooth Anthropic's demand curve.
- **Net revenue positive.** Even a $5/month discount is recovered if it prevents a single month of churn or attracts one new subscriber who would otherwise have chosen a competitor.

### Pillar 2: Residual Compute Marketplace
*"You're paying for it anyway"*

Flat-rate subscriptions create a structural inefficiency: **unused quota is a sunk cost.** Every month, subscribers leave reasoning capacity on the table. At scale, this waste is extraordinary:

> **2M Claude subscribers × 40% idle = 800,000 user-months of wasted reasoning capacity per month.**

Proof@Home creates **two paths for resource contributors:**

- **Donate** — Altruistic mode. Computation goes to public domain proofs. The contributor receives credit, certificates, and the knowledge that their subscription helped prove a theorem.
- **Sell** — Marketplace mode. Contributors list unused quota on the marketplace. Buyers (researchers, institutions, proof campaigns) purchase it to run proof tasks. Results still go to public domain. Contributors earn revenue from capacity they were already paying for.

Even at a conservative 10% proof success rate, this produces an extraordinary volume of verified mathematics — potentially **tens of thousands of new verified lemmas per month.**

**What this means for Anthropic:**

- Claude transforms from "chatbot" to **"scientific infrastructure."** The brand narrative shifts from consumer product to civilization-scale tool.
- Anthropic can facilitate the marketplace: **transaction fees, platform governance, enterprise accounts.**
- Near-zero marginal cost — the compute is already provisioned. Every marketplace transaction is almost pure margin.

### Pillar 3: NGO Governance
*"Build the institution, not just the product"*

We propose co-founding **The Formal Knowledge Foundation** (working title) — a neutral, non-profit steward for the public domain lemma library and DOI registry.

**The Foundation would:**

- Govern the public domain proof library and DOI assignment system
- Coordinate with Lean FRO, Mathlib, MathComp, Rocq community, and Isabelle/AFP
- Set standards for proof quality, reviewer certification, and contribution credit
- Invite competitors (OpenAI, Google DeepMind, Meta FAIR) to participate — with Anthropic as the **founding sponsor and initiator**
- Operate independently from any single company, ensuring long-term credibility

**Precedents that worked:**
- The **Linux Foundation** — corporate competitors collaborating on shared infrastructure
- The **Apache Foundation** — neutral governance for critical open-source projects
- **arXiv** — open access preprint server that transformed scientific publishing

Anthropic does not need to own the knowledge. Anthropic needs to be the company that **made the knowledge possible.** The Foundation ensures this legacy outlasts any single product cycle.

---

## 3b. Token Economics — "Invest in Science, Not Speculation"

### Crypto-Backed Academic Credits

Proof@Home can use cryptocurrency tokens to represent contribution credits on the platform — but with a critical difference from typical token projects: **every token is backed by a verified proof artifact.**

### Why Tokens

- **Transparent, transferable, immutable** record of contribution
- Each token represents *work done* — proof-of-work in the literal, mathematical sense
- Not speculation, but actual scientific output with a verifiable on-chain record

### Blockchain as the Immutable Proof Archive

The blockchain is not just for tokens — it is the **permanent, decentralized archive** for the proof artifacts themselves. Every piece of the lifecycle gets written on-chain:

| Artifact | What Goes On-Chain | Why It Matters |
|---|---|---|
| **Question / Conjecture** | The original problem statement, submitted by the Curator | Immutable record of *what was asked* — no one can claim a question was different after the fact |
| **Verified Proof** | The full proof script (Lean/Rocq/Isabelle source) that passed compilation | The mathematical knowledge itself, preserved forever. No server shutdown, no company pivot, no database failure can erase it |
| **Reviewer Verdict** | The human Reviewer's accept/reject decision with reasoning | Transparent, auditable quality control. Anyone can verify *why* a proof was accepted or challenged |
| **Contribution Credit** | Token minted to the Prover, Curator, and Reviewer | Attribution that cannot be revoked or falsified |

**Precedent:** People have already written [entire books onto the Ethereum blockchain](https://en.wikipedia.org/wiki/Ethereum). The difference is that those are *text*. Proof@Home writes **machine-verified mathematical truths** — arguably the most valuable form of knowledge humanity produces. If a novel deserves to be on-chain, a proof of the Fundamental Theorem of Algebra certainly does.

**Why this is uniquely suited to blockchain:**

- **Proofs are small.** A Lean proof script is typically kilobytes, not megabytes. On-chain storage is expensive per byte, but proofs are compact — far cheaper to store than images, videos, or books.
- **Proofs are forever.** Mathematical truths do not expire, get outdated, or need updates. Write-once, read-forever is exactly the blockchain storage model.
- **Verification is self-contained.** Anyone with a Lean/Rocq/Isabelle compiler can independently verify any on-chain proof. The chain is not just storage — it is a *self-verifying archive*. No trust in any institution required.
- **Provenance matters.** Who asked the question, who proved it, who reviewed it, when — the full chain of custody is critical for academic citation and credit. Blockchain makes this tamper-proof.

**The result:** Even if Proof@Home the platform disappears, even if Anthropic pivots, even if the NGO dissolves — **the proofs survive on-chain, verifiable by anyone, forever.** The knowledge cannot be lost. This is the strongest possible guarantee of permanence for public domain science.

### Framing Is Everything

This is **"science funding infrastructure,"** not a speculative coin. The token represents *contribution credit*, not ownership of knowledge. All underlying proofs remain CC0 public domain. The aesthetic is arXiv, not meme coins.

### Attracting Crypto Investors to Fund Science

- Crypto investors seeking "utility tokens" with real-world value get one backed by **verifiable mathematical truths** — the hardest possible asset
- Institutions and DAOs can buy tokens to **fund proof campaigns** on specific conjectures (e.g., "formalize this textbook," "verify this theorem family")
- Token value is anchored to the growing lemma library — more proofs = more utility = organic, non-speculative value growth

### How Anthropic Benefits

- Attracts a new **investor/user demographic** (crypto-native, science-curious) without cannibalizing existing markets
- Marketing: **"the first token backed by mathematical truth"** — provocative, defensible, and entirely unique in the market
- Revenue from token marketplace transaction fees

### Reputation Safeguards

- Tokens are **non-speculative utility tokens** (access credits, not investment contracts)
- NGO governance prevents pump-and-dump dynamics; the Foundation controls issuance
- All underlying proofs are CC0 public domain — the token represents *contribution credit*, not ownership of knowledge
- Clear legal structure: consult with securities lawyers, comply with all applicable regulations
- **Fallback option:** make tokens non-transferable (soulbound) if regulatory risk is too high — still fully useful as a reputation and credit system

---

## 4. SWOT Analysis

| | **Positive** | **Negative** |
|---|---|---|
| **Internal** | **Strengths:** Binary verification (zero hallucination risk), CC0 public domain output, mature proof assistant ecosystems, novel resource model (reasoning, not compute), direct mission alignment with Anthropic | **Weaknesses:** AI proof generation still immature (5–20% success rate), user friction (install client + configure API key), cold start problem (need provers before researchers see value), dependency on AI provider pricing decisions |
| **External** | **Opportunities:** Rapid LLM reasoning improvement compounds platform value year-over-year, growing academic demand for responsible AI use frameworks, government and foundation grant eligibility, natural extension to software and hardware verification, crypto investor demographic as science funders | **Threats:** API policy changes could restrict usage, philosophical resistance from parts of academia, competitor replication of the model, regulatory uncertainty around tokens and AI-generated content, proof assistant community fragmentation, crypto association risks if poorly framed |

---

## 5. Market Sizing

| Metric | Estimate |
|---|---|
| **TAM** (Total Addressable Market) | 100M+ global AI subscribers across all providers |
| **SAM** (Serviceable Addressable Market) | 1–5M Claude paid subscribers |
| **SOM** (Serviceable Obtainable Market) | 5–10% opt-in → **100,000–500,000 active proof miners** |
| **Comparable precedent** | SETI@Home peaked at ~5.2M active users; Folding@Home at ~4.5M |
| **Output value** | 100K verified lemmas/year × $500–$5,000 human-equivalent cost = **$50M–$500M in donated labor value annually** |

The comparison to SETI@Home is instructive but understates the opportunity. SETI@Home asked users to donate *electricity* for a project with no tangible output. Proof@Home asks users to donate *already-paid-for reasoning* for a project that produces **citable, permanent, verified mathematical knowledge.** The value proposition to the individual contributor is categorically stronger.

---

## 6. Competitive Positioning

| Competitor | Their Position | Proof@Home's Advantage |
|---|---|---|
| **OpenAI** | No public-benefit compute program. Consumer-focused, no verification initiative. | First-mover opportunity for Anthropic to own the "AI for public good" narrative |
| **Google DeepMind (AlphaProof)** | Impressive results, but proprietary and closed. Research artifact, not open infrastructure. | Proof@Home is open, decentralized, and produces public domain output |
| **Meta FAIR** | Open-source models, but no verification platform or coordination layer. | Models alone don't produce verified proofs; Proof@Home provides the full pipeline |
| **Mathlib / MathComp / AFP** | World-class formalization libraries maintained by dedicated communities. | **Complementary, not competitive.** Proof@Home feeds INTO these libraries, accelerating their growth |
| **BOINC / SETI@Home** | Pioneered volunteer distributed computing for science. | Different resource model entirely: BOINC donates raw compute; Proof@Home donates structured *reasoning* |

**The key insight:** No one else is building this. The intersection of consumer AI subscriptions, formal verification, and volunteer science is an unoccupied niche. The first mover defines the category.

---

## 7. Why Claude — A Practitioner's Testimony

This section is personal. It is not market analysis. It is the lived experience that inspired this platform.

### Daily workflow with Claude Opus for proof exploration

I use Claude Opus every day to explore formal proofs in Rocq and Lean. Not as a novelty. Not as an experiment. As my primary research tool. This is the workflow that convinced me Proof@Home is not just possible — it is *inevitable*. Someone will build it. The question is whether Anthropic will be the partner that shapes how it's built.

### Even wrong proofs are valuable

Claude does not always generate proofs that compile. Current success rates for non-trivial theorems hover around 5–20%. But here is what the success rate misses: **a failed proof attempt with the right structure is enormously valuable.** Claude generates proof *skeletons* — attempts that point toward the right approach, identify the right tactics, and narrow the search space. A failed attempt is not wasted. It is a scaffold that a human or a second AI pass can complete. Proof@Home is designed around this reality.

### Claude excels at the full researcher workflow

What makes Claude uniquely suited is not just proof generation. It is the **complete workflow:**

- **Parsing error messages** — Rocq and Lean compiler errors are notoriously opaque. Claude translates them into actionable guidance, often identifying the exact tactic or lemma needed.
- **Searching scientific literature** — Finding relevant theorems, definitions, and prior work across formalization libraries.
- **Evaluating proof strategies** — Checking whether an approach is sound before committing hours to it.
- **Generating examples and counterexamples** — The fastest way to test whether a conjecture is even plausible.
- **Compressing research time** — Hours of manual library searching compressed into minutes of conversation.

### Workflow amplification

Each of these capabilities is useful in isolation. Combined into structured workflows — task decomposition → skeleton generation → error-guided refinement → verification — they become exponentially more powerful. **Proof@Home encodes these workflows into the platform.** What I do manually every day, Proof@Home automates and scales to hundreds of thousands of participants.

### This is not hypothetical

I have already done this work. Manually. Daily. For months. The proofs exist. The workflow works. Proof@Home is the automation and scaling layer for a process that is already proven viable by a single researcher with a Claude subscription.

---

## 8. Alignment with Anthropic's Mission

Anthropic's stated mission is the **responsible development and maintenance of advanced AI for the long-term benefit of humanity.**

Proof@Home is not loosely "aligned" with this mission. It is a **direct implementation** of it:

- **Formal verification IS AI safety.** The same technology that verifies mathematical proofs can verify properties of AI systems. Every investment in formal verification infrastructure is an investment in the tools needed to ensure AI behaves as intended. Building a global community skilled in formal methods builds the workforce that AI safety will need.

- **Concrete, measurable public benefit.** Not vague claims about "making the world better." Verified lemmas. DOI-registered proofs. CC0 public domain knowledge. Every output is countable, auditable, and permanent.

- **Solving the AI authorship crisis.** The question "can I use AI in my research?" paralyzes academia. Proof@Home provides a transparent framework: the AI generates, the compiler verifies, the human curates, the public benefits. No ambiguity. No hidden AI. No accountability gap.

- **Building the infrastructure for "how do we know the AI is correct?"** In the long run, the most important question about AI is not "how capable is it?" but "how do we verify its outputs?" Proof@Home builds the largest-scale answer to that question ever attempted. It is a proving ground — literally — for AI verification methods.

---

## 9. Revenue Model & Business Case

| Revenue Stream | Estimate |
|---|---|
| **Subscriber acquisition** | 50,000 new subscribers attracted by the program = ~$12M/year in subscription revenue, minus discount cost |
| **Batch API revenue** | Proof tasks consume otherwise-idle batch capacity at near-zero marginal cost — pure incremental revenue |
| **Enterprise/academic upsell** | Institutional licenses for universities, research labs, and proof campaigns |
| **Marketplace fees** | Transaction fees on the residual compute marketplace (Pillar 2) |
| **Brand value** | "The AI company digitizing mathematics for humanity" — unmatched positioning in the AI safety narrative |
| **Training data synergy** | Prompt-proof pairs from the platform create high-quality training data that improves Claude's mathematical reasoning — a virtuous cycle |
| **Tax benefits** | NGO sponsorship provides corporate tax deductions |

**The core business insight:** Proof@Home converts a *cost center* (idle subscription capacity, customer churn, flat brand perception) into a *growth engine* (new subscribers, higher retention, marketplace revenue, training data, mission-aligned brand). The economics are not zero-sum. They are *generative.*

---

## 10. Risk Mitigation

| Risk | Mitigation |
|---|---|
| **API abuse** | Dedicated Proof@Home API tier with restricted capabilities — proofs only, no general chat |
| **Trivial proof spam** | Curated problem sets sourced from Mathlib gaps, open conjectures, and textbook formalization projects. Reviewer role filters meaningless results. |
| **"Exploitative" perception** | Participation is entirely voluntary. Users receive a discount. NGO independence ensures the platform serves the public, not the sponsor. |
| **Scalability** | Local-first verification architecture — the client verifies before submitting. Server only re-verifies accepted proofs. Load scales with participants, not centrally. |
| **Single-provider lock-in** | Multi-provider support from Phase 2 of the roadmap. Anthropic positioned as flagship partner, not sole dependency. |
| **Proof quality** | Human Reviewer role catches technically-correct-but-useless proofs. Curated task queues prevent gaming. |

---

## 11. Proposed Next Steps

Based on the [project roadmap](roadmap.md):

1. **Technical Proof of Concept** — Demonstrate end-to-end pipeline using Anthropic's Batch API + Lean 4: submit lemma → Claude generates proof → Lean verifies → DOI assigned. Timeline: 8–12 weeks.

2. **Joint Announcement** — Co-authored blog post on Anthropic's blog. Present at Lean Together conference or ICML workshop. Establish Anthropic as the founding AI partner.

3. **Pilot Program** — 1,000 Claude Pro subscribers opt in. Measure proof success rate, user engagement, churn impact, and batch API utilization patterns.

4. **NGO Formation** — Establish The Formal Knowledge Foundation with Lean FRO, Mathlib maintainers, and academic partners. Draft governance charter and DOI registration process.

5. **Public Launch** — Open enrollment with discount program. Multi-provider support. Researcher portal with verified lemma library and citation export.

---

## 12. Appendices

### Reference Documents

- [Architecture Overview](architecture.md) — Full system design, component descriptions, data flow, and technology choices
- [Project Roadmap](roadmap.md) — Phased development timeline from foundation through ecosystem
- [README & BOINC Comparison](../README.md) — Problem framing, user personas, and comparison with traditional distributed science

### Example Proof Workflow

```
1. Researcher submits: "Formalize the statement that every finite group
   of order p² (p prime) is abelian."

2. Task Coordinator decomposes into sub-lemmas:
   a. Define finite group of order p²
   b. Prove the center is non-trivial (class equation)
   c. Prove G/Z(G) cyclic implies G abelian
   d. Assemble: order p² → |Z(G)| ∈ {p, p²} → G abelian

3. Lemma (c) assigned to a Proof Miner running Claude via Batch API

4. Claude generates a Lean 4 proof script (attempt 1: fails on
   tactic 'group_theory.quotient'; attempt 2: succeeds with
   'QuotientGroup.cyclic_of_prime_power')

5. Local Lean 4 compiler verifies: PASS ✓

6. Submitted to coordinator → server-side re-verification: PASS ✓

7. Stored in Lemma Library → DOI assigned: 10.XXXXX/pah.2026.00142

8. Researcher cites DOI in their paper on finite group classification
```

### Potential NGO Advisory Board

Representatives from the formal methods community, including:

- Lean FRO (Lean Focused Research Organization)
- Mathlib maintainers and contributors
- Rocq development team
- Isabelle/AFP (Archive of Formal Proofs) editors
- Academic formal methods researchers
- AI safety organizations
- Open access advocates

---

*Proof@Home is not asking Anthropic to do charity. We are asking Anthropic to lead — to be the first AI company that turns its subscription base into a scientific instrument, its idle compute into verified knowledge, and its brand into a synonym for AI that builds, not just generates. The proofs will speak for themselves. They always do.*

---

**Contact:** [Your Name] — [Your Email] — [Your Affiliation]
**Project:** [github.com/[your-org]/proof-at-home](https://github.com/[your-org]/proof-at-home)
