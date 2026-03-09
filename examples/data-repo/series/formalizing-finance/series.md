---
series_id: formalizing-finance
title: "Formalizing the Foundations of Finance"
difficulty: hard
description: "A comprehensive course combining formal verification (Lean 4 & Rocq) with mathematical finance. From basic NPV and put-call parity through binomial pricing, martingale theory, and the Fundamental Theorem of Asset Pricing, each concept is machine-checked for correctness."
lesson_ids:
  - irr-existence-ivt
  - put-call-parity
  - binomial-no-arbitrage
  - delta-hedging
  - multi-period-binomial
  - discrete-martingales
  - discrete-ftap
  - crr-convergence
  - verified-numerical-pricing
published: true
---
# Formalizing the Foundations of Finance

This series bridges two worlds: **mathematical finance** and **formal verification**. Every theorem is machine-checked in either Lean 4 (with Mathlib) or Rocq (Coq), giving you both deep financial intuition and rigorous proof skills.

## Who Is This For?

- **Math/CS students** who want to see formal verification applied to a domain beyond pure mathematics
- **Finance professionals** curious about what "provably correct" pricing really means
- **Lean 4 / Rocq practitioners** looking for applied, non-trivial proof challenges

Prerequisites: basic real analysis (continuity, limits), comfort with one of Lean 4 or Rocq. No prior finance knowledge is assumed — we build everything from scratch.

## Course Structure

### Module 1: Deterministic Cash Flows & No-Arbitrage

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 1 | [Time Value of Money — Existence of IRR via IVT](../../lessons/irr-existence-ivt/lesson.md) | Lean 4 | Medium |
| 2 | [Static Replication & Put-Call Parity](../../lessons/put-call-parity/lesson.md) | Rocq | Easy |

We start with the basics: NPV, IRR, and the simplest no-arbitrage argument (put-call parity). These lessons establish the pattern of translating financial identities into formal statements.

### Module 2: The Binomial Model (Discrete Time)

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 3 | [Single-Period Binomial Tree & No-Arbitrage](../../lessons/binomial-no-arbitrage/lesson.md) | Lean 4 | Medium |
| 4 | [Delta Hedging & Market Completeness](../../lessons/delta-hedging/lesson.md) | Lean 4 | Medium |
| 5 | [Multi-Period Binomial & Backward Induction](../../lessons/multi-period-binomial/lesson.md) | Lean 4 | Hard |

The binomial model is the workhorse of discrete-time finance. We build it up from a single period to multiple periods, proving risk-neutral pricing, the Law of One Price, delta hedging, and backward induction along the way.

### Module 3: Discrete Probability & Martingales (Advanced)

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 6 | [Discrete Martingales & Fair Games](../../lessons/discrete-martingales/lesson.md) | Lean 4 | Hard |
| 7 | [First Fundamental Theorem of Asset Pricing](../../lessons/discrete-ftap/lesson.md) | Lean 4 | Hard |
| 7b | [CRR Convergence: Binomial to Black-Scholes](../../lessons/crr-convergence/lesson.md) *(bonus)* | Lean 4 | Hard |

The mathematical core: martingale theory and the FTAP. Lesson 7b is a bonus that connects the discrete binomial world to continuous-time Black-Scholes pricing.

### Module 4: Numerical Correctness

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 8 | [Verified Numerical Pricing with Interval Arithmetic](../../lessons/verified-numerical-pricing/lesson.md) | Rocq | Hard |

The final module addresses a practical concern: can we trust the numbers our pricing software produces? Using Flocq and CoqInterval, we prove rigorous bounds on computed option prices.

## What You'll Learn

By completing this series, you will be able to:

1. **Formalize financial concepts** — NPV, options, arbitrage, risk-neutral pricing — as precise mathematical statements
2. **Prove fundamental theorems** — IVT for IRR existence, put-call parity, the FTAP — in Lean 4 and Rocq
3. **Work with Mathlib** — use `Continuous`, `Finset.sum`, `MeasureTheory`, and `Probability.Martingale`
4. **Apply interval arithmetic** — verify numerical correctness of pricing implementations using Flocq/CoqInterval
5. **Bridge theory and practice** — understand why risk-neutral pricing works, not just how to compute it

## Conjectures Overview

| ID | Title | Prover | Difficulty |
|----|-------|--------|------------|
| `fin_irr_002` | NPV is continuous in the discount rate | Lean 4 | Easy |
| `fin_irr_001` | Existence of IRR via IVT | Lean 4 | Medium |
| `fin_pcp_002` | Call payoff is non-negative | Rocq | Easy |
| `fin_pcp_001` | Put-Call Parity: payoff identity | Rocq | Easy |
| `fin_binom_001` | Risk-neutral probability lies in (0,1) | Lean 4 | Medium |
| `fin_binom_002` | Law of One Price | Lean 4 | Medium |
| `fin_delta_001` | Delta hedge replicates derivative payoff | Lean 4 | Medium |
| `fin_multi_001` | Backward induction pricing | Lean 4 | Easy |
| `fin_multi_002` | Self-financing portfolio identity | Lean 4 | Medium |
| `fin_mart_001` | Symmetric random walk is a martingale | Lean 4 | Easy |
| `fin_mart_002` | Discounted binomial price is martingale under Q | Lean 4 | Hard |
| `fin_ftap_001` | FTAP (two-state): no-arbitrage ⇒ risk-neutral probability | Lean 4 | Hard |
| `fin_ftap_002` | FTAP: risk-neutral measure ⇒ no-arbitrage | Lean 4 | Medium |
| `fin_crr_001` | CRR convergence to Black-Scholes *(bonus, placeholder)* | Lean 4 | Hard (placeholder) |
| `fin_num_001` | Interval bounds on discounted call intrinsic value | Rocq | Hard |
| `fin_num_002` | Vega positivity (call price increasing in vol) | Rocq | Medium |
