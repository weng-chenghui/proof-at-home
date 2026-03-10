---
series_id: chemical-logic
title: "Formal Foundations of Chemical Logic"
difficulty: hard
description: "A rigorous course applying formal verification (Lean 4 & Rocq) to Chemical Reaction Network Theory (CRNT). From stoichiometric conservation laws and graph topology through deficiency and invariance, culminating in the Deficiency Zero Theorem — the crown jewel of introductory CRNT."
lesson_ids:
  - crn-stoichiometry
  - crn-weak-reversibility
  - crn-deficiency
  - crn-invariance
  - crn-deficiency-zero
published: true
---
# Formal Foundations of Chemical Logic

This series brings **formal verification** to **Chemical Reaction Network Theory** (CRNT). Every theorem is machine-checked in either Lean 4 (with Mathlib) or Rocq (with MathComp), giving you both chemical intuition and rigorous proof skills.

## Who Is This For?

- **Math/CS students** interested in applying formal methods to chemistry and systems biology
- **Chemical engineers** curious about what "provably correct" stoichiometry and kinetics really mean
- **Lean 4 / Rocq practitioners** looking for applied proof challenges in linear algebra and graph theory

Prerequisites: basic linear algebra (matrices, kernels, rank), comfort with one of Lean 4 or Rocq. No prior chemistry or CRNT knowledge is assumed — we build everything from scratch.

## Course Structure

### Module 1: Atomicity & Conservation Laws (Stoichiometry)

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 1 | [Atomicity & Conservation Laws](../../lessons/crn-stoichiometry/lesson.md) | Lean 4 & Rocq | Easy |

We start with the stoichiometric matrix and prove that element conservation follows from left-nullspace membership. The classic water formation reaction 2H₂ + O₂ → 2H₂O serves as the running example.

### Module 2: Graph Topology (Weak Reversibility)

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 2 | [Graph Topology & Weak Reversibility](../../lessons/crn-weak-reversibility/lesson.md) | Rocq & Lean 4 | Medium |

CRNs have a natural graph structure: complexes are vertices, reactions are edges. A network is weakly reversible iff every connected component is strongly connected. We prove this for a simple 3-cycle using Tarjan's SCC formalization in Rocq.

### Module 3: The Deficiency Formula

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 3 | [The Deficiency Formula](../../lessons/crn-deficiency/lesson.md) | Lean 4 & Rocq | Hard |

The deficiency δ = n − ℓ − s is the central invariant of CRNT. We formalize the formula, prove δ ≥ 0, and compute δ = 0 for the classic enzymatic reaction E + S ⇌ ES → E + P.

### Module 4: Stoichiometric Compatibility Classes (Invariance)

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 4 | [Stoichiometric Compatibility Classes](../../lessons/crn-invariance/lesson.md) | Lean 4 & Rocq | Medium |

The concentration vector c(t) is confined to c(0) + im(S), the stoichiometric compatibility class. This invariance is the reason you cannot create atoms from nothing. We prove that carbon count is preserved under any trajectory.

### Module 5: The Deficiency Zero Theorem

| # | Lesson | Prover | Difficulty |
|---|--------|--------|------------|
| 5 | [The Deficiency Zero Theorem](../../lessons/crn-deficiency-zero/lesson.md) | Lean 4 & Rocq | Hard |

The crown theorem of introductory CRNT: for a weakly reversible, deficiency-zero network under mass-action kinetics, there exists exactly one positive equilibrium in each stoichiometric compatibility class. This module synthesizes all previous results.

## What You'll Learn

By completing this series, you will be able to:

1. **Formalize chemical concepts** — stoichiometric matrices, complexes, reaction graphs, deficiency — as precise mathematical statements
2. **Prove conservation laws** — show that element counts are preserved using left-nullspace arguments
3. **Work with graph theory** — formalize strong connectivity and weak reversibility in Rocq (tarjan) and Lean 4 (Quiver)
4. **Reason about invariants** — prove that trajectories are confined to stoichiometric compatibility classes
5. **State the Deficiency Zero Theorem** — the culmination of introductory CRNT, connecting topology, algebra, and kinetics

## Conjectures Overview

| ID | Title | Prover | Difficulty |
|----|-------|--------|------------|
| `crn_stoich_001_lean4` | H-atom conservation for water formation | Lean 4 | Easy |
| `crn_stoich_002_rocq` | O-atom conservation for water formation | Rocq | Easy |
| `crn_graph_001_rocq` | 3-cycle is strongly connected | Rocq | Easy |
| `crn_graph_002_lean4` | Reachability in a simple reaction graph | Lean 4 | Medium |
| `crn_def_001_lean4` | Deficiency is non-negative | Lean 4 | Medium |
| `crn_def_002_rocq` | Deficiency zero for enzymatic reaction | Rocq | Hard |
| `crn_inv_001_lean4` | Concentration stays in compatibility class | Lean 4 | Medium |
| `crn_inv_002_rocq` | Carbon-count invariant | Rocq | Easy |
| `crn_dzt_001_lean4` | Positive equilibrium exists (DZT) | Lean 4 | Hard |
| `crn_dzt_002_rocq` | Unique equilibrium for enzymatic network | Rocq | Medium |
