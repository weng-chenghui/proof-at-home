---
lesson_id: discrete-ftap
title: "First Fundamental Theorem of Asset Pricing"
topic: mathematical-finance
difficulty: hard
conjecture_ids: [fin_ftap_001_lean4, fin_ftap_001_rocq, fin_ftap_002_lean4, fin_ftap_002_rocq]
published: true
ai_annotations:
  - zone: "## The FTAP"
    context: "Statement and significance of the First Fundamental Theorem of Asset Pricing"
    suggestions:
      - "Why is the FTAP considered the central result of mathematical finance?"
      - "What does it mean for Q to be equivalent to P?"
      - "How does the FTAP generalize risk-neutral pricing beyond the binomial model?"
  - zone: "## The Easy Direction: Risk-Neutral Measure Implies No-Arbitrage"
    context: "Proving that existence of a risk-neutral measure rules out arbitrage"
    suggestions:
      - "Why can't a non-negative, non-zero payoff have zero expected value under positive state prices?"
      - "How does this direction relate to the pricing formula?"
      - "Is this direction specific to finite markets or does it hold in general?"
  - zone: "## The Hard Direction: No-Arbitrage Implies Risk-Neutral Measure"
    context: "Separation arguments and Farkas' lemma for constructing the risk-neutral measure"
    suggestions:
      - "What is Farkas' lemma and how does it apply here?"
      - "Why is this direction harder than the reverse?"
      - "How does the separating hyperplane theorem connect to state prices?"
---
# First Fundamental Theorem of Asset Pricing

The First Fundamental Theorem of Asset Pricing (FTAP) is the crown jewel of mathematical finance. It states that a market is arbitrage-free if and only if there exists a risk-neutral (equivalent martingale) measure. This connects the economic concept of "no free lunch" to the mathematical concept of measure change, explaining why risk-neutral pricing works as a general principle rather than just a binomial trick.

## The FTAP

**Theorem (First Fundamental Theorem of Asset Pricing).** A finite market model admits no arbitrage if and only if there exists a probability measure $\mathbb{Q}$ equivalent to $\mathbb{P}$ under which the discounted price process is a martingale.

In a finite market with $m$ states, equivalence $\mathbb{Q} \sim \mathbb{P}$ means $\mathbb{Q}$ assigns strictly positive probability to every state. This is the same as the existence of **strictly positive state prices** $q_1, \ldots, q_m > 0$ such that the price of any asset equals its discounted expected payoff under $\mathbb{Q}$.

The FTAP has two directions:

- **Easy direction (this lesson):** If a risk-neutral measure exists, there is no arbitrage.
- **Hard direction (this lesson):** If there is no arbitrage, a risk-neutral measure must exist.

The first direction is a straightforward linear algebra argument. The second requires a separation theorem -- a deep result connecting geometry and optimization.

## The Easy Direction: Risk-Neutral Measure Implies No-Arbitrage

Suppose we have strictly positive state prices $q_1, \ldots, q_m > 0$. An **arbitrage** is a portfolio with:
- Non-negative payoff in every state: $\text{payoff}_j \geq 0$ for all $j$,
- Positive payoff in at least one state: $\text{payoff}_k > 0$ for some $k$,
- Zero or negative initial cost.

Under the risk-neutral measure, the discounted expected payoff is:

$$\sum_{j=1}^{m} q_j \cdot \text{payoff}_j = 0$$

But each term $q_j \cdot \text{payoff}_j \geq 0$ (since $q_j > 0$ and $\text{payoff}_j \geq 0$). A sum of non-negative terms equals zero only if every term is zero. Since $q_k > 0$, we need $\text{payoff}_k = 0$ -- contradicting the assumption that some payoff is positive.

**Conjecture `fin_ftap_002_lean4`:** *The easy direction of the FTAP -- positive state prices rule out arbitrage.*

```lean4
/-- If state prices are positive and payoffs are non-negative,
    then the pricing equation forces both payoffs to zero. -/
theorem ftap_easy_direction
    (q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (payoff₁ payoff₂ : ℝ) (hp₁ : 0 ≤ payoff₁) (hp₂ : 0 ≤ payoff₂)
    (hprice : q₁ * payoff₁ + q₂ * payoff₂ = 0) :
    payoff₁ = 0 ∧ payoff₂ = 0 := by
  constructor
  · nlinarith [mul_nonneg (le_of_lt hq₁) hp₁, mul_nonneg (le_of_lt hq₂) hp₂]
  · nlinarith [mul_nonneg (le_of_lt hq₁) hp₁, mul_nonneg (le_of_lt hq₂) hp₂]
```

```rocq
Lemma ftap_easy_direction :
  forall q1 q2 payoff1 payoff2 : R,
  0 < q1 -> 0 < q2 ->
  0 <= payoff1 -> 0 <= payoff2 ->
  q1 * payoff1 + q2 * payoff2 = 0 ->
  payoff1 = 0 /\ payoff2 = 0.
Proof.
  (* your proof here *)
Admitted.
```

The proof uses `nlinarith` to combine the facts: both products $q_1 \cdot \text{payoff}_1$ and $q_2 \cdot \text{payoff}_2$ are non-negative (positive times non-negative), and they sum to zero. Therefore each product is zero, and since the $q_j$ are positive, each payoff must be zero.

## The Hard Direction: No-Arbitrage Implies Risk-Neutral Measure

This direction is substantially deeper. The idea is a **separation argument**: if no arbitrage exists, the set of achievable payoffs (a convex cone) does not intersect the positive orthant. By the **separating hyperplane theorem** (or equivalently, **Farkas' lemma**), there exists a hyperplane -- defined by a vector of strictly positive weights -- separating the two sets. These weights are the state prices.

In the two-state binomial model, we can give a direct proof. If $d < 1 + r < u$ (no-arbitrage condition), then we can explicitly construct:

$$q = \frac{(1+r) - d}{u - d} \in (0, 1)$$

This $q$ serves as the risk-neutral probability, and we've already shown in the previous lesson that it lies in $(0, 1)$ precisely when $d < 1 + r < u$.

**Conjecture `fin_ftap_001_lean4`:** *FTAP (two-state): no-arbitrage implies risk-neutral probability exists.*

```lean4
/-- In the two-state model, the no-arbitrage condition d < 1+r < u
    implies existence of a risk-neutral probability q ∈ (0,1)
    such that the expected gross return under q equals 1+r. -/
theorem ftap_two_state_forward (u d r : ℝ)
    (hd_lt : d < 1 + r) (hr_lt : 1 + r < u) :
    let q := (1 + r - d) / (u - d)
    0 < q ∧ q < 1 ∧ q * u + (1 - q) * d = 1 + r := by
  refine ⟨?_, ?_, ?_⟩
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)] <;> linarith
  · field_simp
    ring
```

```rocq
Lemma ftap_two_state_forward : forall u d r : R,
  d < 1 + r -> 1 + r < u ->
  let q := (1 + r - d) / (u - d) in
  0 < q /\ q < 1 /\ q * u + (1 - q) * d = 1 + r.
Proof.
  (* your proof here *)
Admitted.
```

The proof constructs $q$ explicitly, verifies $q \in (0, 1)$ using the no-arbitrage bounds, and checks the pricing equation $q \cdot u + (1 - q) \cdot d = 1 + r$ by clearing denominators and simplifying.

**The general finite-dimensional case** uses Farkas' lemma from linear programming duality. Mathlib's `LinearProgramming` and convexity libraries provide the ingredients, though a full formalization of the general FTAP remains an open project.

## Historical Context

The FTAP has a rich history spanning several decades:

- **Harrison & Kreps (1979):** First formulation of the FTAP for discrete-time models. Established the connection between no-arbitrage and martingale measures.
- **Harrison & Pliska (1981):** Characterized complete markets via unique martingale measures (the Second Fundamental Theorem).
- **Dalang, Morton & Willinger (1990):** Proved the general finite discrete-time FTAP using measurable selection arguments.
- **Delbaen & Schachermayer (1994):** Extended the FTAP to continuous-time models, replacing "no-arbitrage" with the stronger "no free lunch with vanishing risk" (NFLVR).

Each generalization required increasingly sophisticated mathematical tools, from linear algebra to functional analysis to stochastic integration.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_ftap_001_lean4` | No-arbitrage implies risk-neutral measure (two-state) | Explicit construction of $q$, `div_pos`, `field_simp` |
| `fin_ftap_002_lean4` | Risk-neutral measure implies no-arbitrage | Non-negative sum equals zero, `nlinarith` |

The FTAP tells us that the ability to price derivatives by discounted expectation under $\mathbb{Q}$ is not a modeling assumption -- it is a *theorem*, equivalent to the absence of arbitrage. Any market that is free of risk-free profit opportunities admits a consistent pricing framework via martingale measures.

**Remark: the Second FTAP and uniqueness.** The *Second Fundamental Theorem of Asset Pricing* (Harrison & Pliska, 1981) states that the risk-neutral measure $\mathbb{Q}$ is **unique** if and only if the market is **complete** — every contingent claim can be replicated. In the binomial model (two states, two assets), the market is complete and $\mathbb{Q}$ is unique. In models with more states than assets, $\mathbb{Q}$ is not unique, leading to a range of no-arbitrage prices rather than a single price.

## Further Reading

- S. E. Shreve, *Stochastic Calculus for Finance I*, Springer, 2004, Chapter 1.
- H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed., de Gruyter, 2016.
- M. Harrison and S. Kreps, "Martingales and arbitrage in multiperiod securities markets," *Journal of Economic Theory*, 1979.
- F. Delbaen and W. Schachermayer, "A general version of the fundamental theorem of asset pricing," *Mathematische Annalen*, 1994.
