---
lesson_id: discrete-martingales
title: "Discrete Martingales & Fair Games"
topic: mathematical-finance
difficulty: hard
conjecture_ids: [fin_mart_001_lean4, fin_mart_001_rocq, fin_mart_002_lean4, fin_mart_002_rocq]
published: true
ai_annotations:
  - zone: "## What is a Martingale?"
    context: "Intuition and formal definition of a martingale as a fair game"
    suggestions:
      - "What does it mean intuitively for a process to be a martingale?"
      - "How does the filtration capture the idea of information over time?"
      - "Can you give a non-financial example of a martingale?"
  - zone: "## Martingales in Lean 4"
    context: "Mathlib's MeasureTheory and Filtration for formalizing martingales"
    suggestions:
      - "How does Mathlib represent conditional expectation?"
      - "What is MeasureTheory.Filtration and how does it model information?"
      - "Why is handling sigma-algebras tricky even in the finite case?"
  - zone: "## Discounted Prices as Martingales"
    context: "The martingale property of discounted prices under the risk-neutral measure Q"
    suggestions:
      - "Why must discounted prices be martingales under Q?"
      - "How does the definition of q make the martingale property work?"
      - "What goes wrong if we use the real-world measure P instead of Q?"
---
# Discrete Martingales & Fair Games

A martingale is a stochastic process whose expected future value, given all past information, equals its current value -- the mathematical model of a "fair game." Martingale theory is the backbone of modern mathematical finance: the discounted price of any asset is a martingale under the risk-neutral measure. This lesson introduces the martingale concept, connects it to Lean 4 formalization via Mathlib, and shows why discounted prices satisfy the martingale property.

## What is a Martingale?

We work on a **filtered probability space** $(\Omega, \mathcal{F}, (\mathcal{F}_n)_{n \geq 0}, \mathbb{P})$, where $(\mathcal{F}_n)$ is an increasing sequence of sigma-algebras representing the information available at each time step.

A stochastic process $(X_n)_{n \geq 0}$ is a **martingale** (with respect to $(\mathcal{F}_n)$ and $\mathbb{P}$) if:

1. $X_n$ is $\mathcal{F}_n$-measurable for each $n$ (adapted),
2. $E[|X_n|] < \infty$ for each $n$ (integrable),
3. $E[X_{n+1} \mid \mathcal{F}_n] = X_n$ almost surely (the martingale property).

**Intuition:** Knowing the entire history up to time $n$ does not help predict the future increment $X_{n+1} - X_n$. On average, the process stays where it is.

**Classic example: symmetric random walk.** Let $X_1, X_2, \ldots$ be independent with $P(X_i = +1) = P(X_i = -1) = 1/2$. Define $S_n = X_1 + \cdots + X_n$. Then:

$$E[S_{n+1} \mid S_1, \ldots, S_n] = S_n + E[X_{n+1}] = S_n + 0 = S_n$$

So $(S_n)$ is a martingale. This is the simplest model of a fair game: on each round, you win or lose one unit with equal probability.

**Conjecture `fin_mart_001_lean4`:** *The symmetric random walk is a martingale.*

```lean4
/-- The expected value of a symmetric ±1 step is zero,
    so the partial sum S_n is a martingale. -/
theorem symmetric_rw_martingale
    (p : ℝ) (hp : p = 1 / 2)
    (X_up X_dn : ℝ) (hup : X_up = 1) (hdn : X_dn = -1)
    (S : ℝ) :
    p * (S + X_up) + (1 - p) * (S + X_dn) = S := by
  subst hp; subst hup; subst hdn
  ring
```

```rocq
Lemma symmetric_rw_martingale : forall x : R,
  let p := 1/2 in
  p * (x + 1) + (1 - p) * (x - 1) = x.
Proof.
  (* your proof here *)
Admitted.
```

The proof substitutes $p = 1/2$, $X_{\text{up}} = 1$, $X_{\text{dn}} = -1$ and reduces the one-step conditional expectation to an algebraic identity that `ring` discharges.

## Martingales in Lean 4

Mathlib provides the infrastructure for a fully measure-theoretic treatment of martingales:

- **`MeasureTheory.Filtration`** models the information structure $(\mathcal{F}_n)$ as an order-preserving map from an index type to sub-sigma-algebras.
- **`MeasureTheory.condexp`** provides conditional expectation $E[X \mid \mathcal{G}]$ with the correct measurability and integrability properties.
- **`Probability.Martingale`** in Mathlib defines a process as a martingale when `condexp m (f (n+1)) =ᵐ[μ] f n` for all `n`.

The full formalization of even simple examples requires careful handling of sigma-algebras, measurability proofs, and integrability conditions. Even in finite settings, the measure-theoretic overhead is non-trivial.

Our simplified conjecture `fin_mart_001_lean4` sidesteps the measure theory by working directly with the algebraic content of the martingale property: the expected value computation. A full Mathlib-based proof would additionally verify adaptedness and integrability.

## Discounted Prices as Martingales

The key result connecting martingale theory to finance is:

> **The discounted stock price $\tilde{S}_n = S_n / (1+r)^n$ is a martingale under the risk-neutral measure $\mathbb{Q}$.**

In the single-period binomial model, this is a direct computation. With $q = ((1+r) - d)/(u - d)$:

$$E^{\mathbb{Q}}[\tilde{S}_1] = \frac{q \cdot S_0 u + (1 - q) \cdot S_0 d}{1 + r}$$

Substituting the definition of $q$:

$$= \frac{S_0 \left(\frac{(1+r) - d}{u - d} \cdot u + \frac{u - (1+r)}{u - d} \cdot d\right)}{1 + r} = \frac{S_0 \cdot (1+r)}{1+r} = S_0 = \tilde{S}_0$$

This is exactly the martingale property! The definition of $q$ is precisely the value that makes discounted prices a martingale.

**Conjecture `fin_mart_002_lean4`:** *The discounted binomial price is a martingale under Q.*

```lean4
/-- Under the risk-neutral measure, the discounted stock price
    satisfies E^Q[S₁/(1+r)] = S₀. -/
theorem discounted_martingale (S₀ u d r : ℝ) (hdu : d < u)
    (hr1 : d < 1 + r) (hr2 : 1 + r < u) (hr_pos : 0 < 1 + r) :
    let q := (1 + r - d) / (u - d)
    (q * (S₀ * u) + (1 - q) * (S₀ * d)) / (1 + r) = S₀ := by
  sorry
```

```rocq
Lemma discounted_martingale : forall S0 u d r : R,
  d < u -> d < 1 + r -> 1 + r < u -> 0 < 1 + r ->
  let q := (1 + r - d) / (u - d) in
  (q * (S0 * u) + (1 - q) * (S0 * d)) / (1 + r) = S0.
Proof.
  (* your proof here *)
Admitted.
```

The proof expands $q$ and simplifies. `field_simp` clears the denominators, and `ring` closes the resulting polynomial identity.

**Risk-neutral vs. real-world measure.** The martingale property holds under the *risk-neutral* measure $\mathbb{Q}$, not under the real-world measure $\mathbb{P}$. Under $\mathbb{P}$, stocks typically have positive expected return (a risk premium), so the discounted price process has upward drift — it is *not* a martingale under $\mathbb{P}$. The risk-neutral measure $\mathbb{Q}$ is a mathematical device that reweights probabilities so that discounted prices become martingales, enabling pricing by expectation.

## Why Martingales Matter for Finance

The martingale perspective unifies several key results:

- **Risk-neutral pricing formula:** The price of any derivative is $V_0 = E^{\mathbb{Q}}[\text{payoff} / (1+r)^n]$. This is simply the martingale property applied to the discounted price process.
- **No-arbitrage and martingale measures:** The First Fundamental Theorem of Asset Pricing (next lesson) states that no-arbitrage is *equivalent* to the existence of a martingale measure. This deep connection is the reason martingales are central to finance.
- **Convergence theorems:** Martingale convergence theorems describe the long-run behavior of prices and portfolios, providing theoretical foundations for questions about market stability.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_mart_001_lean4` | Symmetric random walk one-step martingale property | Substitute $p = 1/2$, `ring` |
| `fin_mart_002_lean4` | Discounted binomial price is a martingale under Q | Expand $q$, `field_simp`, `ring` |

The martingale concept captures the idea that in a "fair" market (under the risk-neutral measure), prices have no predictable drift after discounting. This is not a statement about reality -- real prices do have drift under $\mathbb{P}$ -- but rather about the existence of a *valuation measure* under which discounted prices are fair games.

## Further Reading

- D. Williams, *Probability with Martingales*, Cambridge University Press, 1991.
- S. E. Shreve, *Stochastic Calculus for Finance I*, Springer, 2004, Chapter 2.
- Mathlib documentation: `Probability.Martingale`, `MeasureTheory.Filtration`, `MeasureTheory.condexp`.
