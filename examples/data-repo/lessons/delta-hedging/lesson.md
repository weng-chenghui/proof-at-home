---
lesson_id: delta-hedging
title: "Delta Hedging & Market Completeness"
topic: mathematical-finance
difficulty: medium
conjecture_ids: [fin_delta_001_lean4, fin_delta_001_rocq]
published: true
ai_annotations:
  - zone: "## The Replicating Portfolio"
    context: "Constructing the hedge ratio Delta and bond position B"
    suggestions:
      - "How do we solve the system of two equations for Delta and B?"
      - "Why is u != d required for the replicating portfolio to exist?"
      - "Can you show a numerical example of computing Delta?"
  - zone: "## Market Completeness"
    context: "Every contingent claim is attainable in the binomial model"
    suggestions:
      - "What does it mean for a market to be complete?"
      - "How does completeness relate to the uniqueness of the risk-neutral measure?"
      - "Can you give an example of an incomplete market?"
---
# Delta Hedging & Market Completeness

In the previous lesson, we saw that no-arbitrage determines the risk-neutral probability. Now we show something stronger: any derivative payoff can be perfectly replicated by a portfolio of stock and bond. This is the concept of market completeness, and the key quantity is the **delta** -- the number of shares needed to hedge the derivative.

## The Replicating Portfolio

Consider a derivative that pays $V_u$ in the up state and $V_d$ in the down state. We want to find a portfolio consisting of $\Delta$ shares of stock and $B$ units of bond that replicates the derivative payoff in both states:

$$\Delta \cdot S_0 \cdot u + B \cdot (1 + r) = V_u$$
$$\Delta \cdot S_0 \cdot d + B \cdot (1 + r) = V_d$$

This is a system of two linear equations in two unknowns. Subtracting the second from the first:

$$\Delta \cdot S_0 \cdot (u - d) = V_u - V_d$$

Solving:

$$\Delta = \frac{V_u - V_d}{S_0 (u - d)}$$

This is the **hedge ratio** or **delta** of the derivative. Substituting back:

$$B = \frac{V_d - \Delta \cdot S_0 \cdot d}{1 + r} = \frac{u \cdot V_d - d \cdot V_u}{(u - d)(1 + r)}$$

**Conjecture `fin_delta_001_lean4`:** *The delta hedge replicates any derivative payoff.*

```lean4
theorem delta_hedge_replicates (S₀ u d r Vu Vd : ℝ)
    (hS : S₀ ≠ 0) (hdu : d < u) (hr : 1 + r ≠ 0) :
    let Δ := (Vu - Vd) / (S₀ * (u - d))
    let B := (Vd - Δ * S₀ * d) / (1 + r)
    Δ * S₀ * u + B * (1 + r) = Vu ∧ Δ * S₀ * d + B * (1 + r) = Vd := by
  sorry
```

```rocq
Lemma delta_hedge_replicates : forall S0 u d r Vu Vd : R,
  S0 <> 0 -> d < u -> 1 + r <> 0 ->
  let D := (Vu - Vd) / (S0 * (u - d)) in
  let B := (Vd - D * S0 * d) / (1 + r) in
  D * S0 * u + B * (1 + r) = Vu /\
  D * S0 * d + B * (1 + r) = Vd.
Proof.
  (* your proof here *)
Admitted.
```

The proof is pleasingly short: once we unfold the definitions of $\Delta$ and $B$, the tactic `field_simp` clears the denominators and `ring` verifies the resulting polynomial identities. This is a case where the algebra is straightforward but tedious by hand -- exactly the kind of verification where a proof assistant shines.

## Market Completeness

A market is **complete** if every contingent claim (i.e., every possible payoff) can be replicated by a trading strategy using the available assets.

In the single-period binomial model, any payoff $(V_u, V_d) \in \mathbb{R}^2$ can be replicated by the portfolio $(\Delta, B)$ constructed above. The replicating portfolio always exists and is unique, provided:

- $u \neq d$ (the stock price actually moves)
- $S_0 \neq 0$ (the stock has positive price)
- $1 + r \neq 0$ (the bond is non-degenerate)

From a linear algebra perspective, the **payoff matrix**

$$M = \begin{pmatrix} S_0 u & 1 + r \\ S_0 d & 1 + r \end{pmatrix}$$

has determinant $S_0 (u - d)(1 + r)$, which is nonzero under our assumptions. Therefore $M$ has full rank, and the system $M \begin{pmatrix} \Delta \\ B \end{pmatrix} = \begin{pmatrix} V_u \\ V_d \end{pmatrix}$ always has a unique solution.

**Completeness and uniqueness of pricing.** Market completeness implies that the risk-neutral measure is unique. In an incomplete market, there are multiple risk-neutral measures, leading to a range of no-arbitrage prices rather than a single price. The binomial model is complete precisely because we have two states and two assets.

## The Delta

The quantity $\Delta = (V_u - V_d) / (S_0(u - d))$ has a natural interpretation: it measures the **sensitivity** of the derivative value to changes in the stock price.

**Example: European call option.** A call with strike $K$ has payoff:

$$V_u = \max(S_0 u - K, 0), \quad V_d = \max(S_0 d - K, 0)$$

If the call is in the money in the up state but out of the money in the down state ($S_0 u > K > S_0 d$), then:

$$\Delta = \frac{S_0 u - K - 0}{S_0(u - d)} = \frac{S_0 u - K}{S_0(u - d)}$$

Note that $0 < \Delta < 1$ for a call: you hold a fractional share to hedge.

**Delta hedging in practice.** In multi-period models and continuous time, $\Delta$ changes as the stock price moves. A trader who has sold a derivative must continuously rebalance the hedging portfolio to maintain the correct delta. This process is called **dynamic delta hedging** and is the foundation of modern options market making.

### Delta for Different Instruments

The delta formula $\Delta = (V_u - V_d) / (S_0(u - d))$ applies to any derivative. Its range depends on the payoff structure:

**European put.** A put with strike $K$ has payoff $V_u = \max(K - S_0 u, 0)$, $V_d = \max(K - S_0 d, 0)$. Since $V_u \leq V_d$ (the put pays more when the stock falls), we have $V_u - V_d \leq 0$ and thus $\Delta \leq 0$. When the put is in the money in the down state but out of the money in the up state ($S_0 d < K < S_0 u$):

$$\Delta = \frac{0 - (K - S_0 d)}{S_0(u - d)} = \frac{S_0 d - K}{S_0(u - d)} \in [-1, 0]$$

To hedge a short put, you *sell* shares (negative delta).

**Digital (binary) call.** A digital call pays 1 if $S_1 > K$ and 0 otherwise. When $S_0 d < K < S_0 u$:

$$\Delta = \frac{1 - 0}{S_0(u - d)} = \frac{1}{S_0(u - d)}$$

The digital delta is always positive and inversely proportional to $S_0(u - d)$. As $u - d$ shrinks (finer tree), the digital delta grows — reflecting the sharp discontinuity in the digital payoff.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_delta_001_lean4` | Delta hedge replicates any payoff | `field_simp`, `ring` |

The replicating portfolio formula gives us both a pricing method (the initial cost $\Delta S_0 + B$ is the no-arbitrage price) and a hedging strategy (hold $\Delta$ shares and $B$ bonds). Market completeness ensures that this works for every possible derivative payoff.

## Further Reading

- J. C. Hull, *Options, Futures, and Other Derivatives*, Pearson, 2022.
- S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*, Springer, 2004.
