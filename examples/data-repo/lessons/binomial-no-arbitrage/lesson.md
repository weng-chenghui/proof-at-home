---
lesson_id: binomial-no-arbitrage
title: "Single-Period Binomial Tree & No-Arbitrage"
topic: mathematical-finance
difficulty: medium
conjecture_ids: [fin_binom_001_lean4, fin_binom_001_rocq, fin_binom_002_lean4, fin_binom_002_rocq]
published: true
ai_annotations:
  - zone: "## The Binomial Model"
    context: "Setup and parameters of the single-period binomial model"
    suggestions:
      - "What happens if the no-arbitrage condition is violated?"
      - "Can you walk me through constructing an explicit arbitrage?"
      - "Why do we need both a stock and a bond in the model?"
  - zone: "## Risk-Neutral Pricing"
    context: "Risk-neutral probability and the pricing equation"
    suggestions:
      - "Why is q called a risk-neutral probability?"
      - "How does the pricing formula relate to expected values?"
      - "What is the intuition behind discounting by 1+r?"
  - zone: "## Law of One Price"
    context: "Uniqueness of the replicating portfolio value"
    suggestions:
      - "Why does the Law of One Price follow from no-arbitrage?"
      - "What happens if two portfolios have different initial values but the same payoff?"
      - "How does u != d ensure uniqueness?"
---
# Single-Period Binomial Tree & No-Arbitrage

The single-period binomial model is the simplest non-trivial model of a financial market. Despite its simplicity, it contains all the key ideas of mathematical finance: no-arbitrage, risk-neutral pricing, and the Law of One Price. In this lesson, we formalize these concepts and prove two fundamental results in Lean 4.

## The Binomial Model

We consider a market with two assets observed at two times: $t = 0$ (today) and $t = 1$ (one period later).

**Stock.** The stock has price $S_0 > 0$ at time 0. At time 1, it moves to one of two values:

$$S_1 = \begin{cases} S_0 \cdot u & \text{(up state)} \\ S_0 \cdot d & \text{(down state)} \end{cases}$$

where $u > d > 0$ are the up and down factors.

**Bond.** The risk-free bond pays a fixed return: invest 1 at time 0, receive $1 + r$ at time 1, where $r > -1$ is the risk-free interest rate.

The tree diagram:

```
              S_0 * u    (up state)
             /
    S_0 ----
             \
              S_0 * d    (down state)
```

**No-arbitrage condition.** For the model to be free of arbitrage (risk-free profit), we need:

$$d < 1 + r < u$$

If $1 + r \geq u$, the bond dominates the stock in all states -- sell the stock and buy the bond for a risk-free profit. If $1 + r \leq d$, the stock dominates the bond -- borrow at rate $r$ and buy the stock. In either case, we can construct an explicit arbitrage.

## Risk-Neutral Pricing

Define the **risk-neutral probability** of the up state:

$$q = \frac{(1 + r) - d}{u - d}$$

This is the probability under which the expected return of the stock equals the risk-free rate:

$$q \cdot S_0 u + (1 - q) \cdot S_0 d = S_0 (1 + r)$$

**Conjecture `fin_binom_001_lean4`:** *The risk-neutral probability lies in $(0, 1)$.*

```lean4
theorem binomial_risk_neutral (u d r : ℝ) (hdu : d < u)
    (hr1 : d < 1 + r) (hr2 : 1 + r < u) :
    let q := (1 + r - d) / (u - d); 0 < q ∧ q < 1 := by
  constructor
  · apply div_pos
    · linarith
    · linarith
  · rw [div_lt_one (by linarith : (0 : ℝ) < u - d)]
    linarith
```

```rocq
Lemma binomial_risk_neutral : forall u d r : R,
  d < u -> d < 1 + r -> 1 + r < u ->
  let q := (1 + r - d) / (u - d) in
  0 < q /\ q < 1.
Proof.
  (* your proof here *)
Admitted.
```

The proof breaks into two parts:
- **$q > 0$:** The numerator $(1 + r) - d$ is positive by $d < 1 + r$, and the denominator $u - d$ is positive by $d < u$.
- **$q < 1$:** We need $(1 + r) - d < u - d$, which simplifies to $1 + r < u$.

The no-arbitrage condition $d < 1 + r < u$ is therefore *equivalent* to $q \in (0, 1)$.

**Pricing formula.** Given a derivative with payoff $V_u$ in the up state and $V_d$ in the down state, its unique no-arbitrage price is:

$$V_0 = \frac{q \cdot V_u + (1 - q) \cdot V_d}{1 + r}$$

This is the discounted expected payoff under the risk-neutral measure.

## Law of One Price

The **Law of One Price** states: if two portfolios produce the same payoff in every state, they must have the same initial value. This is a direct consequence of no-arbitrage.

Formally, suppose portfolios $(\Delta_1, B_1)$ and $(\Delta_2, B_2)$ both replicate a derivative with payoff $(V_u, V_d)$:

$$\Delta_1 S_0 u + B_1 (1 + r) = V_u = \Delta_2 S_0 u + B_2 (1 + r)$$
$$\Delta_1 S_0 d + B_1 (1 + r) = V_d = \Delta_2 S_0 d + B_2 (1 + r)$$

**Conjecture `fin_binom_002_lean4`:** *The Law of One Price -- replicating portfolios have the same initial value.*

```lean4
theorem law_of_one_price (u d r Vu Vd : ℝ) (hdu : d < u)
    (hr1 : d < 1 + r) (hr2 : 1 + r < u)
    (Δ₁ B₁ Δ₂ B₂ : ℝ)
    (h1u : Δ₁ * u + B₁ * (1 + r) = Vu) (h1d : Δ₁ * d + B₁ * (1 + r) = Vd)
    (h2u : Δ₂ * u + B₂ * (1 + r) = Vu) (h2d : Δ₂ * d + B₂ * (1 + r) = Vd) :
    Δ₁ + B₁ = Δ₂ + B₂ := by
  sorry
```

```rocq
Lemma law_of_one_price : forall u d r Vu Vd D1 B1 D2 B2 : R,
  d < u ->
  d < 1 + r -> 1 + r < u ->
  D1 * u + B1 * (1 + r) = Vu ->
  D1 * d + B1 * (1 + r) = Vd ->
  D2 * u + B2 * (1 + r) = Vu ->
  D2 * d + B2 * (1 + r) = Vd ->
  D1 + B1 = D2 + B2.
Proof.
  (* your proof here *)
Admitted.
```

The proof proceeds by subtracting the down-state equation from the up-state equation. This eliminates $B$, leaving $(\Delta_1 - \Delta_2) \cdot (u - d) = 0$. Since $u \neq d$ (from `hdu`), we get $\Delta_1 = \Delta_2$. Substituting back gives $B_1 = B_2$, so the initial portfolio values are equal.

### Arbitrage When the Condition Fails

What happens when the no-arbitrage condition $d < 1 + r < u$ is violated? We can construct explicit arbitrage portfolios.

**Case 1: $1 + r \geq u$ (bond dominates stock).** The bond return exceeds even the best stock outcome. Strategy: short one share of stock (receive $S_0$), invest the proceeds in bonds. At time 1:
- Up state: bond pays $S_0(1+r) \geq S_0 u$, stock costs $S_0 u$ to buy back. Profit $\geq 0$.
- Down state: bond pays $S_0(1+r) \geq S_0 u > S_0 d$, stock costs $S_0 d$. Profit $> 0$.

Zero initial cost, non-negative payoff in all states, strictly positive in at least one: arbitrage.

**Case 2: $d \geq 1 + r$ (stock dominates bond).** Even the worst stock outcome beats the bond. Strategy: borrow $S_0$ at rate $r$ (sell bond), buy one share. At time 1:
- Up state: stock is worth $S_0 u > S_0 d \geq S_0(1+r)$, repay $S_0(1+r)$. Profit $> 0$.
- Down state: stock is worth $S_0 d \geq S_0(1+r)$, repay $S_0(1+r)$. Profit $\geq 0$.

Again, this is an arbitrage.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_binom_001_lean4` | Risk-neutral probability $q \in (0,1)$ | Positivity of numerator/denominator, `div_lt_one` |
| `fin_binom_002_lean4` | Law of One Price | Subtract equations, use $u \neq d$ and $S_0 \neq 0$ |

The single-period binomial model, despite its simplicity, captures the essential logic of derivative pricing: the no-arbitrage condition pins down a unique risk-neutral probability, which in turn determines a unique price for any derivative. In the next lessons, we explore replication (delta hedging) and extend the model to multiple periods.

## Further Reading

- S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*, Springer, 2004.
- J. C. Cox, S. A. Ross, and M. Rubinstein, "Option pricing: A simplified approach," *Journal of Financial Economics*, 1979.
