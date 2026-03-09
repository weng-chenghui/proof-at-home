---
lesson_id: multi-period-binomial
title: "Multi-Period Binomial & Backward Induction"
topic: mathematical-finance
difficulty: hard
conjecture_ids: [fin_multi_001, fin_multi_002]
published: true
ai_annotations:
  - zone: "## Extending to Multiple Periods"
    context: "Multi-period tree structure and recombining property"
    suggestions:
      - "Why does the recombining property keep the tree manageable?"
      - "How many distinct terminal nodes are there after n periods?"
      - "How do we represent the tree in Lean 4 using Fin?"
  - zone: "## Backward Induction"
    context: "Recursive pricing from terminal payoffs back to time zero"
    suggestions:
      - "Walk me through backward induction on a two-period example"
      - "Why does backward induction give the unique no-arbitrage price?"
      - "How does the recursion relate to the risk-neutral expectation?"
  - zone: "## Self-Financing Strategies"
    context: "The wealth process and self-financing condition"
    suggestions:
      - "What does self-financing mean economically?"
      - "Why is the self-financing condition important for no-arbitrage pricing?"
      - "Can you show a concrete example of rebalancing a portfolio?"
---
# Multi-Period Binomial & Backward Induction

Real financial markets evolve over multiple periods. We extend the single-period binomial model to $n$ periods, where the stock price follows a recombining tree. The key insight: we can price derivatives by working backward from expiry, using single-period pricing at each node.

## Extending to Multiple Periods

In the multi-period binomial model, time runs from $t = 0$ to $t = n$. At each step, the stock price either goes up by factor $u$ or down by factor $d$:

```
                            S₀u³
                          /
                    S₀u²
                  /       \
            S₀u            S₀u²d
          /     \         /
    S₀              S₀ud
          \     /         \
            S₀d            S₀ud²
                  \       /
                    S₀d²
                          \
                            S₀d³
```

After $n$ periods, the stock price is $S_0 u^j d^{n-j}$ where $j$ counts the number of up moves, $j \in \{0, 1, \ldots, n\}$.

**Recombining property.** The tree is recombining because $u \cdot d = d \cdot u$ (multiplication commutes). An up move followed by a down move gives the same price as down-then-up. This means the number of distinct terminal nodes is $n + 1$ (not $2^n$), making computation tractable.

**Lean 4 representation.** We index terminal nodes using `Fin (n + 1)`, where the index $j$ represents the node with price $S_0 u^j d^{n-j}$:

```lean4
def terminalPrice (S₀ u d : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  S₀ * u ^ (j : ℕ) * d ^ (n - (j : ℕ))
```

## Backward Induction

To price a derivative with terminal payoff $V_n(j)$ at each node $j$, we work backward through the tree.

**Terminal condition.** At time $n$:

$$V_n(j) = \text{payoff}(S_0 u^j d^{n-j}), \quad j = 0, 1, \ldots, n$$

**Recursive step.** At each earlier time $k$, node $j$:

$$V_k(j) = \frac{q \cdot V_{k+1}(j+1) + (1 - q) \cdot V_{k+1}(j)}{1 + r}$$

where $q = (1 + r - d)/(u - d)$ is the risk-neutral probability from the single-period model.

This recursion computes the no-arbitrage price by treating each node as a single-period model and applying risk-neutral pricing locally.

**Conjecture `fin_multi_001`:** *Backward induction gives the unique no-arbitrage price.*

```lean4
theorem backward_induction_price (u d r : ℝ) (hdu : d < u)
    (hr1 : d < 1 + r) (hr2 : 1 + r < u)
    (n : ℕ) (payoff : Fin (n + 1) → ℝ) :
    let q := (1 + r - d) / (u - d)
    let price : Fin (n + 1) → ℝ := fun k =>
      (q * payoff ⟨min (k + 1) n, by omega⟩ + (1 - q) * payoff ⟨k, by omega⟩) / (1 + r)
    ∀ k : Fin (n + 1), price k = (q * payoff ⟨min (k + 1) n, by omega⟩ + (1 - q) * payoff ⟨k, by omega⟩) / (1 + r) := by
  sorry
```

This is a definitional warm-up: the statement says the locally-defined `price` function equals its own definition. While trivial (provable by `intro k; rfl`), it sets up the notation for the real backward induction proof. The substantive content — that this recursion gives the unique no-arbitrage price — requires showing that each step corresponds to the single-period replication argument.

**Indexing convention.** We index terminal nodes by `Fin (n + 1)` where index $j$ represents the node reached after $j$ up-moves (and $n - j$ down-moves). At each backward step, node $j$ at time $k$ has successors $j$ (down) and $j + 1$ (up) at time $k + 1$. The `min (k + 1) n` bound handles the edge case at the boundary of the tree.

## Self-Financing Strategies

A **trading strategy** specifies, at each time $k$, the number of shares $\Delta_k$ and bonds $B_k$ held in the portfolio. A strategy is **self-financing** if portfolio rebalancing at each time step requires no injection or withdrawal of cash.

Formally, the portfolio value at time $k$ before rebalancing is:

$$W_k = \Delta_k \cdot S_k + B_k \cdot (1 + r)$$

The self-financing condition requires that the cost of the new portfolio equals the value of the old one:

$$\Delta_{k+1} \cdot S_k + B_{k+1} = \Delta_k \cdot S_k + B_k$$

Rearranging:

$$(\Delta_{k+1} - \Delta_k) \cdot S_k = (B_k - B_{k+1})$$

The proceeds from selling $(\Delta_k - \Delta_{k+1})$ shares at price $S_k$ exactly fund the change in bond holdings, and vice versa.

**Conjecture `fin_multi_002`:** *The self-financing portfolio identity.*

```lean4
theorem self_financing (Δ_old Δ_new B_old B_new S r : ℝ)
    (h_sf : Δ_new * S + B_new * (1 + r) = Δ_old * S + B_old * (1 + r)) :
    (Δ_new - Δ_old) * S = (B_old - B_new) * (1 + r) := by
  linarith
```

The proof follows directly from rearranging the self-financing condition.

## The Binomial Pricing Formula

By unrolling the backward induction recursion, we obtain the **closed-form binomial pricing formula**:

$$V_0 = \frac{1}{(1+r)^n} \sum_{j=0}^{n} \binom{n}{j} q^j (1-q)^{n-j} \cdot \text{payoff}(S_0 u^j d^{n-j})$$

This has a beautiful probabilistic interpretation: $V_0$ is the **expected payoff under the risk-neutral measure** $\mathbb{Q}$, discounted at the risk-free rate. Under $\mathbb{Q}$, the number of up moves follows a Binomial$(n, q)$ distribution.

**Connection to Black-Scholes.** As $n \to \infty$ with appropriate scaling ($u = e^{\sigma\sqrt{\Delta t}}$, $d = e^{-\sigma\sqrt{\Delta t}}$, $r_{\Delta t} = r \Delta t$), the binomial formula converges to the Black-Scholes formula. This limit theorem, due to Cox, Ross, and Rubinstein (1979), provides both a theoretical justification for Black-Scholes and a practical numerical method.

**Example: Two-period European call.** With $S_0 = 100$, $u = 1.1$, $d = 0.9$, $r = 0.05$, $K = 100$:

- Terminal prices (indexed by up-count $j$): $S_0 d^2 = 81$ ($j=0$), $S_0 ud = 99$ ($j=1$), $S_0 u^2 = 121$ ($j=2$)
- Call payoffs: $V_2(0) = \max(81 - 100, 0) = 0$, $V_2(1) = \max(99 - 100, 0) = 0$, $V_2(2) = \max(121 - 100, 0) = 21$
- Risk-neutral probability: $q = (1.05 - 0.9)/(1.1 - 0.9) = 0.75$
- **Step 1 (backward from $t=2$ to $t=1$):**
  - $V_1(1) = (q \cdot V_2(2) + (1-q) \cdot V_2(1))/1.05 = (0.75 \cdot 21 + 0.25 \cdot 0)/1.05 = 15$
  - $V_1(0) = (q \cdot V_2(1) + (1-q) \cdot V_2(0))/1.05 = (0.75 \cdot 0 + 0.25 \cdot 0)/1.05 = 0$
- **Step 2 (backward from $t=1$ to $t=0$):**
  - $V_0 = (q \cdot V_1(1) + (1-q) \cdot V_1(0))/1.05 = (0.75 \cdot 15 + 0.25 \cdot 0)/1.05 \approx 10.71$

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_multi_001` | Backward induction consistency | `field_simp` |
| `fin_multi_002` | Self-financing identity | `nlinarith` |

The multi-period binomial model extends single-period pricing via backward induction, with each node treated as an independent single-period problem. The self-financing condition ensures that hedging strategies require no external cash flows. The closed-form binomial pricing formula reveals the deep connection between no-arbitrage pricing and expectation under the risk-neutral measure.

## Further Reading

- S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*, Springer, 2004, Chapter 1.
- J. C. Cox, S. A. Ross, and M. Rubinstein, "Option pricing: A simplified approach," *Journal of Financial Economics*, 7(3):229--263, 1979.
- S. R. Pliska, *Introduction to Mathematical Finance: Discrete Time Models*, Blackwell, 1997.
