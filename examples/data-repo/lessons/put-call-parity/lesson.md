---
lesson_id: put-call-parity
title: "Static Replication & Put-Call Parity"
topic: mathematical-finance
difficulty: easy
conjecture_ids: [fin_pcp_002, fin_pcp_001]
published: true
ai_annotations:
  - zone: "## Options and Payoffs"
    context: "Definition of call and put option payoffs"
    suggestions:
      - "What is the difference between a call and a put?"
      - "Why do we use max(S-K, 0) instead of S-K?"
      - "When would you buy a call vs. a put?"
  - zone: "## Put-Call Parity"
    context: "The fundamental relationship between call and put payoffs"
    suggestions:
      - "Why must these two portfolios have the same price?"
      - "What is the Law of One Price?"
      - "Can you show this with concrete numbers?"
  - zone: "## Proving It in Rocq"
    context: "Formalizing the proof using case analysis and lra"
    suggestions:
      - "Why do we case split on S vs K?"
      - "How does Rmax work in Rocq?"
      - "What does the lra tactic do?"
---
# Static Replication & Put-Call Parity

Put-call parity is one of the simplest and most elegant results in mathematical finance. It relates the payoffs of European call and put options through a pure algebraic identity — no probability theory or stochastic calculus required. The argument relies only on the definition of $\max$ and basic arithmetic.

This makes it an ideal first formal verification exercise: the mathematics is elementary, but the result is financially significant. In this lesson, we formalize put-call parity in Rocq using case analysis and the `lra` tactic.

## Options and Payoffs

A **European call option** with strike price $K$ gives the holder the right (but not the obligation) to *buy* the underlying asset at price $K$ at expiry. A **European put option** gives the right to *sell* at price $K$.

At expiry, if the spot price of the underlying is $S$:

- **Call payoff:** $\max(S - K,\; 0)$ — you exercise only if $S > K$ (the asset is worth more than the strike).
- **Put payoff:** $\max(K - S,\; 0)$ — you exercise only if $K > S$ (the strike is worth more than the asset).

The $\max$ with zero captures the fact that options confer a *right*, not an obligation. If exercising would lose money, you simply let the option expire worthless.

In Rocq, we define these using `Rmax` from the standard reals library:

```rocq
Definition call_payoff (S K : R) : R := Rmax (S - K) 0.
Definition put_payoff (S K : R) : R := Rmax (K - S) 0.
```

**Conjecture `fin_pcp_002`:** *Call payoff is non-negative.*

```rocq
Lemma call_payoff_nonneg : forall S K : R, 0 <= Rmax (S - K) 0.
Proof.
  (* your proof here *)
Admitted.
```

This warm-up follows directly from the definition of `Rmax`: since $\max(S-K, 0) \geq 0$ by construction (the maximum of anything with zero is at least zero), the result is immediate. In Rocq, `Rmax_r` with the fact that $0 \leq 0$ suffices.

## Put-Call Parity

The key identity: for any spot price $S$ and strike $K$,

$$\max(S - K,\; 0) + K = \max(K - S,\; 0) + S$$

What does this mean financially? Consider two portfolios at expiry:

- **Portfolio A:** Hold one call option and $K$ dollars in cash. Payoff: $\max(S-K, 0) + K$.
- **Portfolio B:** Hold one put option and one share of stock. Payoff: $\max(K-S, 0) + S$.

Both portfolios have the **same payoff in every state of the world**:
- If $S > K$: Portfolio A pays $(S - K) + K = S$. Portfolio B pays $0 + S = S$.
- If $S \leq K$: Portfolio A pays $0 + K = K$. Portfolio B pays $(K - S) + S = K$.

By the **Law of One Price**, two portfolios with identical payoffs in all states must have the same price today. This is an arbitrage argument — if prices differed, you could buy the cheap portfolio and sell the expensive one for a risk-free profit.

**Conjecture `fin_pcp_001`:** *Put-Call Parity: payoff identity.*

```rocq
Lemma put_call_parity : forall S K : R,
  Rmax (S - K) 0 + K = Rmax (K - S) 0 + S.
Proof.
  (* your proof here *)
Admitted.
```

Note that this is a *pointwise* identity — it holds for every value of $S$. No assumptions about probability distributions, volatility, or interest rates are needed at the payoff level.

## Proving It in Rocq

The proof proceeds by **case analysis** on whether $S \leq K$ or $S > K$.

- **Case $S \leq K$:**
  Then $S - K \leq 0$, so $\max(S - K, 0) = 0$.
  And $K - S \geq 0$, so $\max(K - S, 0) = K - S$.
  Left side: $0 + K = K$. Right side: $(K - S) + S = K$. Equal.

- **Case $S > K$:**
  Then $S - K > 0$, so $\max(S - K, 0) = S - K$.
  And $K - S < 0$, so $\max(K - S, 0) = 0$.
  Left side: $(S - K) + K = S$. Right side: $0 + S = S$. Equal.

In Rocq, use `Rle_dec S K` to obtain the case split. In each branch, apply `Rmax_left` or `Rmax_right` to simplify the `Rmax` expressions, then close the arithmetic goal with `lra` (linear real arithmetic).

The `lra` tactic is particularly well-suited here: once the `Rmax` terms are resolved, the remaining goals are linear equalities over the reals, which `lra` handles automatically.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_pcp_002` | Call payoff $\geq 0$ | Definition of `Rmax` |
| `fin_pcp_001` | $\max(S-K,0) + K = \max(K-S,0) + S$ | Case split on $S \leq K$, then `lra` |

This payoff identity extends naturally to the **pricing equation** when we introduce discounting. In continuous time with risk-free rate $r$ and time to expiry $T$:

$$C + Ke^{-rT} = P + S$$

where $C$ is the call price and $P$ is the put price. Our formalization covers the payoff layer; the pricing layer requires an additional ingredient: the **Law of One Price** (a consequence of no-arbitrage), which guarantees that portfolios with identical payoffs in all states must have the same price today. The payoff identity alone is pure algebra; the step from equal payoffs to equal prices is an economic argument that relies on the absence of arbitrage.

## Further Reading

- Hull — *Options, Futures, and Other Derivatives*, Pearson.
- Stoll, "The Relationship Between Put and Call Option Prices," *Journal of Finance*, 1969.
- The Rocq standard library documentation for `Rmax`, `Rle_dec`, and `lra`.
