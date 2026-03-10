---
lesson_id: crr-convergence
title: "CRR Convergence: Binomial to Black-Scholes"
topic: mathematical-finance
difficulty: hard
conjecture_ids: [fin_crr_001_lean4, fin_crr_001_rocq]
published: true
ai_annotations:
  - zone: "## The CRR Parametrization"
    context: "Setting u and d as functions of n to match the continuous-time limit"
    suggestions:
      - "Why do we choose u = exp(sigma * sqrt(T/n))?"
      - "What happens to the risk-neutral probability q_n as n grows?"
      - "How does the CRR parametrization differ from other binomial parametrizations?"
  - zone: "## Convergence to Black-Scholes"
    context: "Central Limit Theorem argument showing the binomial price converges"
    suggestions:
      - "How does the CLT apply to the sum of binomial up/down moves?"
      - "Why does the binomial distribution converge to a normal distribution here?"
      - "What rate does the convergence happen at?"
---
# CRR Convergence: Binomial to Black-Scholes

*Bonus lesson.* The Cox-Ross-Rubinstein (CRR) model bridges discrete and continuous finance. By choosing $u = e^{\sigma\sqrt{T/n}}$ and $d = e^{-\sigma\sqrt{T/n}}$, the $n$-period binomial model converges to the Black-Scholes model as $n \to \infty$. This lesson outlines the convergence argument and discusses the challenges of formalizing it.

## The CRR Parametrization

In an $n$-period binomial model with maturity $T$, the CRR parametrization sets:

$$u_n = e^{\sigma\sqrt{T/n}}, \qquad d_n = e^{-\sigma\sqrt{T/n}} = 1/u_n$$

where $\sigma > 0$ is the volatility. The risk-free rate per period is $r_n = e^{rT/n} - 1$ (continuously compounded), and the risk-neutral probability is:

$$q_n = \frac{e^{rT/n} - d_n}{u_n - d_n}$$

As $n$ grows, the time steps $T/n$ shrink, the up and down factors $u_n, d_n$ converge to 1, and the tree becomes a finer and finer approximation to continuous trading. The stock price after $n$ periods is:

$$S_n = S_0 \cdot u_n^{J} \cdot d_n^{n - J}$$

where $J$ is the number of up-moves, a binomial random variable with parameters $(n, q_n)$.

## The Black-Scholes Formula

The Black-Scholes formula for a European call option with strike $K$ and maturity $T$ is:

$$C_{BS} = S_0 \Phi(d_1) - K e^{-rT} \Phi(d_2)$$

where $\Phi$ is the standard normal CDF and:

$$d_1 = \frac{\ln(S_0/K) + (r + \sigma^2/2)T}{\sigma\sqrt{T}}, \qquad d_2 = d_1 - \sigma\sqrt{T}$$

This formula was derived by Black and Scholes (1973) using continuous-time stochastic calculus. The CRR convergence provides an alternative derivation using only discrete probability.

## Convergence to Black-Scholes

The binomial call price in the $n$-period CRR model is:

$$C_n = e^{-rT} \sum_{j=a}^{n} \binom{n}{j} q_n^j (1 - q_n)^{n-j} \left(S_0 u_n^j d_n^{n-j} - K\right)$$

where $a = \min\{j : S_0 u_n^j d_n^{n-j} > K\}$ is the minimum number of up-moves for the option to finish in the money.

The convergence $C_n \to C_{BS}$ follows from the **Central Limit Theorem**:

1. The log-return $\ln(S_n/S_0) = J \ln(u_n/d_n) + n \ln(d_n)$ is a sum of $n$ independent, identically distributed terms.
2. Each term has mean and variance that scale as $O(1/n)$ and $O(1/n)$ respectively.
3. By the CLT, the normalized sum converges in distribution to a normal random variable with mean $(r - \sigma^2/2)T$ and variance $\sigma^2 T$.
4. The binomial call price, being an expectation of a continuous function of this sum, converges to the Black-Scholes price.

This is the precise sense in which the binomial model "becomes" the Black-Scholes model in the limit.

## Formalization Status

**Conjecture `fin_crr_001_lean4`:** *CRR binomial prices converge to the Black-Scholes price.*

```lean4
/-- Placeholder: CRR convergence to Black-Scholes.
    Full formalization requires the CLT, real exponential properties,
    and careful limit arguments.

    Intended real statement (for when Mathlib CLT matures):
    theorem crr_convergence (S K r σ T : ℝ) (hS : 0 < S) (hK : 0 < K)
        (hσ : 0 < σ) (hT : 0 < T) :
        Filter.Tendsto (fun n => crr_call_price S K r σ T n)
          Filter.atTop (nhds (black_scholes_call S K r σ T))
-/
theorem crr_convergence_statement (S K r σ T : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    True := by trivial
```

```rocq
(** Placeholder: CRR convergence to Black-Scholes in Rocq.
    Full formalization requires the CLT and real analysis libraries. *)
Lemma crr_convergence_statement : forall S K r sigma T : R,
  0 < S -> 0 < K -> 0 < sigma -> 0 < T -> True.
Proof.
  intros. exact I.
Qed.
```

This conjecture is currently a **placeholder** stating `True`. The comment shows the intended real statement: `Filter.Tendsto` of the CRR call price sequence to the Black-Scholes price. A full formalization would require:

- **Central Limit Theorem** in Mathlib (available via `ProbabilityTheory.IdentDistrib` and related results, though the full CLT with Lindeberg condition is still under development).
- **Properties of the real exponential** and logarithm, including Taylor expansions for $e^{x} \approx 1 + x + x^2/2$ as $x \to 0$.
- **Convergence of expectations** under distributional convergence (continuous mapping theorem).
- **Standard normal CDF** $\Phi$ and its properties.

This is a stretch goal that will ship when Mathlib's probability theory library matures sufficiently. The statement serves as a roadmap for future formalization work.

## Summary

| Conjecture | Statement | Status |
|---|---|---|
| `fin_crr_001_lean4` | CRR converges to Black-Scholes | Placeholder (`True`) — see intended statement in comment |

The CRR convergence result is both practically and theoretically important. Practically, it justifies using binomial trees as numerical approximations to Black-Scholes prices. Theoretically, it shows that the continuous-time theory emerges as a limit of the discrete-time theory, providing a rigorous foundation for the Black-Scholes formula without stochastic calculus.

## Further Reading

- J. C. Cox, S. A. Ross, and M. Rubinstein, "Option pricing: A simplified approach," *Journal of Financial Economics*, 1979.
- S. E. Shreve, *Stochastic Calculus for Finance I*, Springer, 2004, Chapter 1, Section 1.7.
- F. Black and M. Scholes, "The pricing of options and corporate liabilities," *Journal of Political Economy*, 1973.
