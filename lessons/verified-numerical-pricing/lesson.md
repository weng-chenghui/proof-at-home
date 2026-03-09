---
lesson_id: verified-numerical-pricing
title: "Verified Numerical Pricing with Interval Arithmetic"
topic: mathematical-finance
difficulty: hard
conjecture_ids: [fin_num_001, fin_num_002]
published: true
ai_annotations:
  - zone: "## The Problem with Floating-Point"
    context: "Rounding errors in financial computation and why they matter"
    suggestions:
      - "How large can floating-point errors get in a typical pricing computation?"
      - "Why is IEEE 754 not exact for decimal fractions?"
      - "What real-world failures have been caused by floating-point errors in finance?"
  - zone: "## Interval Arithmetic in Rocq"
    context: "Flocq and CoqInterval libraries for verified numerical computation"
    suggestions:
      - "How does interval arithmetic differ from ordinary floating-point computation?"
      - "What does the interval tactic in CoqInterval do?"
      - "How does Flocq model IEEE 754 floating-point in Rocq?"
  - zone: "## Verified Bounds on a Call Price"
    context: "Using interval arithmetic to prove rigorous bounds on option prices"
    suggestions:
      - "How tight are the bounds that interval arithmetic produces?"
      - "Could this approach scale to more complex derivatives?"
      - "What is the performance overhead of verified computation?"
---
# Verified Numerical Pricing with Interval Arithmetic

Financial software computes option prices using floating-point arithmetic, which introduces rounding errors. For regulatory and risk management purposes, we need guarantees that computed prices are correct within known bounds. This lesson shows how to use formal verification in Rocq (formerly Coq) to prove rigorous bounds on option prices using interval arithmetic.

## The Problem with Floating-Point

IEEE 754 floating-point arithmetic represents real numbers approximately. Every arithmetic operation may introduce a rounding error, and these errors accumulate through chains of computation.

The Black-Scholes formula involves several operations that are each individually inexact:
- **Exponential** $e^{-rT}$: transcendental function, computed via polynomial approximation
- **Logarithm** $\ln(S/K)$: another transcendental function
- **Square root** $\sigma\sqrt{T}$: irrational for most inputs
- **Normal CDF** $\Phi(d)$: defined as an integral, computed via rational approximation

Each step introduces rounding error. A naive computation might give a call price of $10.4506$ when the true value is $10.4512$. While the relative error is small, in production systems:

- Pricing millions of contracts amplifies small errors into large P&L discrepancies.
- Risk sensitivities (Greeks) involve differences of nearby prices, magnifying relative errors.
- Regulatory models require demonstrable accuracy, not just "probably close enough."

## Interval Arithmetic in Rocq

Instead of computing a single floating-point number that *approximates* the true value, **interval arithmetic** computes an interval $[a, b]$ that is *guaranteed* to contain the true value. Every operation propagates intervals:

$$[a, b] + [c, d] = [a + c, b + d], \qquad [a, b] \times [c, d] = [\min(ac, ad, bc, bd), \max(ac, ad, bc, bd)]$$

The key libraries in the Rocq ecosystem are:

- **Flocq** (Formalization of floating-point computations): Models IEEE 754 arithmetic in Rocq, including rounding modes, special values, and error bounds. Developed by S. Boldo and G. Melquiond.
- **CoqInterval**: Provides an `interval` tactic that automatically proves bounds on real-valued expressions involving standard functions (exp, log, sqrt, etc.).

With CoqInterval, proving that a computation lies in a given interval is nearly automatic:

```rocq
Require Import Interval.Tactic.

Goal (17/10 <= sqrt 3 <= 18/10)%R.
Proof. interval. Qed.
```

The `interval` tactic evaluates the expression using verified interval arithmetic and checks that the result is contained in the stated bounds.

## Verified Bounds on a Call Price

**Conjecture `fin_num_001`:** *Interval bounds on discounted call intrinsic value.*

```rocq
Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** Simplified: verify that the discounted intrinsic value
    S - K/(1+r) is positive for given parameters. *)
Lemma call_price_bound : forall S K r T sigma : R,
  S = 100 -> K = 100 -> r = 5/100 -> T = 1 -> sigma = 20/100 ->
  let price := S - K / (1 + r) in
  0 < price.
Proof.
  (* Substitute concrete values, then lra *)
Admitted.
```

This simplified example verifies that the discounted intrinsic value $S - K/(1+r)$ is positive — a basic sanity check on the price bounds. The full version would define `black_scholes_call` using exp, $\Phi$, and the other components, then use `interval` to automatically verify that the computed price lies within specified bounds.

For the full Black-Scholes formula, the proof structure would be:

```rocq
(* Hypothetical -- requires full Black-Scholes definition *)
Theorem bs_call_bound :
  forall S K r sigma T : R,
    S = 100 -> K = 95 -> r = 5/100 -> sigma = 2/10 -> T = 1 ->
    (927/100 <= black_scholes_call S K r sigma T <= 937/100).
Proof. intros. subst. unfold black_scholes_call. interval. Qed.
```

## Monotonicity: Vega Positivity

Beyond computing bounds, we can prove *qualitative* properties of option prices. One of the most important is **vega positivity**: the call price is increasing in volatility.

$$\text{Vega} = \frac{\partial C}{\partial \sigma} > 0$$

**Intuition:** Higher volatility increases both the upside and downside of the stock. But the call option's payoff $\max(S - K, 0)$ is bounded below by zero, so increased downside doesn't hurt. The net effect of more volatility is a higher option price.

In the binomial model, increasing the up-factor $u$ (with $d = 1/u$) spreads the payoff distribution while keeping the mean fixed. The call payoff in the up state increases, while the down-state payoff remains zero.

**Conjecture `fin_num_002`:** *The call price is increasing in the up-factor.*

```rocq
Require Import Reals.
Open Scope R_scope.

(** Binomial call price as a function of the up-factor. *)
Definition binomial_call (S K u r : R) : R :=
  let d := 1 / u in
  let q := ((1 + r) - d) / (u - d) in
  (q * Rmax (S * u - K) 0 + (1 - q) * Rmax (S * d - K) 0) / (1 + r).

(** The call price increases when u increases (simplified two-state case). *)
Theorem call_increasing_in_u :
  forall S K u1 u2 r : R,
    S > 0 -> K > 0 -> u1 > 1 -> u2 > u1 ->
    0 < r -> 1 / u2 < 1 + r -> 1 + r < u1 ->
    binomial_call S K u1 r <= binomial_call S K u2 r.
Proof.
  intros. unfold binomial_call.
  (* Case analysis on whether each payoff is in the money,
     then algebraic comparison of the pricing expressions. *)
Admitted.
```

The proof requires case analysis on whether $S \cdot u - K$ and $S \cdot d - K$ are positive, followed by algebraic manipulation of the pricing formula. The `Admitted` marks this as an open formalization goal.

## Practical Implications

Verified numerical pricing has several real-world applications:

- **Regulatory compliance:** Basel III and IV require banks to validate their pricing models. Formal proofs provide machine-checkable certificates that a pricing implementation is correct within stated tolerances.
- **Auditing and certification:** Rather than relying on test suites (which can only check finitely many inputs), a formal proof covers *all* inputs in the specified domain.
- **Code extraction:** Rocq's extraction mechanism can produce verified OCaml or Haskell code from proofs. This means the same artifact that *proves* correctness can also *run* in production.

The gap between current practice (testing, code review) and formal verification is large, but interval arithmetic provides a pragmatic middle ground: the proofs are largely automatic, and the guarantees are meaningful.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_num_001` | Interval bounds on discounted call intrinsic value | Substitution, `lra` / CoqInterval `interval` |
| `fin_num_002` | Call price increasing in up-factor | Case analysis, algebraic comparison |

## Further Reading

- S. Boldo and G. Melquiond, *Computer Arithmetic and Formal Proofs*, ISTE Press, 2017.
- Flocq documentation: [https://flocq.gitlabpages.inria.fr/](https://flocq.gitlabpages.inria.fr/)
- CoqInterval documentation: [https://coqinterval.gitlabpages.inria.fr/](https://coqinterval.gitlabpages.inria.fr/)
- IEEE 754-2019, *Standard for Floating-Point Arithmetic*.
