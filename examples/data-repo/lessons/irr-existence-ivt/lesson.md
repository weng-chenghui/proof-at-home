---
lesson_id: irr-existence-ivt
title: "Time Value of Money — Existence of IRR via IVT"
topic: mathematical-finance
difficulty: medium
conjecture_ids: [fin_irr_002_lean4, fin_irr_002_rocq, fin_irr_001_lean4, fin_irr_001_rocq]
published: true
ai_annotations:
  - zone: "## Net Present Value"
    context: "Definition of NPV and its role in finance"
    suggestions:
      - "What does NPV measure intuitively?"
      - "Why do we discount future cash flows?"
      - "How does the discount rate affect NPV?"
  - zone: "## Continuity of NPV"
    context: "Proving NPV is continuous using Mathlib"
    suggestions:
      - "Which Mathlib lemmas handle continuity of sums?"
      - "Why is continuity important for applying IVT?"
      - "What happens at r = -1?"
  - zone: "## Existence of IRR"
    context: "Using IVT to prove a root exists"
    suggestions:
      - "Walk me through the IVT argument step by step"
      - "Why do we need the sign-change condition?"
      - "Does IRR always exist for any cash flow?"
---
# Time Value of Money — Existence of IRR via IVT

The Internal Rate of Return (IRR) is one of the most fundamental concepts in finance. It is the discount rate at which the Net Present Value (NPV) of a series of cash flows equals zero. Every capital budgeting textbook introduces IRR, but few ask the question: *does such a rate always exist, and can we prove it rigorously?*

In this lesson, we formalize the existence of IRR using Lean 4 and Mathlib. The key mathematical tool is the **Intermediate Value Theorem** (IVT), applied to the continuous NPV function. We progress through two conjectures: first establishing continuity of NPV, then proving existence of a root.

## Net Present Value

Given a cash flow vector $\mathbf{c} = (c_0, c_1, \ldots, c_n)$ and a discount rate $r > -1$, the **Net Present Value** is defined as:

$$\text{NPV}(r) = \sum_{i=0}^{n} \frac{c_i}{(1+r)^i}$$

The idea is simple: a dollar received in the future is worth less than a dollar today, because you could invest today's dollar and earn a return. The discount factor $1/(1+r)^i$ converts a future cash flow $c_i$ at time $i$ back to its present-day equivalent.

- A **positive NPV** means the investment creates value — the present value of inflows exceeds outflows.
- A **negative NPV** means the investment destroys value.
- The **IRR** is the rate $r^*$ where $\text{NPV}(r^*) = 0$ — the break-even discount rate.

In Lean 4, we represent NPV as a function from $\mathbb{R}$ to $\mathbb{R}$:

```lean4
noncomputable def npv (n : ℕ) (cf : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ i : Fin n, cf i / (1 + r) ^ (i : ℕ)
```

Note that this definition is well-defined for all $r \neq -1$. At $r = 0$, each discount factor is 1, so $\text{NPV}(0) = \sum c_i$. As $r \to \infty$, all terms except $c_0$ vanish because the denominators grow without bound.

## Continuity of NPV

To apply IVT, we first need to show that NPV is **continuous** as a function of the discount rate $r$.

**Conjecture `fin_irr_002_lean4`:** *NPV is continuous in the discount rate.*

```lean4
theorem npv_continuous (n : ℕ) (cf : Fin n → ℝ) :
    Continuous (fun r : ℝ => ∑ i : Fin n, cf i / (1 + r) ^ (i : ℕ)) := by
  sorry
```

```rocq
(** Simplified: NPV of a single cash flow is continuous. *)
Lemma npv_continuous_simple : forall C : R,
  continuity (fun r => C / (1 + r)).
Proof.
  (* your proof here *)
Admitted.
```

### Proof Strategy

Each summand $c_i / (1+r)^i$ is a composition of continuous functions:

1. $r \mapsto 1 + r$ is continuous (continuous addition of a constant).
2. $x \mapsto x^i$ is continuous (`Continuous.pow`).
3. $c_i / x$ is continuous where $x \neq 0$ (`Continuous.div`).

The finite sum of continuous functions is continuous (`continuous_finset_sum`).

The subtlety is that division by $(1+r)^i$ requires $1 + r \neq 0$, i.e., $r \neq -1$. In fact, Lean 4 handles division by zero gracefully (it returns 0), so the function is *defined* everywhere, but the financial interpretation only makes sense for $r > -1$.

## Existence of IRR

Now for the main result. Under what conditions does an IRR exist?

Consider a typical investment: an initial outlay $c_0 < 0$ (you pay money upfront) and total cash flows $\sum c_i > 0$ (the investment is profitable overall in undiscounted terms). Under these conditions:

- **At $r = 0$:** $\text{NPV}(0) = \sum_{i=0}^n c_i > 0$, since each denominator equals 1.
- **As $r \to \infty$:** $\text{NPV}(r) \to c_0 < 0$, since all terms with $i \geq 1$ vanish.

Since NPV is continuous and changes sign on $(0, \infty)$, by the **Intermediate Value Theorem** there exists some $r^* > 0$ with $\text{NPV}(r^*) = 0$.

**Conjecture `fin_irr_001_lean4`:** *Existence of IRR via the Intermediate Value Theorem.*

```lean4
theorem exists_irr (n : ℕ) (cf : Fin (n+1) → ℝ)
    (h_init : cf 0 < 0) (h_total : 0 < ∑ i, cf i)
    (h_neg : ∃ R : ℝ, 0 < R ∧ ∑ i : Fin (n+1), cf i / (1 + R) ^ (i : ℕ) < 0) :
    ∃ r : ℝ, 0 < r ∧ ∑ i : Fin (n+1), cf i / (1 + r) ^ (i : ℕ) = 0 := by
  sorry
```

```rocq
(** Simplified version: NPV changes sign between two rates. *)
Lemma irr_existence_simple : forall C0 C1 : R,
  C0 < 0 -> C1 > 0 -> 0 < C0 + C1 ->
  exists r : R, 0 < r /\ C0 + C1 / (1 + r) = 0.
Proof.
  (* your proof here *)
Admitted.
```

### Proof Strategy

1. **Show $\text{NPV}(0) = \sum c_i > 0$:** Substitute $r = 0$. Every denominator $(1 + 0)^i = 1$, so each term simplifies to $c_i$. The hypothesis `h_total` gives the result.

2. **Obtain $R$ with $\text{NPV}(R) < 0$:** The hypothesis `h_neg` provides an explicit $R > 0$ where $\text{NPV}(R) < 0$. (Economically, for large enough $R$ the heavy discounting makes NPV approach $c_0 < 0$. The limit argument $\text{NPV}(r) \to c_0$ as $r \to \infty$ is non-trivial to formalize, so we take $R$ as a hypothesis.)

3. **Apply IVT:** NPV is continuous on $[0, R]$, positive at 0, and negative at $R$. By `intermediate_value_uIcc`, there exists $r^* \in (0, R)$ with $\text{NPV}(r^*) = 0$.

The Mathlib lemma `IsPreconnected.intermediate_value₂_uIcc` (or related IVT variants) provides the key tool for step 3.

### A Word on Uniqueness

Note that we prove *existence* but not *uniqueness* of the IRR. In general, IRR can be **non-unique** for cash flows with alternating signs. For example, the cash flow $(-1, +3, -2.5)$ has two IRRs. Uniqueness requires additional conditions, such as the cash flow having exactly one sign change.

**Descartes' Rule of Signs.** The NPV equation $\sum c_i / (1+r)^i = 0$ can be rewritten as a polynomial in $x = 1/(1+r)$. Descartes' rule bounds the number of positive real roots by the number of sign changes in the coefficient sequence. For a conventional investment (one initial outflow followed by inflows), there is exactly one sign change, guaranteeing a unique positive IRR.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `fin_irr_002_lean4` | NPV is continuous in $r$ | `continuous_finset_sum`, `Continuous.div`, `Continuous.pow` |
| `fin_irr_001_lean4` | IRR exists when $c_0 < 0$ and $\sum c_i > 0$ | Intermediate Value Theorem on continuous NPV |

The progression mirrors how one builds a mathematical proof: first establish the regularity of the function (continuity), then apply a topological theorem (IVT) to deduce existence. This pattern — *regularity then application* — recurs throughout mathematical finance, from option pricing (continuity of payoff functions) to equilibrium theory (fixed-point theorems).

## Further Reading

- Brealey, Myers, Allen — *Principles of Corporate Finance*, McGraw-Hill.
- Mathlib docs on `Continuous` and `intermediate_value_uIcc`.
- Hairer — *An Introduction to Financial Mathematics*, for the formal treatment of IRR and NPV.
