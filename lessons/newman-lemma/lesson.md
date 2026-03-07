---
lesson_id: newman-lemma
title: "Newman's Lemma: From Local to Global Confluence"
topic: rewriting-systems
difficulty: hard
conjecture_ids: [newman_001, newman_002, newman_003]
published: true
ai_annotations:
  - zone: "## Abstract Reduction Systems"
    context: "Foundational definitions of reduction, confluence, and termination"
    suggestions:
      - "What is the difference between confluence and local confluence?"
      - "Can you give a concrete example of a reduction system?"
      - "Why does termination matter for confluence?"
  - zone: "## Building the Proof"
    context: "The proof strategy for Newman's lemma using well-founded induction"
    suggestions:
      - "Walk me through the well-founded induction step"
      - "Why do we need to convert between clos_refl_trans and clos_refl_trans_1n?"
      - "What goes wrong if we try ordinary induction instead?"
  - zone: "## The Counterexample"
    context: "Why local confluence without termination is insufficient"
    suggestions:
      - "Can you draw the diamond diagram for this counterexample?"
      - "What other properties can rescue confluence without termination?"
---
# Newman's Lemma: From Local to Global Confluence

Newman's lemma is one of the fundamental results in the theory of abstract reduction systems. It tells us that for terminating systems, *local* confluence (one-step divergences can be rejoined) implies *global* confluence (multi-step divergences can be rejoined). This is a powerful result because local confluence is often much easier to check.

In this lesson, we build toward a machine-checked proof of Newman's lemma in Rocq, progressing through three conjectures of increasing difficulty.

## Abstract Reduction Systems

An **abstract reduction system** (ARS) is a set $A$ with a binary relation $R$ on $A$, written $a \to b$ when $R(a, b)$ holds. We think of $\to$ as a "computation step" or "rewrite rule."

The **reflexive-transitive closure** $\to^*$ extends $\to$ to zero or more steps. In Rocq, this is `clos_refl_trans A R`.

Key properties:

- **Confluence (CR):** If $a \to^* b$ and $a \to^* c$, then there exists $d$ with $b \to^* d$ and $c \to^* d$.
- **Local confluence (WCR):** If $a \to b$ and $a \to c$ (single steps), then there exists $d$ with $b \to^* d$ and $c \to^* d$.
- **Termination (SN):** There are no infinite reduction sequences. Equivalently, the *reverse* relation is well-founded.

$$\text{CR: } a \to^* b \text{ and } a \to^* c \implies \exists d.\; b \to^* d \wedge c \to^* d$$

$$\text{WCR: } a \to b \text{ and } a \to c \implies \exists d.\; b \to^* d \wedge c \to^* d$$

Confluence is also called the **Church-Rosser property**. It guarantees that the order of evaluation doesn't matter -- all paths lead to the same result.

## Conjecture 1: Transitivity of Reflexive-Transitive Closure

Before tackling confluence, we need a basic fact: the reflexive-transitive closure is transitive. If $x \to^* y$ and $y \to^* z$, then $x \to^* z$.

**Conjecture `newman_001`:** *The reflexive-transitive closure is transitive.*

```rocq
Lemma clos_rt_trans : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans A R x y -> clos_refl_trans A R y z -> clos_refl_trans A R x z.
```

This is proved by induction on the derivation of `clos_refl_trans A R x y`. The three cases correspond to the constructors of `clos_refl_trans`:

1. **`rt_step`:** One step $x \to y$, then chain with $y \to^* z$.
2. **`rt_refl`:** $x = y$, so $x \to^* z$ is just the second hypothesis.
3. **`rt_trans`:** $x \to^* w \to^* y$; apply the inductive hypothesis twice.

## Conjecture 2: Confluence Implies Joinability

The second conjecture establishes that confluence is precisely the joinability of all pairs reachable from a common ancestor.

**Conjecture `newman_002`:** *If $R$ is confluent, then for any $b$ and $c$ both reachable from $a$, there exists a common reduct.*

```rocq
Lemma confluence_joinable :
  forall a b c, clos_refl_trans A R a b -> clos_refl_trans A R a c ->
  CR -> exists d, clos_refl_trans A R b d /\ clos_refl_trans A R c d.
```

This follows directly from unfolding the definition of CR. Its purpose is to build comfort with the diamond-shaped reasoning that pervades the Newman's lemma proof.

## The Counterexample

Before proving Newman's lemma, it's important to understand *why* termination is necessary. Consider the following ARS:

$$a \to b, \quad a \to c, \quad b \to a, \quad c \to a$$

This system is locally confluent: the only divergence is $a \to b$ and $a \to c$, and both $b$ and $c$ reduce back to $a$ (hence to each other via $a$). But it is **not** terminating -- we have the cycle $a \to b \to a \to b \to \cdots$.

Now extend the system:

$$a \to b, \quad a \to c, \quad b \to a, \quad c \to a, \quad b \to d, \quad c \to e$$

Here $b$ and $c$ reduce to $d$ and $e$ respectively, but $d$ and $e$ have no common reduct. The system is still locally confluent (check each one-step divergence), but **not** confluent. The non-termination allows reductions to "escape" before confluence can catch them.

## Building the Proof

**Conjecture `newman_003`:** *Newman's Lemma -- if $R$ is terminating and locally confluent, then $R$ is confluent.*

```rocq
Lemma newman : well_founded (transp A R) -> WCR -> CR.
```

The key idea is **well-founded induction**. Since $R$ is terminating, the reverse relation `transp A R` is well-founded, and we can do induction on it via `Acc` (accessibility).

### Proof Strategy

Given $a \to^* b$ and $a \to^* c$, we prove there exists a common reduct $d$ by well-founded induction on $a$.

1. **Decompose** using `clos_refl_trans_1n` to get the first step: either $a = b$ (trivial) or $a \to a_1 \to^* b$.

2. **Similarly decompose** $a \to^* c$: either $a = c$ (trivial) or $a \to a_2 \to^* c$.

3. **Apply WCR** to the one-step divergence $a \to a_1$ and $a \to a_2$, getting $d$ with $a_1 \to^* d$ and $a_2 \to^* d$.

4. **Apply IH to $a_1$** (which is accessible since $a \to a_1$): from $a_1 \to^* b$ and $a_1 \to^* d$, get $e$ with $b \to^* e$ and $d \to^* e$.

5. **Chain:** $a_2 \to^* d \to^* e$, so $a_2 \to^* e$.

6. **Apply IH to $a_2$** (accessible since $a \to a_2$): from $a_2 \to^* e$ and $a_2 \to^* c$, get $f$ with $e \to^* f$ and $c \to^* f$.

7. **Conclude:** $b \to^* e \to^* f$ and $c \to^* f$.

The proof is a beautiful example of how well-founded induction lets us reason about terminating computations -- each recursive call is on a "smaller" element (one step forward in the reduction).

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `newman_001` | $\to^*$ is transitive | Induction on `clos_refl_trans` |
| `newman_002` | Confluence $\Rightarrow$ joinability | Unfold definition |
| `newman_003` | SN + WCR $\Rightarrow$ CR | Well-founded induction on `Acc` |

Newman's lemma is widely used in term rewriting, lambda calculus, and automated theorem proving. For example, it underlies the proof that the simply-typed lambda calculus is confluent (since it is both terminating and locally confluent). In Knuth-Bendix completion, checking local confluence of a terminating rewrite system suffices to establish global confluence.

## Further Reading

- F. Baader and T. Nipkow, *Term Rewriting and All That*, Cambridge University Press, 1998.
- M. H. A. Newman, "On theories with a combinatorial definition of equivalence," *Annals of Mathematics*, 1942.
- G. Huet, "Confluent reductions: Abstract properties and applications to term rewriting systems," *JACM*, 1980.
