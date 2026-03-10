---
lesson_id: crn-invariance
title: "Stoichiometric Compatibility Classes"
topic: chemical-reaction-networks
difficulty: medium
conjecture_ids: [crn_inv_001_lean4, crn_inv_002_rocq]
published: true
ai_annotations:
  - zone: "## The Stoichiometric Compatibility Class"
    context: "Defining the affine subspace c(0) + im(S)"
    suggestions:
      - "What is an affine subspace geometrically?"
      - "Why does c(t) stay in c(0) + im(S)?"
      - "How does this relate to conservation laws from Module 1?"
  - zone: "## A Concrete Invariant: Carbon Count"
    context: "Carbon atoms cannot be created or destroyed"
    suggestions:
      - "How is carbon conservation related to the left nullspace?"
      - "Can you show the calculation for a specific reaction?"
      - "What other invariants does the stoichiometric compatibility class encode?"
---
# Stoichiometric Compatibility Classes

In Module 1, we proved that certain quantities (atom counts) are conserved. Now we formalize a stronger statement: the entire concentration vector $c(t)$ is confined to an **affine subspace** determined by the initial condition and the stoichiometric matrix. This affine subspace is called a **stoichiometric compatibility class**.

## Dynamics of a CRN

Under mass-action kinetics (or any kinetics consistent with the stoichiometry), the concentration vector $c(t) \in \mathbb{R}^m$ evolves according to:

$$\frac{dc}{dt} = S \cdot v(c)$$

where $S$ is the stoichiometric matrix and $v(c) \in \mathbb{R}^r$ is the vector of reaction rates. The key structural point is that $\dot{c}$ always lies in the **column space** (image) of $S$.

## The Stoichiometric Compatibility Class

Integrating the ODE:

$$c(t) = c(0) + S \int_0^t v(c(\tau)) \, d\tau$$

The integral $\int_0^t v(c(\tau)) \, d\tau$ is some vector in $\mathbb{R}^r$, so $c(t) - c(0) \in \text{im}(S)$. Therefore:

$$c(t) \in c(0) + \text{im}(S)$$

The set $c(0) + \text{im}(S)$ is the **stoichiometric compatibility class** containing $c(0)$. It is an affine subspace of $\mathbb{R}^m$ of dimension $s = \text{rank}(S)$.

**Key consequence:** The dynamics decompose into independent subsystems on parallel affine subspaces. Different initial conditions on the same compatibility class may converge to the same equilibrium; initial conditions on different classes cannot.

## Duality with Conservation Laws

The stoichiometric compatibility class and conservation laws are dual perspectives:

- **Conservation laws** (Module 1): $a^T c(t) = a^T c(0)$ for all $a \in \ker(S^T)$
- **Compatibility class**: $c(t) - c(0) \in \text{im}(S)$

These are equivalent by the fundamental theorem of linear algebra: $\ker(S^T) = \text{im}(S)^\perp$.

## A Concrete Invariant: Carbon Count

Consider the combustion of methane:

$$\text{CH}_4 + 2\text{O}_2 \to \text{CO}_2 + 2\text{H}_2\text{O}$$

Species: (CH₄, O₂, CO₂, H₂O). Stoichiometric matrix:

$$S = \begin{pmatrix} -1 \\ -2 \\ 1 \\ 2 \end{pmatrix}$$

The carbon atom-count vector is $a_C = (1, 0, 1, 0)$ (one C in CH₄, one C in CO₂).

$$a_C^T \cdot S = 1 \cdot (-1) + 0 \cdot (-2) + 1 \cdot 1 + 0 \cdot 2 = 0$$

So $a_C \in \ker(S^T)$, confirming carbon conservation. If we start with 5 carbon atoms (e.g., 5 moles of CH₄), we will always have exactly 5 carbon atoms distributed among CH₄ and CO₂. We cannot reach a state with 10 carbon atoms.

**Conjecture `crn_inv_001_lean4`:** *The concentration vector stays in its stoichiometric compatibility class.*

```lean4
theorem compatibility_class_invariant
    (S : Matrix (Fin m) (Fin r) ℝ) (c₀ : Fin m → ℝ)
    (c : Fin m → ℝ) (w : Fin r → ℝ)
    (h : c = c₀ + S.mulVec w) :
    c - c₀ ∈ Set.range S.mulVec := by
  sorry
```

**Conjecture `crn_inv_002_rocq`:** *Carbon count is invariant under methane combustion.*

```rocq
Lemma carbon_invariant :
  let S := col_mx3 (-1) (-2) 1 2 in
  let aC := row_mx4 1 0 1 0 in
  aC *m S = 0.
```

## Positive Stoichiometric Compatibility Classes

For applications to chemical kinetics, we often restrict to the **positive** stoichiometric compatibility class:

$$(c(0) + \text{im}(S)) \cap \mathbb{R}_{>0}^m$$

This is the set of concentration vectors that are both stoichiometrically compatible with $c(0)$ and have all positive concentrations. The Deficiency Zero Theorem (Module 5) guarantees a unique equilibrium in each positive compatibility class.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `crn_inv_001_lean4` | $c(t) - c(0) \in \text{im}(S)$ | `AffineSubspace`, `Set.range` |
| `crn_inv_002_rocq` | Carbon count is conserved | MathComp matrix multiplication |

## Further Reading

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer, 2019, Chapters 5–6.
- G. Craciun and M. Feinberg, *Multiple equilibria in complex chemical reaction networks: I. The injectivity property*, SIAM J. Appl. Math., 2005.
