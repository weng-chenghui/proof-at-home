---
lesson_id: crn-stoichiometry
title: "Atomicity & Conservation Laws (Stoichiometry)"
topic: chemical-reaction-networks
difficulty: easy
conjecture_ids: [crn_stoich_001, crn_stoich_002]
published: true
ai_annotations:
  - zone: "## The Stoichiometric Matrix"
    context: "Defining reactions as vectors and assembling the stoichiometric matrix"
    suggestions:
      - "How do we encode 2H₂ + O₂ → 2H₂O as a vector?"
      - "What does each column of the stoichiometric matrix represent?"
      - "Can you show how to build the matrix for a multi-reaction network?"
  - zone: "## Conservation Laws via the Left Nullspace"
    context: "Why left-nullspace membership implies element conservation"
    suggestions:
      - "What is the left nullspace geometrically?"
      - "Why does aᵀ · S = 0 mean element a is conserved?"
      - "Can you show that both H and O are conserved in water formation?"
---
# Atomicity & Conservation Laws (Stoichiometry)

Chemistry obeys strict bookkeeping: atoms are neither created nor destroyed. In this lesson, we formalize this intuition using linear algebra. The key object is the **stoichiometric matrix**, and the key insight is that an element is conserved if and only if its atom-count vector lies in the **left nullspace** of this matrix.

## Chemical Reactions as Vectors

Consider the water formation reaction:

$$2\text{H}_2 + \text{O}_2 \to 2\text{H}_2\text{O}$$

We track three species: H₂, O₂, and H₂O. The **reaction vector** records the net change in each species:

$$\nu = (-2, -1, 2)^T$$

meaning: 2 molecules of H₂ are consumed, 1 molecule of O₂ is consumed, and 2 molecules of H₂O are produced.

## The Stoichiometric Matrix

For a network with $m$ species and $r$ reactions, the **stoichiometric matrix** $S \in \mathbb{R}^{m \times r}$ has column $j$ equal to the reaction vector of reaction $j$. For our single-reaction example:

$$S = \begin{pmatrix} -2 \\ -1 \\ 2 \end{pmatrix}$$

In general, for a network like:

$$\text{H}_2 + \text{Cl}_2 \to 2\text{HCl}, \quad 2\text{H}_2 + \text{O}_2 \to 2\text{H}_2\text{O}$$

the stoichiometric matrix has one column per reaction, and the rows correspond to species (H₂, Cl₂, HCl, O₂, H₂O).

## Atom-Count Vectors

Each element (H, O, Cl, ...) has an **atom-count vector** that records how many atoms of that element are in each molecule of each species.

For the water formation reaction with species (H₂, O₂, H₂O):

- **Hydrogen atom-count vector**: $a_H = (2, 0, 2)$ — H₂ has 2 H-atoms, O₂ has 0, H₂O has 2
- **Oxygen atom-count vector**: $a_O = (0, 2, 1)$ — H₂ has 0 O-atoms, O₂ has 2, H₂O has 1

## Conservation Laws via the Left Nullspace

An element is conserved if the total count of its atoms does not change under any reaction. Mathematically, for atom-count vector $a$:

$$a^T \cdot \nu = 0 \quad \text{for every reaction vector } \nu$$

This is equivalent to:

$$a^T \cdot S = 0$$

i.e., $a$ lies in the **left nullspace** of $S$ (the kernel of $S^T$).

**Hydrogen conservation check:**

$$a_H^T \cdot S = (2, 0, 2) \cdot \begin{pmatrix} -2 \\ -1 \\ 2 \end{pmatrix} = 2 \cdot (-2) + 0 \cdot (-1) + 2 \cdot 2 = -4 + 0 + 4 = 0 \checkmark$$

**Oxygen conservation check:**

$$a_O^T \cdot S = (0, 2, 1) \cdot \begin{pmatrix} -2 \\ -1 \\ 2 \end{pmatrix} = 0 \cdot (-2) + 2 \cdot (-1) + 1 \cdot 2 = 0 - 2 + 2 = 0 \checkmark$$

Both atom-count vectors are in the left nullspace, confirming H and O conservation.

**Conjecture `crn_stoich_001`:** *The H-atom count vector is in the left nullspace of the stoichiometric matrix for water formation.*

```lean4
theorem h_atom_conservation :
    let S : Matrix (Fin 3) (Fin 1) ℤ := !![(-2); (-1); (2)]
    let aH : Fin 3 → ℤ := ![2, 0, 2]
    ∀ j : Fin 1, ∑ i : Fin 3, aH i * S i j = 0 := by
  sorry
```

**Conjecture `crn_stoich_002`:** *The O-atom count vector is in the left nullspace for water formation.*

```rocq
Lemma o_atom_conservation :
  let S := fun i : 'I_3 => (fun j : 'I_1 =>
    [:: -2; -1; 2]`_i) in
  forall j : 'I_1,
    \sum_(i < 3) [:: 0; 2; 1]`_i * S i j = 0.
```

## The General Principle

**Theorem (Conservation Law Criterion).** An element with atom-count vector $a \in \mathbb{R}^m$ is conserved under all reactions of a CRN with stoichiometric matrix $S$ if and only if $a \in \ker(S^T)$.

Note the subtlety: mass balance for a *specific element* requires that element's particular atom-count vector to be in the left nullspace. Not every vector in the left nullspace corresponds to an element — the left nullspace may contain linear combinations that represent "generalized conservation laws" (e.g., Wegscheider conditions).

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `crn_stoich_001` | H-atom vector in left nullspace | `Matrix`, `Fin`, `decide` or `norm_num` |
| `crn_stoich_002` | O-atom vector in left nullspace | MathComp `matrix`, `mxker` |

## Further Reading

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer, 2019.
- D. F. Anderson, *A Proof of the Global Attractor Conjecture in the Single Linkage Class Case*, SIAM J. Appl. Math., 2011.
