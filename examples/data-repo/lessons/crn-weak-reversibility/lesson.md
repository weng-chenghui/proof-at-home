---
lesson_id: crn-weak-reversibility
title: "Graph Topology & Weak Reversibility"
topic: chemical-reaction-networks
difficulty: medium
conjecture_ids: [crn_graph_001, crn_graph_002]
published: true
ai_annotations:
  - zone: "## The Reaction Graph"
    context: "Modeling CRNs as directed graphs with complexes as vertices"
    suggestions:
      - "What is the difference between a species and a complex?"
      - "How do we represent the reaction graph formally?"
      - "Can you give an example with multiple connected components?"
  - zone: "## Weak Reversibility and Strong Connectivity"
    context: "The equivalence between weak reversibility and SCC structure"
    suggestions:
      - "What is the difference between reversibility and weak reversibility?"
      - "Why is strong connectivity the right graph-theoretic notion?"
      - "How does Tarjan's algorithm detect SCCs?"
---
# Graph Topology & Weak Reversibility

Chemical reaction networks have a natural graph structure: **complexes** (combinations of species) are vertices, and **reactions** are directed edges. The topological property of **weak reversibility** — every reaction's effect can be undone by some sequence of reactions — turns out to be central to CRNT.

## Species, Complexes, and Reactions

A **species** is an individual chemical entity (e.g., A, B, C, or H₂, O₂, H₂O). A **complex** is a non-negative integer linear combination of species that appears on one side of a reaction. For example, in:

$$A + B \to C, \quad C \to A + B$$

the complexes are $\{A + B, C\}$ and the reactions are directed edges between them.

In the enzymatic reaction:

$$E + S \rightleftharpoons ES \to E + P$$

the complexes are $\{E + S, ES, E + P\}$ and the reactions are $E + S \to ES$, $ES \to E + S$, and $ES \to E + P$.

## The Reaction Graph

The **reaction graph** (or **complex graph**) of a CRN is a directed graph $G = (V, E)$ where:

- $V$ = set of complexes
- $E$ = set of reactions (directed edges from source complex to product complex)

**Example: A 3-cycle.**

$$A \to B, \quad B \to C, \quad C \to A$$

The reaction graph has vertices $\{A, B, C\}$ and edges forming a directed cycle.

**Linkage classes.** The connected components of the underlying undirected graph are called **linkage classes**. The number of linkage classes $\ell$ appears in the deficiency formula (Module 3).

## Weak Reversibility and Strong Connectivity

A CRN is **reversible** if for every reaction $y \to y'$, the reverse reaction $y' \to y$ also exists.

A CRN is **weakly reversible** if for every reaction $y \to y'$, there exists a sequence of reactions leading from $y'$ back to $y$. In other words, every reaction lies on a directed cycle.

**Theorem.** *A CRN is weakly reversible if and only if every connected component (linkage class) of the reaction graph is strongly connected.*

Recall that a directed graph is **strongly connected** if for every pair of vertices $u, v$, there exists a directed path from $u$ to $v$.

**Example: The 3-cycle is weakly reversible.**

In the network $A \to B \to C \to A$:
- From $B$, we can reach $A$ via $B \to C \to A$ ✓
- From $C$, we can reach $B$ via $C \to A \to B$ ✓
- From $A$, we can reach $C$ via $A \to B \to C$ ✓

Every vertex can reach every other vertex, so the graph is strongly connected, hence the network is weakly reversible.

**Conjecture `crn_graph_001`:** *The 3-cycle A → B → C → A is strongly connected.*

```rocq
(* Uses rocq-community/graph-theory and rocq-community/tarjan *)
Lemma three_cycle_strongly_connected :
  forall (u v : 'I_3),
    connect (fun x y : 'I_3 =>
      ((x == 0%N) && (y == 1%N)) ||
      ((x == 1%N) && (y == 2%N)) ||
      ((x == 2%N) && (y == 0%N)))
    u v.
```

This is a concrete verification: we define the 3-cycle as an adjacency predicate on `'I_3` and prove reachability for all pairs.

**Conjecture `crn_graph_002`:** *In a simple reaction graph, vertex 0 can reach vertex 2.*

```lean4
theorem reachability_0_to_2 :
    let adj : Fin 3 → Fin 3 → Prop := fun i j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
    Relation.TransGen adj 0 2 := by
  sorry
```

## Non-Examples

**An irreversible network.** Consider $A \to B \to C$. There is no path from $C$ back to $A$ or $B$, so this network is not weakly reversible. The single linkage class $\{A, B, C\}$ is not strongly connected.

**A network with two linkage classes.** Consider:

$$A \rightleftharpoons B, \quad C \to D$$

Linkage class 1: $\{A, B\}$ — strongly connected (reversible). Linkage class 2: $\{C, D\}$ — not strongly connected. The network is **not** weakly reversible because linkage class 2 fails.

## Why Weak Reversibility Matters

Weak reversibility is one of the two hypotheses of the **Deficiency Zero Theorem** (Module 5). Networks that are weakly reversible have a kind of "recycling" property: mass flows in cycles rather than accumulating at terminal complexes. This cyclic structure is what allows the existence of positive equilibria.

## Summary

| Conjecture | Statement | Key Technique |
|---|---|---|
| `crn_graph_001` | 3-cycle is strongly connected | `connect`, `tarjan` library, `by decide` |
| `crn_graph_002` | Reachability via `TransGen` | `Relation.TransGen`, constructive path |

## Further Reading

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer, 2019, Chapter 4.
- R. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput., 1972.
