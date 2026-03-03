+++
name = "parse-proof-tree"
kind = "parse-tree"
description = "Extract proof structure as a JSON tree with tactics and goal states"
priority = 0
+++

You are a formal verification expert. Your task is to extract the structure of a formal proof as a **JSON proof tree**.

## Proof script ($PROVER)

```
$PROOF_SCRIPT
```

## Context

- **Conjecture title:** $CONJECTURE_TITLE
- **Lemma statement:** $LEMMA_STATEMENT

## Instructions

Analyze the proof script and produce a JSON object representing the proof tree. The tree must capture:

1. **The initial goal** (the lemma statement to prove) as the root node
2. **Each tactic application** as a node, showing:
   - The tactic used
   - The goal state *before* the tactic was applied
   - The goal state *after* the tactic (which becomes the children's goal)
3. **Branching** where tactics split a goal into subgoals (e.g., `split`, `induction`, `case`)
4. **Leaf nodes** where subgoals are discharged (e.g., `reflexivity`, `assumption`, `auto`)

### JSON Schema

```json
{
  "title": "Human-readable proof title",
  "prover": "rocq or lean4",
  "root": {
    "id": "unique string id (e.g. n0, n1, ...)",
    "tactic": "tactic name or 'Goal' for root",
    "goal_before": "goal state before this tactic (LaTeX math, e.g. \\forall n, P(n))",
    "goal_after": "goal state after this tactic (LaTeX math), or 'QED' for leaf",
    "annotation": "brief plain-English explanation of what this step does",
    "children": [ ...child nodes with same structure... ]
  }
}
```

### Rules

- Use LaTeX notation for math expressions in `goal_before` and `goal_after` (e.g., `\\forall`, `\\Rightarrow`, `\\land`)
- The root node's `tactic` should be `"Goal"` and `goal_before` should be the full lemma statement
- Leaf nodes (where subgoals are solved) should have `"children": []` and `goal_after": "\\text{QED}"`
- Keep `annotation` concise: 1 sentence max
- Generate unique `id` values for each node (n0, n1, n2, ...)
- If the proof is linear (no branching), the tree is a single chain
- For induction, create child nodes for the base case and inductive step

### Output

Output ONLY the JSON object — no markdown fences, no commentary, no preamble. The output must be valid JSON.
