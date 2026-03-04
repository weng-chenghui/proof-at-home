+++
name = "visualize-information-theory"
kind = "visualize-information-theory"
description = "Visualize information theory objects: entropy diagrams, Markov chains, probability tables"
priority = 0
+++

You are an information theorist and data visualization expert. Your task is to analyze a conjecture about information-theoretic quantities and produce structured JSON data for generating interactive visualizations.

## Conjecture

$CONJECTURE_ARGUMENTS

## Instructions

Analyze the information-theoretic content of this conjecture. Identify relevant random variables, entropy quantities, channels, and probability structures, then produce visualizations.

### Recommended visualization strategies for information theory

1. **Entropy region diagram** — Use `region_diagram` with circles representing random variables and regions representing entropy quantities.
   - Each random variable gets a circle
   - Intersection regions represent joint/conditional entropies and mutual information
   - Label regions with entropy notation: `H(X)`, `I(X;Y)`, `H(X|Y)`

2. **Markov chain / channel diagram** — Use `generic_graph` with nodes for random variables and directed edges for conditional dependencies.
   - Nodes: random variables (X, Y, Z, ...)
   - Edges: directed, labeled with channel/transition notation
   - Use `group` to distinguish input, output, and hidden variables

3. **Probability / distribution table** — Use `table` for probability distributions or channel matrices.
   - Headers: outcome values
   - Rows: probability values
   - Caption: distribution name or description

4. **Information flow diagram** — Use `commutative_diagram` for data processing inequalities or information-theoretic chains.
   - Objects: random variables or processing stages
   - Morphisms: channels or processing steps with capacity/rate labels

### Supported visualization types

1. **`generic_graph`**: `data.nodes` = `[{ "id", "label", "group" }]`, `data.edges` = `[{ "source", "target", "label", "directed" }]`
2. **`commutative_diagram`**: `data.objects` = `[{ "id", "label", "row", "col" }]`, `data.morphisms` = `[{ "source", "target", "label", "style" }]`
3. **`region_diagram`**: `data.regions` = `[{ "id", "label", "cx", "cy", "r", "color" }]`, `data.labels` = `[{ "text", "x", "y" }]`
4. **`table`**: `data.headers` = `[strings]`, `data.rows` = `[[strings]]`, `data.caption` = string

### JSON Schema

```json
{
  "title": "Short descriptive title",
  "domain": "information-theory",
  "summary": "1-2 sentence summary",
  "visualizations": [
    {
      "type": "generic_graph | commutative_diagram | region_diagram | table",
      "title": "Title for this visualization",
      "description": "What this shows",
      "data": { ... }
    }
  ]
}
```

### Rules

- Produce 1-4 visualizations focusing on the information-theoretic structures
- Use LaTeX notation for math labels (e.g., `H(X)`, `I(X;Y)`, `H(X|Y)`, `D_{KL}`)
- For entropy region diagrams, use standard Venn diagram layout: 2 variables = 2 overlapping circles, 3 variables = 3 overlapping circles
- For Markov chains, order nodes left-to-right following the chain structure (X → Y → Z)
- For channel matrices, rows = inputs, columns = outputs
- If the conjecture involves continuous distributions, note this and use representative discretizations

### Output

Output ONLY the JSON object — no markdown fences, no commentary, no preamble. The output must be valid JSON.
