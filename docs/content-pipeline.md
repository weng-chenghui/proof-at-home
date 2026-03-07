# Content Pipeline Guide

This document describes the full content pipeline for Proof@Home: how educational content flows from conjectures through proofs, expositions, lessons, and series.

## Pipeline Overview

```
1. CONJECTURE  ──>  2. PROOF  ──>  3. EXPOSITION  ──>  4. LESSON  ──>  5. SERIES
   (generate)        (solve)        (explain)           (compose)        (curate)
```

Each stage builds on the previous one. Conjectures are formal statements; proofs verify them; expositions explain them; lessons teach them; series organize them into courses.

## Three Methods per Resource

Every resource action supports three creation methods:

| Method | Who does the AI work | Cost | stdin needed |
|--------|---------------------|------|-------------|
| `api-assisted` (default) | `pah` calls AI provider directly | Tracked | No |
| `pair-proved` | User pastes into Claude/ChatGPT | Free | Yes |
| `manual` | User writes everything by hand | Free | Yes |

### Pair-Proved Workflow

For users who have Claude access but no API key configured:

```bash
# 1. Export the prompt
pah <resource> export [options] > prompt.txt

# 2. Paste prompt.txt into Claude or ChatGPT

# 3. Copy the AI's response into a file

# 4. Pipe it back
cat result.md | pah <resource> create --stdin --method pair-proved [options]
```

When `pah lesson create` detects no API key, it automatically exports the prompt and prints these instructions.

## Command Reference

### 1. Conjecture (generate)

```bash
pah conjecture list                          # List all conjectures
pah conjecture get <id>                      # Get conjecture details
pah conjecture create <source>               # Create from directory, .tar.gz, or git URL
pah conjecture generate <source>             # Generate from Lean sources
pah conjecture export <id>                   # Export for AI assistant
```

### 2. Proof (solve)

```bash
pah contribution run --by prove-coq-lemma    # AI-assisted proof run
pah proof submit <id> <file>                 # Submit hand-written proof
pah proof submit <id> --stdin                # Submit from stdin
pah proof list --contribution <id>           # List proofs for a contribution
pah proof parse <file>                       # Parse proof into explanation
```

### 3. Exposition (explain)

```bash
pah exposition create --for <id>                          # API-assisted exposition
pah exposition create --for <id> --stdin --method manual   # From stdin
pah exposition export --for <id>                          # Export prompt
pah exposition list                                       # List all expositions
pah exposition get <id>                                   # Get exposition details
```

### 4. Lesson (compose)

```bash
pah lesson list                              # List all lessons
pah lesson get <id>                          # Get lesson details + content
pah lesson create --topic <topic> \
  --conjectures id1,id2,id3                  # API-assisted creation
pah lesson create --stdin --method manual     # From stdin
pah lesson export --conjectures id1,id2       # Export prompt for pair-proved
```

### 5. Series (curate)

```bash
pah series list                              # List all series
pah series get <id>                          # Get series details
pah series create --lessons id1,id2,id3      # API-assisted creation
pah series create --stdin --method manual     # From stdin
pah series export --lessons id1,id2           # Export prompt for pair-proved
```

## Format Reference

### Lesson Format: `lessons/{id}/lesson.md`

```yaml
---
lesson_id: my-lesson                    # Required: unique kebab-case ID
title: "My Lesson Title"               # Required: display title
topic: algebra                          # Optional: topic for filtering
difficulty: medium                      # Optional: easy/medium/hard
description: "Short description"        # Optional: for listing pages
prerequisites: "Linear algebra"         # Optional: free text
conjecture_ids: [conj_001, conj_002]    # Required: referenced conjectures
published: true                         # Required: visibility flag
ai_annotations:                         # Optional: interactive zones
  - zone: "## Section Heading"
    context: "What this section covers"
    suggestions:
      - "Suggested question 1"
      - "Suggested question 2"
---
# Lesson Title

Markdown body with $\LaTeX$ math, code blocks, etc.
```

### Series Format: `series/{id}/series.md`

```yaml
---
series_id: intro-verification          # Required: unique kebab-case ID
title: "Introduction to Verification"  # Required: display title
author_username: admin                 # Optional: author
difficulty: beginner-to-advanced       # Optional: range description
description: "A complete course"       # Optional: short description
lesson_ids:                            # Required: ordered lesson list
  - getting-started
  - newman-lemma
published: true                        # Required: visibility flag
---
# Series Title

Markdown body with learning path, prerequisites, outcomes.
```

### AI Annotations

Each annotation identifies a section of the lesson where AI can provide interactive help:

- `zone`: Must match an H2 (`##`) heading in the lesson body
- `context`: Background information for the AI about the section
- `suggestions`: 2-3 pre-written prompts displayed as clickable buttons

## Full Pipeline Example

Here's a complete walkthrough using the Newman's lemma conjectures:

```bash
# Step 1: Conjectures (already in the pool)
pah conjecture list
# newman_001  Reflexive-transitive closure is transitive  easy
# newman_002  Confluence implies Church-Rosser             medium
# newman_003  Newman's Lemma: WCR + SN implies CR          hard

# Step 2: Proofs (AI-assisted)
pah contribution run --by prove-coq-lemma

# Step 3: Expositions (AI generates from proof)
pah exposition create --for newman_001
pah exposition create --for newman_003

# Step 4: Lesson (AI composes from all the above)
pah lesson create --topic rewriting-systems \
  --conjectures newman_001,newman_002,newman_003

# Step 5: Series (package lessons into a course)
pah series create --lessons how-to-create-a-lesson,newman-lemma
```

## Troubleshooting

### No API key configured

If you haven't set an API key, `pah lesson create` will auto-switch to export mode:

```bash
pah setting set  # Interactive wizard to configure API key
# or
export PAH_API_KEY=sk-ant-...
```

Alternatively, use the pair-proved workflow (see above).

### Verification failures

If a proof doesn't verify:
- Check that the prover version matches the conjecture's dependencies
- Run `pah tools check` to verify your Rocq/Lean installation
- Try `pah proof parse <file>` to get a readable explanation of what the proof does

### Lesson not appearing

- Ensure `published: true` in the frontmatter
- Check that the `lesson_id` in frontmatter matches the directory name
- The server rebuilds its cache from git -- changes may take a moment after push
