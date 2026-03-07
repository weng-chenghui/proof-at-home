---
lesson_id: how-to-create-a-lesson
title: "How to Create a Lesson"
topic: meta
difficulty: easy
conjecture_ids: []
published: true
ai_annotations:
  - zone: "## The Content Pipeline"
    context: "Overview of how content flows from conjectures to lessons"
    suggestions:
      - "What is the difference between a conjecture and a proof?"
      - "Why does the pipeline have separate exposition and lesson steps?"
  - zone: "## Writing lesson.md"
    context: "The YAML frontmatter format and Markdown body conventions"
    suggestions:
      - "What fields are required in the frontmatter?"
      - "How do AI annotations work?"
      - "Can I write a lesson without any conjectures?"
  - zone: "## Three Creation Methods"
    context: "API-assisted, pair-proved, and manual lesson creation"
    suggestions:
      - "Which method should I use if I don't have an API key?"
      - "How does the pair-proved workflow work step by step?"
---
# How to Create a Lesson

This lesson teaches you how to create lessons for Proof@Home. It is itself a lesson -- you can examine the source file `lessons/how-to-create-a-lesson/lesson.md` to see every feature in action.

## The Content Pipeline

Every piece of educational content in Proof@Home follows a pipeline:

```
Conjecture --> Proof --> Exposition --> Lesson --> Series
```

1. **Conjecture:** A formal statement to prove (JSON file with Rocq/Lean code).
2. **Proof:** A machine-checked proof of the conjecture (`.v` or `.lean` file).
3. **Exposition:** A human-readable explanation of the proof (generated or written).
4. **Lesson:** An educational narrative tying together multiple conjectures.
5. **Series:** A curriculum ordering multiple lessons into a course.

Each step builds on the previous one. A lesson references conjectures by ID, and readers can view the proofs and expositions for each one.

## Writing lesson.md

A lesson is a single Markdown file with YAML frontmatter. Here is the format:

```yaml
---
lesson_id: my-lesson-id          # Unique kebab-case identifier
title: "My Lesson Title"         # Human-readable title
topic: algebra                    # Topic slug for filtering
difficulty: medium                # easy, medium, or hard
conjecture_ids: [conj_001, conj_002]  # Referenced conjectures
published: true                   # Whether the lesson is visible
ai_annotations:                   # Interactive AI zones (optional)
  - zone: "## Section Heading"
    context: "What this section covers"
    suggestions:
      - "A question students might ask"
      - "Another suggested prompt"
---
# My Lesson Title

Markdown body goes here...
```

### Required Fields

| Field | Description |
|---|---|
| `lesson_id` | Unique identifier (kebab-case, e.g., `newman-lemma`) |
| `title` | Display title |
| `conjecture_ids` | Array of conjecture IDs referenced in the lesson |
| `published` | `true` to make the lesson visible |

### Optional Fields

| Field | Description |
|---|---|
| `topic` | Topic for filtering (e.g., `algebra`, `rewriting-systems`) |
| `difficulty` | One of `easy`, `medium`, `hard` |
| `description` | Short description for listing pages |
| `prerequisites` | Free text describing what the reader should know |
| `ai_annotations` | Zones for interactive AI features |

### Markdown Body

The body supports standard Markdown with:

- **Math:** Inline `$x + y$` and display `$$\forall x. P(x)$$`
- **Code blocks:** Use ` ```rocq ` or ` ```lean4 ` for proof snippets
- **Tables, lists, headings** -- all standard Markdown
- **Conjecture references:** Mention conjecture IDs like `newman_001` in the text

### AI Annotations

AI annotations define interactive zones in the lesson. When a reader selects text within a zone, the AI sidebar can offer contextual help.

Each annotation has:
- `zone`: A section heading that identifies the zone (must match an H2 heading)
- `context`: Background for the AI about what the section covers
- `suggestions`: Pre-written prompts the student can click

## Three Creation Methods

Every resource in the pipeline (including lessons) supports three creation methods:

### 1. API-Assisted (Default)

The CLI fetches conjecture data from the server, sends it to an AI provider, and generates the lesson automatically.

```bash
pah lesson create --topic rewriting-systems \
  --conjectures newman_001,newman_002,newman_003
```

### 2. Pair-Proved

For users who have access to Claude or ChatGPT but no API key configured:

```bash
# Step 1: Export the prompt
pah lesson export --conjectures newman_001,newman_002,newman_003 > prompt.txt

# Step 2: Paste prompt.txt into Claude, get lesson.md back

# Step 3: Pipe the result back
cat lesson.md | pah lesson create --stdin --method pair-proved
```

### 3. Manual

Write `lesson.md` by hand and submit it:

```bash
pah lesson create --stdin --method manual < lessons/my-lesson/lesson.md
```

## Organizing into a Series

Once you have multiple lessons, you can package them into a series:

```yaml
---
series_id: intro-formal-verification
title: "Introduction to Formal Verification"
lesson_ids:
  - how-to-create-a-lesson
  - newman-lemma
published: true
---
# Introduction to Formal Verification

1. [How to Create a Lesson](../../lessons/how-to-create-a-lesson/lesson.md)
2. [Newman's Lemma](../../lessons/newman-lemma/lesson.md)
```

Create it with:

```bash
pah series create --lessons how-to-create-a-lesson,newman-lemma
```

## Walkthrough: The Newman's Lemma Lesson

The `newman-lemma` lesson in this repository demonstrates every feature:

1. **Three conjectures** of increasing difficulty (`newman_001`, `newman_002`, `newman_003`)
2. **Proof strategy walkthrough** before the formal proof
3. **A counterexample** showing why termination is necessary
4. **AI annotations** on the key sections
5. **Math notation** throughout (inline and display)
6. **Code blocks** with Rocq proof snippets
7. **A summary table** and further reading

To see the full pipeline in action:

```bash
# List available conjectures
pah conjecture list

# View the lesson
pah lesson get newman-lemma

# Export the lesson creation prompt
pah lesson export --conjectures newman_001,newman_002,newman_003 --topic rewriting-systems
```

## Summary

- Lessons live at `lessons/{id}/lesson.md`
- They use YAML frontmatter + Markdown body
- Three creation methods: API-assisted, pair-proved, manual
- AI annotations enable interactive learning
- Series package lessons into courses
- The Newman's lemma lesson is a complete worked example
