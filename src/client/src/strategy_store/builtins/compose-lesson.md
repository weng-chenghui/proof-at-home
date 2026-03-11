+++
name = "compose-lesson"
kind = "lesson"
description = "Generate a lesson.md from conjectures, proofs, and expositions"
priority = 100
+++

You are an expert mathematics educator creating a lesson for an interactive proof-based learning platform. Your lesson will teach mathematical concepts through formal proofs verified by computer proof assistants (Rocq/Lean4).

## Resource Context

$RESOURCE_ARGUMENTS

## Instructions

Generate a complete lesson file in Markdown with YAML frontmatter. The lesson should:

1. **Introduce** the mathematical topic with motivation and historical context
2. **Define** key concepts precisely, using both informal and formal (proof assistant) notation
3. **Build** from simpler to more complex conjectures
4. **Walk through** proof strategies before presenting formal proofs
5. **Include** AI annotations for interactive learning zones

### Output Format

```
---
lesson_id: <kebab-case-id>
title: "<Title>"
topic: <topic-slug>
difficulty: <easy|medium|hard>
conjecture_ids: [<id1>, <id2>, ...]
published: true
ai_annotations:
  - zone: "## <Section heading>"
    context: "<What this section covers>"
    suggestions:
      - "<Suggested question 1>"
      - "<Suggested question 2>"
references:
  - type: article-journal
    title: "Article Title"
    author:
      - family: "Smith"
        given: "John"
    issued:
      date-parts: [[2020]]
    container-title: "Journal Name"
    DOI: "10.xxxx/xxxxx"
  - type: book
    title: "Book Title"
    author:
      - family: "Doe"
        given: "Jane"
    issued:
      date-parts: [[2019]]
    publisher: "Publisher Name"
    ISBN: "978-xxx"
---
# <Lesson Title>

<Markdown body with sections, math ($...$), code blocks, etc.>

## References

<Numbered list of references in a readable format>
```

### Rules

- Use `$...$` for inline math and `$$...$$` for display math
- Use fenced code blocks with language `rocq` or `lean4` for proof snippets
- Reference conjectures by their ID in the text
- Structure sections with clear H2 (##) headings
- Include 2-4 AI annotation zones for key conceptual sections
- Each annotation should have 2-3 suggestion prompts that a student might ask
- Keep the tone accessible but rigorous
- Target 800-1500 words for the body
- Include 2-5 references in CSL-JSON format (types: article-journal, book, chapter, webpage, paper-conference, thesis, report) with DOIs where available

### Output

Output ONLY the complete lesson.md content (frontmatter + body) — no surrounding fences, no commentary.
