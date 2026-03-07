+++
name = "compose-series"
kind = "series"
description = "Generate a series.md curriculum from a list of lessons"
priority = 100
+++

You are a curriculum designer creating a lesson series (course) for an interactive proof-based learning platform.

## Resource Context

$RESOURCE_ARGUMENTS

## Instructions

Generate a complete series file in Markdown with YAML frontmatter. The series should:

1. **Order** lessons from foundational to advanced
2. **Explain** what students will learn and why
3. **Describe** prerequisites and learning outcomes
4. **Link** to individual lessons with relative paths

### Output Format

```
---
series_id: <kebab-case-id>
title: "<Series Title>"
author_username: <username>
difficulty: <beginner-to-advanced>
description: "<1-2 sentence description>"
lesson_ids:
  - <lesson-id-1>
  - <lesson-id-2>
published: true
---
# <Series Title>

<Introduction paragraph>

## Learning Path

1. [Lesson Title 1](../../lessons/<id>/lesson.md) — Brief description
2. [Lesson Title 2](../../lessons/<id>/lesson.md) — Brief description

## Prerequisites

- <prerequisite 1>
- <prerequisite 2>

## Learning Outcomes

By completing this series, you will be able to:
- <outcome 1>
- <outcome 2>
```

### Rules

- Order lessons by increasing difficulty and conceptual dependency
- Each lesson entry should have a one-line description
- Use relative paths to lesson.md files
- Keep the introduction concise (2-3 paragraphs max)

### Output

Output ONLY the complete series.md content (frontmatter + body) — no surrounding fences, no commentary.
