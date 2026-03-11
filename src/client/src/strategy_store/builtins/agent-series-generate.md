+++
name = "agent-series-generate"
kind = "agent-command"
description = "Produce batch manifest for lesson generation from assessed series plan"
priority = 0
+++
# Series Agent — Generate Step

You are preparing a batch generation manifest. This manifest will be used to spawn individual lesson-agent instances for each lesson in the series.

## Series Plan & Assessment
$RESOURCE_ARGUMENTS

## Your Accumulated Knowledge
$AGENT_MEMORIES

## Current State
$AGENT_STATE

## Instructions
1. **Finalize** the lesson list incorporating assessment feedback
2. **Prepare resource arguments** for each lesson — topic, difficulty, conjecture IDs, references, and any context from the series plan
3. **Set generation order** — lessons with no dependencies first, then dependent lessons
4. **Define shared context** — series-wide terminology, notation conventions, and style guidelines that all lessons should follow

## Output Format
Respond with a JSON object:
```json
{
  "series_id": "...",
  "series_title": "...",
  "generation_order": [0, 1, 2],
  "shared_context": "Series-wide style and notation guidelines...",
  "lessons": [
    {
      "sequence": 1,
      "lesson_id": "...",
      "title": "...",
      "topic": "...",
      "difficulty": "easy|medium|hard",
      "conjecture_ids": ["..."],
      "resource_arguments": "Formatted resource context for compose-lesson strategy...",
      "references": [
        {"title": "...", "authors": "...", "year": 2020, "doi": "...", "type": "book"}
      ],
      "depends_on": []
    }
  ],
  "notes": "..."
}
```

Note: You do NOT generate lessons yourself. You prepare the manifest so the orchestrator can delegate each lesson to a lesson-agent instance.
