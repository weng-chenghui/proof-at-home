+++
name = "agent-series-audit"
kind = "agent-command"
description = "Audit existing series: cross-lesson consistency, terminology, notation, difficulty progression, citation quality"
priority = 0
+++
# Series Agent — Audit Step

You are auditing an existing lesson series for quality and consistency.

## Series & Lessons
$RESOURCE_ARGUMENTS

## Your Accumulated Knowledge
$AGENT_MEMORIES

## Current State
$AGENT_STATE

## Instructions
Review the series across these dimensions:

1. **Cross-lesson consistency** — Are definitions, notation, and terminology consistent across lessons?
2. **Difficulty progression** — Does difficulty increase smoothly? Are there jarring jumps?
3. **Prerequisite coverage** — Does each lesson adequately build on previous ones?
4. **Completeness** — Are there missing topics that should be covered given the series scope?
5. **Citation quality** — Are references accurate, accessible, and sufficient?
6. **Pedagogical flow** — Do lessons transition naturally? Is there a clear narrative arc?
7. **Conjecture coverage** — Are conjectures well-distributed and appropriately difficult?

## Output Format
Respond with a JSON object:
```json
{
  "overall_score": 8,
  "dimensions": {
    "consistency": {"score": 9, "issues": ["..."]},
    "difficulty_progression": {"score": 7, "issues": ["..."]},
    "prerequisite_coverage": {"score": 8, "issues": ["..."]},
    "completeness": {"score": 8, "issues": ["..."]},
    "citation_quality": {"score": 7, "issues": ["..."]},
    "pedagogical_flow": {"score": 8, "issues": ["..."]},
    "conjecture_coverage": {"score": 8, "issues": ["..."]}
  },
  "critical_issues": ["..."],
  "suggestions": ["..."],
  "lesson_specific_feedback": [
    {"lesson_id": "...", "issues": ["..."], "suggestions": ["..."]}
  ],
  "series_level_suggestions": ["..."]
}
```
