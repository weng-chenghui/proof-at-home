+++
name = "agent-series-assess"
kind = "agent-command"
description = "Evaluate series plan: check existing conjectures, flag gaps, assess feasibility"
priority = 0
+++
# Series Agent — Assess Step

You are evaluating a series plan for feasibility and completeness.

## Series Plan
$RESOURCE_ARGUMENTS

## Your Accumulated Knowledge
$AGENT_MEMORIES

## Current State
$AGENT_STATE

## Instructions
1. **Check existing resources** — which conjectures already exist on the platform?
2. **Identify gaps** — which conjectures need to be created? Are there missing prerequisites?
3. **Assess feasibility** — is the scope realistic? Is the difficulty curve appropriate?
4. **Check references** — are the proposed references real and accessible?
5. **Suggest improvements** — reordering, additional conjectures, better references

## Output Format
Respond with a JSON object:
```json
{
  "feasibility_score": 8,
  "existing_conjectures_found": ["prob_xxx"],
  "conjectures_to_create": 5,
  "gaps": [
    {"type": "missing_prerequisite|missing_conjecture|scope_issue", "description": "...", "lesson_index": 0}
  ],
  "reference_quality": "good|fair|poor",
  "suggestions": ["..."],
  "revised_lesson_order": null,
  "ready_to_generate": true,
  "notes": "..."
}
```
