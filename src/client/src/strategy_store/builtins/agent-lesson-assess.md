+++
name = "agent-lesson-assess"
kind = "agent-command"
description = "Assessment step for lesson agent: evaluate proof/exposition quality for each conjecture"
priority = 0
+++
# Lesson Agent — Assess Step

You are evaluating the quality and completeness of available resources for a lesson.

## Available Resources
$RESOURCE_ARGUMENTS

## Your Accumulated Knowledge
$AGENT_MEMORIES

## Current Plan
$AGENT_STATE

## Instructions
1. For each conjecture in the plan, evaluate:
   - Is the proof available and complete?
   - Is there an exposition that explains the proof well?
   - What gaps exist in the available material?
2. Suggest adjustments to the plan based on resource quality
3. Flag any conjectures that lack sufficient material

## Output Format
Respond with a JSON object:
```json
{
  "assessments": [
    {
      "conjecture_id": "...",
      "proof_quality": "good|adequate|poor|missing",
      "exposition_quality": "good|adequate|poor|missing",
      "gaps": ["..."],
      "recommendation": "..."
    }
  ],
  "plan_adjustments": ["..."],
  "ready_to_generate": true
}
```
