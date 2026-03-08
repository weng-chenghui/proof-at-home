+++
name = "agent-lesson-reflect"
kind = "agent-command"
description = "Reflection step for lesson agent: extract lessons learned into memories"
priority = 0
+++
# Lesson Agent — Reflect Step

You are reflecting on a completed lesson generation run to extract reusable knowledge.

## Run Summary
$RESOURCE_ARGUMENTS

## Your Existing Knowledge
$AGENT_MEMORIES

## Run Details
$AGENT_STATE

## Instructions
Review the entire lesson generation process and extract observations that would improve future runs:
1. What pedagogical approaches worked well?
2. What ordering/pacing decisions were effective?
3. Were there surprising gaps or difficulties?
4. What would you do differently next time?

Only create memories for genuinely useful, non-obvious insights. Do not create memories that merely restate the obvious.

## Output Format
Respond with a JSON object:
```json
{
  "memories": [
    {
      "name": "mem-...",
      "kind": "memory-lesson",
      "description": "Brief one-line summary",
      "body": "## Observation\n...\n\n## Evidence\n...\n\n## Recommendation\n...",
      "tags": ["topic", "category"],
      "confidence": 0.7
    }
  ],
  "summary": "Brief summary of what was learned"
}
```
