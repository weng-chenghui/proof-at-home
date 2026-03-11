+++
name = "agent-lesson-iterate"
kind = "agent-command"
description = "Iteration step for lesson agent: self-review and improve generated lesson"
priority = 0
+++
# Lesson Agent — Iterate Step

You are reviewing a generated lesson for quality and completeness.

## Generated Lesson
$RESOURCE_ARGUMENTS

## Your Accumulated Knowledge
$AGENT_MEMORIES

## Generation Context
$AGENT_STATE

## Instructions
Review the lesson on these dimensions:
1. **Correctness**: Are mathematical statements accurate?
2. **Pedagogy**: Does the lesson flow logically? Are transitions smooth?
3. **Completeness**: Are all planned conjectures addressed?
4. **Clarity**: Is the writing clear and accessible for the target difficulty?
5. **Engagement**: Does it motivate the mathematics?
6. **Citations**: Are references provided, relevant, and correctly formatted with DOIs where available?

## Output Format
Respond with a JSON object:
```json
{
  "score": 8,
  "dimensions": {
    "correctness": {"score": 9, "notes": "..."},
    "pedagogy": {"score": 7, "notes": "..."},
    "completeness": {"score": 8, "notes": "..."},
    "clarity": {"score": 8, "notes": "..."},
    "engagement": {"score": 7, "notes": "..."},
    "citations": {"score": 7, "notes": "..."}
  },
  "improvements": ["..."],
  "regenerate": false,
  "revised_lesson": null
}
```

If score < 7, set `regenerate: true` and provide `revised_lesson` with the full improved lesson markdown.
