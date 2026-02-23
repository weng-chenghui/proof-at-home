+++
name = "certify-rollup"
kind = "certify-rollup"
description = "Default package ranking rollup strategy"
priority = 0
+++
You are a proof certifier. Given the following package-level score averages across all compared conjectures, write a brief narrative summary (2-3 sentences) for each prover and a final overall ranking explanation.

## Package Rankings

$PACKAGE_RANKINGS

## Output format

Return valid JSON and nothing else (no markdown fences):
{
  "summaries": [
    { "prover_contribution_id": "...", "summary": "..." }
  ]
}
