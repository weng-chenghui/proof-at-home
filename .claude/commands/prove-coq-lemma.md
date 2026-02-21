# Prove a Rocq lemma

Prove the lemma described below. Follow this strategy strictly.

## Arguments

$ARGUMENTS

## Setup

- Compiler: `$ROCQ` (or `rocq c` if not set)
- Include flag: `$COQ_INCLUDE` (may be empty)
- All debug scripts go in `$SCRATCH_DIR/debug_rocq.v` (default: `/tmp/proof-at-home/debug_rocq.v`)
- Lemma file: `$LEMMA_FILE`

## Strategy

### 1. Read the target file

- Read the file containing the lemma. Do NOT read imported files yet — only read specific dependencies later when you need a definition's type or body.

### 2. See the goal and unfold definitions

Do this in a **single** temp script + compile cycle:

- Create `$SCRATCH_DIR/debug_rocq.v` copying the file up to the stuck proof point.
- Add `rewrite /def1 /def2 ... /=.` to reduce local definitions to primitives.
- Insert `Show.` to display the proof state.
- End with `Abort.` so the file compiles.
- Compile: `$ROCQ c $COQ_INCLUDE $SCRATCH_DIR/debug_rocq.v` and inspect the output.

### 3. Check and search for lemmas

Batch all queries into a **single** temp script:

- Use `Check @lemma_name.` for candidate lemmas.
- Use `Search (pattern).` or `Search "keyword".` when the goal almost matches but differs in one subterm.
- Compile once and inspect all output together.

### 4. Build the proof

- Add 2-3 tactics at a time with `Show.` after the last one.
- Compile to verify progress. Only compile after each single tactic when a step is non-obvious or fails.
- After writing the full proof attempt, compile. If it fails, bisect to find the failing tactic.

### 5. Apply to the real file

- Once the proof compiles in the debug script, write the complete proof to `$LEMMA_FILE`.
- Compile: `$ROCQ c $COQ_INCLUDE $LEMMA_FILE` to confirm.

## Rules

- Use `apply`/`exact` (not ssreflect `:` variants) during debugging — they give clearer errors.
- Never guess a proof without seeing the goal via `Show.` first.
- Maximum 5 compile-test cycles before reporting failure.
- If a compilation fails with a type mismatch or stale-signature error, check that imported `.vo` files are newer than their `.v` sources.

## Diagnostics

### "expected type X, got type Y" where Y makes no sense

The identifier likely resolves to a different definition than intended (name shadowing). Run `Locate ident.` to list all definitions with that name and which one is active.

### Check actual signatures before writing instance constructions

Never infer a definition's signature from the section it was defined in. Always run `About @name.` or `Check @name.` to see the real signature.
