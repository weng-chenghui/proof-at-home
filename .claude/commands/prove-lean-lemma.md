# Prove a Lean 4 lemma

Prove the lemma described below. Follow this strategy strictly.

## Arguments

$ARGUMENTS

## Setup

- Compiler: `$LEAN_PATH` (or `lean` if not set)
- Lake: `$LAKE_PATH` (or `lake` if not set)
- Scratch directory: `$SCRATCH_DIR` (default: `/tmp/proof-at-home/`)
- Lemma file: `$LEMMA_FILE`

## Strategy

### 1. Read the target file

- Read the file containing the lemma. Understand the imports and namespace.

### 2. Explore the goal

Create a scratch file `$SCRATCH_DIR/debug_lean.lean`:

- Copy the preamble (imports, opens).
- Write the lemma statement with `sorry` as the proof.
- Add `#check` commands for relevant lemmas.
- Run: `$LEAN_PATH $SCRATCH_DIR/debug_lean.lean` and inspect output.

### 3. Search for relevant lemmas

In the same scratch file, add exploration commands:

- `#check @Lemma.name` for candidate lemmas.
- `#print Lemma.name` to see definitions.
- `example : <type> := by exact?` to search for matching lemmas.
- Compile once and inspect.

### 4. Build the proof

- Start with `sorry` and progressively replace with actual tactics.
- Use `simp`, `omega`, `exact?`, `apply?` as discovery tools.
- After each major step, compile to check progress.
- Build up the proof 1-2 tactics at a time.

### 5. Write the final proof

- Once the proof compiles in the scratch file, write to `$LEMMA_FILE`.
- Compile: `$LEAN_PATH $LEMMA_FILE` to confirm.

## Rules

- Never leave `sorry` in the final proof.
- Maximum 5 compile-test cycles before reporting failure.
- Prefer `simp` lemmas and automation (`omega`, `decide`) over manual proofs.
- If `exact?` or `apply?` finds a solution, use it directly.

## Common Tactics

- `simp [lemma1, lemma2]` — simplification with specific lemmas
- `omega` — linear arithmetic over naturals/integers
- `decide` — decidable propositions
- `exact?` / `apply?` — search for matching lemmas
- `rw [lemma]` — rewriting
- `induction x with ...` — structural induction
- `cases x with ...` — case analysis
