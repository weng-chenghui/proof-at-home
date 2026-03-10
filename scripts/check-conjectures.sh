#!/usr/bin/env bash
# Validate conjecture naming convention and consistency.
# Exit 0 on success, exit 1 with details on failure.
set -euo pipefail

CONJ_DIR="${CONJ_DIR:-examples/data-repo/conjectures}"
LESSON_DIR="${LESSON_DIR:-examples/data-repo/lessons}"
ID_REGEX='^[a-z]+(_[a-z0-9]+)*_[0-9]+_(lean4|rocq)$'

errors=0

# 1. Validate each TOML file
for f in "$CONJ_DIR"/*.toml; do
    [ -f "$f" ] || continue
    fname=$(basename "$f" .toml)

    # Extract id field
    file_id=$(grep -m1 '^id = ' "$f" | sed 's/^id = "\(.*\)"/\1/')
    if [ -z "$file_id" ]; then
        echo "ERROR: $f — missing id field"
        errors=$((errors + 1))
        continue
    fi

    # Check filename matches id
    if [ "$fname" != "$file_id" ]; then
        echo "ERROR: $f — filename '$fname' does not match id '$file_id'"
        errors=$((errors + 1))
    fi

    # Check id matches naming regex
    if ! echo "$file_id" | grep -qE "$ID_REGEX"; then
        echo "ERROR: $f — id '$file_id' does not match naming convention $ID_REGEX"
        errors=$((errors + 1))
    fi

    # Extract prover field
    file_prover=$(grep -m1 '^prover = ' "$f" | sed 's/^prover = "\(.*\)"/\1/')
    if [ -z "$file_prover" ]; then
        echo "ERROR: $f — missing prover field"
        errors=$((errors + 1))
        continue
    fi

    # Check prover suffix matches prover field
    id_suffix="${file_id##*_}"
    if [ "$id_suffix" != "$file_prover" ]; then
        echo "ERROR: $f — id suffix '_${id_suffix}' does not match prover '$file_prover'"
        errors=$((errors + 1))
    fi
done

# 2. Check that conjecture_ids in lesson frontmatter reference existing TOML files
for lesson in "$LESSON_DIR"/*/lesson.md; do
    [ -f "$lesson" ] || continue

    # Extract conjecture_ids from YAML frontmatter
    conj_line=$(awk '/^---$/{n++; next} n==1 && /^conjecture_ids:/{print; exit}' "$lesson")
    [ -z "$conj_line" ] && continue

    # Parse the array: conjecture_ids: [id1, id2, ...]
    ids=$(echo "$conj_line" | sed 's/conjecture_ids: *\[//;s/\].*//;s/,/ /g')
    for cid in $ids; do
        cid=$(echo "$cid" | tr -d ' ')
        [ -z "$cid" ] && continue
        if [ ! -f "$CONJ_DIR/${cid}.toml" ]; then
            echo "ERROR: $lesson — references conjecture '$cid' but $CONJ_DIR/${cid}.toml does not exist"
            errors=$((errors + 1))
        fi
    done
done

if [ "$errors" -gt 0 ]; then
    echo ""
    echo "FAILED: $errors error(s) found"
    exit 1
fi

echo "OK: All conjecture files pass validation"
exit 0
