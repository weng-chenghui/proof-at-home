#!/bin/sh
# Tests for require_tool() error messages (non-interactive)
set -eu

PASS=0
FAIL=0

pass() {
  PASS=$((PASS + 1))
  printf '  \033[32mPASS\033[0m %s\n' "$1"
}

fail() {
  FAIL=$((FAIL + 1))
  printf '  \033[31mFAIL\033[0m %s\n' "$1"
}

summary() {
  echo ""
  echo "Results: $PASS passed, $FAIL failed"
  [ "$FAIL" -eq 0 ] || exit 1
}

echo "=== require_tool error tests ==="
echo ""

# ── Test 1: conjecture generate without lean_conjecturer exits non-zero ──

if pah conjecture generate /dev/null > /tmp/require1.out 2>&1; then
  fail "Test 1: Should exit non-zero without lean_conjecturer"
else
  pass "Test 1: Exits non-zero without lean_conjecturer"
fi

# ── Test 2: Error mentions "not installed" and "lean_conjecturer" ──

ERROR_OUTPUT=$(cat /tmp/require1.out)

if echo "$ERROR_OUTPUT" | grep -qi "not installed"; then
  pass "Test 2: Error contains 'not installed'"
else
  fail "Test 2: Error missing 'not installed'. Got: $ERROR_OUTPUT"
fi

if echo "$ERROR_OUTPUT" | grep -q "lean_conjecturer"; then
  pass "Test 2: Error contains 'lean_conjecturer'"
else
  fail "Test 2: Error missing 'lean_conjecturer'. Got: $ERROR_OUTPUT"
fi

# ── Test 3: Error contains install hint URL ──

if echo "$ERROR_OUTPUT" | grep -q "LeanConjecturer"; then
  pass "Test 3: Error contains install hint (LeanConjecturer)"
else
  fail "Test 3: Error missing install hint. Got: $ERROR_OUTPUT"
fi

summary
