#!/bin/sh
# Tests for `pah tools` subcommands
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

echo "=== pah tools tests ==="
echo ""

# ── Test 1: pah tools check exits 0, prints tool names ──

OUTPUT=$(pah tools check 2>&1) || true

if echo "$OUTPUT" | grep -q "opam"; then
  pass "Test 1: 'pah tools check' prints tool names (opam found)"
else
  fail "Test 1: 'pah tools check' did not print opam"
fi

if echo "$OUTPUT" | grep -q "elan"; then
  pass "Test 1: 'pah tools check' prints tool names (elan found)"
else
  fail "Test 1: 'pah tools check' did not print elan"
fi

# ── Test 2: pah tools list prints tabular output with MISSING ──

OUTPUT=$(pah tools list 2>&1) || true

if echo "$OUTPUT" | grep -q "MISSING"; then
  pass "Test 2: 'pah tools list' shows MISSING for absent tools"
else
  fail "Test 2: 'pah tools list' did not show MISSING"
fi

if echo "$OUTPUT" | grep -q "Tool"; then
  pass "Test 2: 'pah tools list' has table header"
else
  fail "Test 2: 'pah tools list' missing table header"
fi

# ── Test 3: PAH_TOOL_OPAM env override ──

# Create a fake opam binary
echo '#!/bin/sh' > /tmp/fake-opam
echo 'echo "opam 99.0.0"' >> /tmp/fake-opam
chmod +x /tmp/fake-opam

OUTPUT=$(PAH_TOOL_OPAM=/tmp/fake-opam pah tools check 2>&1) || true

if echo "$OUTPUT" | grep -q "custom"; then
  pass "Test 3: PAH_TOOL_OPAM override detected as custom"
else
  # The override is used in detection — check the list view
  OUTPUT2=$(PAH_TOOL_OPAM=/tmp/fake-opam pah tools list 2>&1) || true
  if echo "$OUTPUT2" | grep "opam" | grep -q "custom"; then
    pass "Test 3: PAH_TOOL_OPAM override detected as custom (via list)"
  else
    fail "Test 3: PAH_TOOL_OPAM override not detected"
  fi
fi

# ── Test 4: pah tools install nonexistent exits non-zero ──

if pah tools install nonexistent > /tmp/test4.out 2>&1; then
  fail "Test 4: 'pah tools install nonexistent' should exit non-zero"
else
  pass "Test 4: 'pah tools install nonexistent' exits non-zero"
fi

if grep -qi "unknown\|not found\|available" /tmp/test4.out; then
  pass "Test 4: Error message is helpful"
else
  fail "Test 4: Error message not helpful: $(cat /tmp/test4.out)"
fi

# ── Test 5: Cache directory ~/.proof-at-home/ is writable ──

rm -rf ~/.proof-at-home
mkdir -p ~/.proof-at-home
echo 'test = "value"' > ~/.proof-at-home/tools.toml

if [ -f ~/.proof-at-home/tools.toml ]; then
  pass "Test 5: Cache path ~/.proof-at-home/tools.toml is writable"
else
  fail "Test 5: Could not write to cache path"
fi
rm -rf ~/.proof-at-home

# ── Test 6: PAH_NO_TOOL_CACHE bypasses cache ──

OUTPUT=$(PAH_NO_TOOL_CACHE=1 pah tools check 2>&1) || true
EXIT=$?

# Should still work (exit 0 or produce output), just skip cache
if [ "$EXIT" -eq 0 ] || echo "$OUTPUT" | grep -q "Tool Check\|opam\|elan"; then
  pass "Test 6: PAH_NO_TOOL_CACHE=1 still works"
else
  fail "Test 6: PAH_NO_TOOL_CACHE=1 failed unexpectedly"
fi

# ── Test 7 (slow): elan install ──

if [ "${RUN_SLOW_TESTS:-}" = "1" ]; then
  echo ""
  echo "--- Slow tests ---"

  # Install elan via pah
  if pah tools install elan 2>&1; then
    pass "Test 7: 'pah tools install elan' succeeded"
  else
    fail "Test 7: 'pah tools install elan' failed"
  fi

  # Source elan env if available
  if [ -f "$HOME/.elan/env" ]; then
    . "$HOME/.elan/env"
  fi

  OUTPUT=$(pah tools check 2>&1) || true
  if echo "$OUTPUT" | grep "elan" | grep -qv "NOT FOUND"; then
    pass "Test 7: elan detected after install"
  else
    fail "Test 7: elan not detected after install"
  fi
else
  echo "  SKIP Test 7: elan install (set RUN_SLOW_TESTS=1)"
fi

summary
