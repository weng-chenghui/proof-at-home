#!/bin/sh
# Tests for scripts/install.sh
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

# ── Setup: serve the pre-built binary as a tarball ──

ARCH="$(uname -m)"
case "$ARCH" in
  x86_64)  ARCH_NAME="amd64" ;;
  aarch64) ARCH_NAME="arm64" ;;
  arm64)   ARCH_NAME="arm64" ;;
esac

ARCHIVE="pah-linux-${ARCH_NAME}.tar.gz"
SERVE_DIR="/tmp/pah-serve"
mkdir -p "$SERVE_DIR"
tar czf "$SERVE_DIR/$ARCHIVE" -C /usr/local/bin pah

# Start HTTP server in the background
python3 -m http.server 9999 --directory "$SERVE_DIR" &
HTTP_PID=$!
sleep 1

DOWNLOAD_URL="http://localhost:9999/${ARCHIVE}"

echo "=== install.sh tests ==="
echo ""

# ── Test 1: Basic install ──

export PAH_DOWNLOAD_URL="$DOWNLOAD_URL"
export PAH_INSTALL="/tmp/pah-test-install"
export PAH_VERSION="v0.0.0-test"
rm -rf "$PAH_INSTALL"

sh /workspace/scripts/install.sh --minimal > /tmp/test1.out 2>&1

if [ -x "$PAH_INSTALL/bin/pah" ]; then
  pass "Test 1: Binary installed to \$PAH_INSTALL/bin/pah"
else
  fail "Test 1: Binary not found at $PAH_INSTALL/bin/pah"
fi

if "$PAH_INSTALL/bin/pah" --version > /dev/null 2>&1; then
  pass "Test 1: pah --version exits 0"
else
  fail "Test 1: pah --version failed"
fi

# ── Test 2: PATH setup ──

# The installer writes to a shell rc file
RC_FOUND=0
for rc in "$HOME/.bashrc" "$HOME/.profile" "$HOME/.zshrc"; do
  if [ -f "$rc" ] && grep -qF "$PAH_INSTALL/bin" "$rc" 2>/dev/null; then
    RC_FOUND=1
    break
  fi
done

if [ "$RC_FOUND" = "1" ]; then
  pass "Test 2: PATH added to shell rc file"
else
  fail "Test 2: PATH not found in any rc file"
fi

# ── Test 3: Idempotent re-run ──

sh /workspace/scripts/install.sh --minimal > /tmp/test3.out 2>&1
EXIT_CODE=$?

if [ "$EXIT_CODE" -eq 0 ]; then
  pass "Test 3: Idempotent re-run exits 0"
else
  fail "Test 3: Re-run exited $EXIT_CODE"
fi

# ── Test 4: Unknown flag ──

unset PAH_DOWNLOAD_URL PAH_INSTALL PAH_VERSION
if sh /workspace/scripts/install.sh --bogus-flag > /dev/null 2>&1; then
  fail "Test 4: Unknown flag should exit non-zero"
else
  pass "Test 4: Unknown flag exits non-zero"
fi

# ── Test 5: --minimal flag ──

export PAH_DOWNLOAD_URL="$DOWNLOAD_URL"
export PAH_INSTALL="/tmp/pah-test-minimal"
export PAH_VERSION="v0.0.0-test"
rm -rf "$PAH_INSTALL"

OUTPUT=$(sh /workspace/scripts/install.sh --minimal 2>&1)
EXIT_CODE=$?

if [ "$EXIT_CODE" -eq 0 ]; then
  pass "Test 5: --minimal exits 0"
else
  fail "Test 5: --minimal exited $EXIT_CODE"
fi

# --minimal should not prompt about toolchains
if echo "$OUTPUT" | grep -qi "which prover"; then
  fail "Test 5: --minimal should not prompt about toolchains"
else
  pass "Test 5: --minimal has no toolchain prompt"
fi

# ── Cleanup ──

kill "$HTTP_PID" 2>/dev/null || true

summary
