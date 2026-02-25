#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/.dev"
BARE_REPO="$DEV_DIR/data-repo.git"
EXAMPLE_DATA="$PROJECT_ROOT/examples/data-repo"

if [ -d "$BARE_REPO" ]; then
    echo "Dev environment already exists at $DEV_DIR"
    echo "Run 'make dev-clean' first to start fresh."
    exit 1
fi

echo "=== Setting up local dev environment ==="

# 1. Create bare repo with main as default branch
mkdir -p "$DEV_DIR"
git init --bare --initial-branch=main "$BARE_REPO"
echo "  Created bare repo: $BARE_REPO"

# 2. Create temp working copy, populate with example data, push to bare repo
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

git clone "$BARE_REPO" "$TMPDIR/data"
cp -r "$EXAMPLE_DATA"/* "$TMPDIR/data/"

cd "$TMPDIR/data"
git config user.email "dev@proof-at-home.local"
git config user.name "Proof@Home Dev"
git add -A
git commit -m "Initial data: 3 conjectures, 1 contribution, 1 certificate, 4 commands"
git push origin main

echo "  Populated bare repo with example data"
echo ""
echo "=== Dev environment ready ==="
echo ""
echo "Run the server:"
echo "  make dev-run"
echo ""
echo "Or manually:"
echo "  GIT_DATA_REPO_URL=$BARE_REPO \\"
echo "  GIT_DATA_REPO_PATH=$DEV_DIR/data \\"
echo "  GIT_FORGE_TYPE=local \\"
echo "  DATABASE_PATH=$DEV_DIR/proofathome.db \\"
echo "  go run ./src/server/..."
