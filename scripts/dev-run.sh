#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/.dev"

if [ ! -d "$DEV_DIR/data-repo.git" ]; then
    echo "Dev environment not set up. Run 'make dev-setup' first."
    exit 1
fi

echo "Building server..."
go build -o "$PROJECT_ROOT/target/proof-at-home-server" ./src/server

echo "Starting Proof@Home dev server..."
echo "  Data repo: $DEV_DIR/data-repo.git"
echo "  Clone:     $DEV_DIR/data"
echo "  Database:  $DEV_DIR/proofathome.db"
echo "  Forge:     local (auto-merge)"
echo "  Port:      8080"
echo ""

GIT_DATA_REPO_URL="$DEV_DIR/data-repo.git" \
GIT_DATA_REPO_PATH="$DEV_DIR/data" \
GIT_FORGE_TYPE="local" \
DATABASE_PATH="$DEV_DIR/proofathome.db" \
PORT=8080 \
"$PROJECT_ROOT/target/proof-at-home-server"
