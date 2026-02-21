#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_ROOT"

echo "Starting Proof@Home dev server..."
echo "Problems dir: $PROJECT_ROOT/problems/"
echo ""

PROBLEMS_DIR="$PROJECT_ROOT/problems" go run ./src/server/...
