#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_ROOT"

echo "Starting Proof@Home dev server..."
echo "Conjectures dir: $PROJECT_ROOT/conjectures/"
echo ""

CONJECTURES_DIR="$PROJECT_ROOT/conjectures" go run ./src/server/...
