#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXAMPLE_DATA="$PROJECT_ROOT/examples/data-repo"

# ── Usage ─────────────────────────────────────────────
usage() {
    echo "Usage: $0 <SERVER_URL> [REPO_NAME]"
    echo ""
    echo "Create a private GitHub data repo for Proof@Home and configure its webhook."
    echo ""
    echo "  SERVER_URL   Base URL of your Proof@Home server (e.g. https://pah.example.com)"
    echo "  REPO_NAME    Name for the data repo (default: proof-at-home-data)"
    exit 1
}

SERVER_URL="${1:-}"
REPO_NAME="${2:-proof-at-home-data}"

if [ -z "$SERVER_URL" ]; then
    usage
fi

# Strip trailing slash from SERVER_URL
SERVER_URL="${SERVER_URL%/}"

# ── Prerequisites ─────────────────────────────────────
echo "=== Checking prerequisites ==="

if ! command -v gh &>/dev/null; then
    echo "Error: gh CLI not found. Install it: https://cli.github.com/"
    exit 1
fi

if ! gh auth status &>/dev/null; then
    echo "Error: gh CLI not authenticated. Run: gh auth login"
    exit 1
fi

if ! command -v git &>/dev/null; then
    echo "Error: git not found. Install git first."
    exit 1
fi

if ! command -v openssl &>/dev/null; then
    echo "Error: openssl not found. Install openssl first."
    exit 1
fi

if [ ! -d "$EXAMPLE_DATA" ]; then
    echo "Error: Example data not found at $EXAMPLE_DATA"
    exit 1
fi

echo "  All prerequisites met."

# ── Create repo ───────────────────────────────────────
echo ""
echo "=== Creating private GitHub repo: $REPO_NAME ==="

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cd "$TMPDIR"
gh repo create "$REPO_NAME" --private --clone
cd "$REPO_NAME"

# ── Populate with example data ────────────────────────
echo ""
echo "=== Populating repo with example data ==="

cp -r "$EXAMPLE_DATA"/* .
git add -A
git commit -m "Initial data: conjectures, contributions, certificates"
git push origin main

echo "  Pushed initial data to main."

# ── Get repo info ─────────────────────────────────────
OWNER_REPO=$(gh repo view --json nameWithOwner -q '.nameWithOwner')
CLONE_URL=$(gh repo view --json url -q '.url')

# ── Generate webhook secret ───────────────────────────
echo ""
echo "=== Configuring webhook ==="

WEBHOOK_SECRET=$(openssl rand -hex 32)

# Create webhook via GitHub API
gh api "repos/${OWNER_REPO}/hooks" \
    -f name=web \
    -f "config[url]=${SERVER_URL}/webhooks/git" \
    -f "config[content_type]=application/json" \
    -f "config[secret]=${WEBHOOK_SECRET}" \
    -f "events[]=push" \
    -f active=true \
    --silent

echo "  Webhook created: ${SERVER_URL}/webhooks/git"

# ── Get token for server config ───────────────────────
GIT_TOKEN=$(gh auth token)

# ── Print env vars ────────────────────────────────────
echo ""
echo "=== Setup complete ==="
echo ""
echo "Add these environment variables to your Proof@Home server:"
echo ""
echo "  GIT_DATA_REPO_URL=${CLONE_URL}.git"
echo "  GIT_FORGE_TYPE=github"
echo "  GIT_FORGE_TOKEN=${GIT_TOKEN}"
echo "  GIT_FORGE_PROJECT=${OWNER_REPO}"
echo "  WEBHOOK_SECRET=${WEBHOOK_SECRET}"
echo ""
echo "Repo: https://github.com/${OWNER_REPO}"
