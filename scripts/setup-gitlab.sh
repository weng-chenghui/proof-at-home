#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXAMPLE_DATA="$PROJECT_ROOT/examples/data-repo"

# ── Usage ─────────────────────────────────────────────
usage() {
    echo "Usage: $0 <SERVER_URL> [PROJECT_NAME]"
    echo ""
    echo "Create a private GitLab data repo for Proof@Home and configure its webhook."
    echo ""
    echo "  SERVER_URL    Base URL of your Proof@Home server (e.g. https://pah.example.com)"
    echo "  PROJECT_NAME  Name for the data project (default: proof-at-home-data)"
    exit 1
}

SERVER_URL="${1:-}"
PROJECT_NAME="${2:-proof-at-home-data}"

if [ -z "$SERVER_URL" ]; then
    usage
fi

# Strip trailing slash from SERVER_URL
SERVER_URL="${SERVER_URL%/}"

# ── Prerequisites ─────────────────────────────────────
echo "=== Checking prerequisites ==="

if ! command -v glab &>/dev/null; then
    echo "Error: glab CLI not found. Install it: https://gitlab.com/gitlab-org/cli#installation"
    exit 1
fi

if ! glab auth status &>/dev/null; then
    echo "Error: glab CLI not authenticated. Run: glab auth login"
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
echo "=== Creating private GitLab project: $PROJECT_NAME ==="

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cd "$TMPDIR"
glab repo create "$PROJECT_NAME" --private --defaultBranch main
git clone "$(glab repo view "$PROJECT_NAME" --output json | python3 -c "import sys,json; print(json.load(sys.stdin)['http_url_to_repo'])")" "$PROJECT_NAME"
cd "$PROJECT_NAME"

# ── Populate with example data ────────────────────────
echo ""
echo "=== Populating project with example data ==="

cp -r "$EXAMPLE_DATA"/* .
git add -A
git commit -m "Initial data: conjectures, contributions, certificates"
git push origin main

echo "  Pushed initial data to main."

# ── Get project info ──────────────────────────────────
PROJECT_INFO=$(glab repo view "$PROJECT_NAME" --output json)
PROJECT_ID=$(echo "$PROJECT_INFO" | python3 -c "import sys,json; print(json.load(sys.stdin)['id'])")
PROJECT_PATH=$(echo "$PROJECT_INFO" | python3 -c "import sys,json; print(json.load(sys.stdin)['path_with_namespace'])")
PROJECT_URL=$(echo "$PROJECT_INFO" | python3 -c "import sys,json; print(json.load(sys.stdin)['http_url_to_repo'])")

# ── Generate webhook token ────────────────────────────
echo ""
echo "=== Configuring webhook ==="

WEBHOOK_TOKEN=$(openssl rand -hex 32)

# Create webhook via GitLab API
glab api "projects/${PROJECT_ID}/hooks" \
    -f "url=${SERVER_URL}/webhooks/git" \
    -f "token=${WEBHOOK_TOKEN}" \
    -f "push_events=true" \
    -f "enable_ssl_verification=true" \
    --silent

echo "  Webhook created: ${SERVER_URL}/webhooks/git"

# ── Get token for server config ───────────────────────
# glab doesn't have a direct "auth token" command; read from config
GITLAB_HOST=$(echo "$PROJECT_INFO" | python3 -c "import sys,json; print(json.load(sys.stdin)['web_url'].split('/')[2])")
GIT_TOKEN=$(glab config get token -h "$GITLAB_HOST" 2>/dev/null || echo "<SET_YOUR_GITLAB_TOKEN>")

# ── Determine API URL ─────────────────────────────────
if [ "$GITLAB_HOST" = "gitlab.com" ]; then
    API_URL="https://gitlab.com/api/v4"
else
    API_URL="https://${GITLAB_HOST}/api/v4"
fi

# ── Print env vars ────────────────────────────────────
echo ""
echo "=== Setup complete ==="
echo ""
echo "Add these environment variables to your Proof@Home server:"
echo ""
echo "  GIT_DATA_REPO_URL=${PROJECT_URL}"
echo "  GIT_FORGE_TYPE=gitlab"
echo "  GIT_FORGE_TOKEN=${GIT_TOKEN}"
echo "  GIT_FORGE_API_URL=${API_URL}"
echo "  GIT_FORGE_PROJECT=${PROJECT_PATH}"
echo "  WEBHOOK_SECRET=${WEBHOOK_TOKEN}"
echo ""
echo "Project: https://${GITLAB_HOST}/${PROJECT_PATH}"
