#!/usr/bin/env bash
set -euo pipefail

# Creates tar.gz archives for each demo prover and generates seed contribution
# JSON files that the server can load via SEED_CERTIFICATIONS env var.
#
# Usage:
#   ./scripts/seed-review-demo.sh
#   SEED_CERTIFICATIONS=examples/review-demo/seed CONJECTURES_DIR=conjectures go run ./src/server/...

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEMO_DIR="$PROJECT_ROOT/examples/review-demo"
SEED_DIR="$DEMO_DIR/seed"

mkdir -p "$SEED_DIR"

# Fixed UUIDs for reproducible demos
ALICE_SESSION="a1111111-1111-1111-1111-111111111111"
BOB_SESSION="b2222222-2222-2222-2222-222222222222"
CAROL_SESSION="c3333333-3333-3333-3333-333333333333"

echo "=== Packaging demo proof archives ==="

for prover in alice bob carol; do
    PROVER_DIR="$DEMO_DIR/$prover"
    ARCHIVE="$DEMO_DIR/${prover}-proofs.tar.gz"

    # Create tar.gz from proof files
    tar -czf "$ARCHIVE" -C "$PROVER_DIR" .
    SHA=$(shasum -a 256 "$ARCHIVE" | awk '{print $1}')

    echo "  $prover: $ARCHIVE (sha256: ${SHA:0:16}...)"

    # Determine session ID
    case $prover in
        alice) SESSION_ID="$ALICE_SESSION" ;;
        bob)   SESSION_ID="$BOB_SESSION" ;;
        carol) SESSION_ID="$CAROL_SESSION" ;;
    esac

    # Write seed session JSON
    cat > "$SEED_DIR/${prover}_session.json" <<EOF
{
  "username": "$prover",
  "session_id": "$SESSION_ID",
  "conjectures_attempted": 2,
  "conjectures_proved": 2,
  "total_cost_usd": 0.05,
  "archive_sha256": "$SHA",
  "nft_metadata": {},
  "prover": "rocq",
  "conjecture_ids": ["prob_001", "prob_002"],
  "archive_path": "../${prover}-proofs.tar.gz"
}
EOF
done

echo ""
echo "=== Seed files written to $SEED_DIR/ ==="
echo ""
echo "Start the server with review demo data:"
echo ""
echo "  SEED_CERTIFICATIONS=$SEED_DIR CONJECTURES_DIR=$PROJECT_ROOT/conjectures go run ./src/server/..."
echo ""
echo "Then test:"
echo "  curl http://localhost:8080/certificate-packages | python3 -m json.tool"
echo "  proof-at-home certify start"
