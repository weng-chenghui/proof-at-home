#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# ── 1. Struct renames (Go + Rust source, tests) ──
# ORDER MATTERS: longer patterns first to avoid partial matches
find src/ cmd/ tests/ -type f \( -name '*.go' -o -name '*.rs' \) -exec sed -i '' \
  -e 's/ContributionResult/Proof/g' \
  -e 's/ContributionSummary/Contribution/g' \
  -e 's/CertificatePackageInfo/ContributionReview/g' \
  -e 's/CertificateSummary/Certificate/g' \
  -e 's/PackageRankingSummary/ContributionRanking/g' \
  -e 's/PackageSubmitResponse/ConjectureCreateResponse/g' \
  -e 's/packageSubmitResponse/conjectureCreateResponse/g' \
  -e 's/packageSubmitResult/conjectureSubmitResult/g' \
  {} +

# ── 2. Handler/type renames (Go only) ──
find src/server/ cmd/ -type f -name '*.go' -exec sed -i '' \
  -e 's/PackageHandler/ConjectureWriteHandler/g' \
  -e 's/CommandHandler/StrategyHandler/g' \
  -e 's/type Command struct/type Strategy struct/g' \
  -e 's/data\.Command/data.Strategy/g' \
  {} +

# ── 3. Store/handler method renames (Go) ──
# Note: some of these are already handled by struct renames (e.g.
# AddContributionResult -> AddProof via ContributionResult->Proof),
# but we include them for completeness/safety.
find src/server/ cmd/ tests/ -type f -name '*.go' -exec sed -i '' \
  -e 's/AddProof/AddProof/g' \
  -e 's/ListProofs/ListProofs/g' \
  -e 's/ListContributionReviews/ListContributionReviews/g' \
  -e 's/ListCertificatePackages/ListContributionReviews/g' \
  -e 's/ListCommands/ListStrategies/g' \
  -e 's/GetCommand/GetStrategy/g' \
  -e 's/SubmitResult/SubmitProof/g' \
  -e 's/ListResults/ListProofs/g' \
  {} +

# ── 4. API route renames (Go + Rust + tests) ──
# CRITICAL: archive/specific patterns BEFORE generic patterns
find src/ cmd/ tests/ -type f \( -name '*.go' -o -name '*.rs' \) -exec sed -i '' \
  -e 's|/contributions/{id}/results|/contributions/{id}/proofs|g' \
  -e 's|/contributions/{id}/results|/contributions/{id}/proofs|g' \
  -e 's|/conjecture-packages/{batchId}/seal|/conjectures/batches/{batchId}/seal|g' \
  -e 's|/conjecture-packages/{bid}/seal|/conjectures/batches/{bid}/seal|g' \
  -e 's|/conjecture-packages|/conjectures|g' \
  -e 's|certificate-packages/{contributionID}/archive|contributions/{contributionID}/archive|g' \
  -e 's|certificate-packages/{cid}/archive|contributions/{cid}/archive|g' \
  -e 's|certificate-packages/{id}/archive|contributions/{id}/archive|g' \
  -e 's|certificate-packages/" + contributionID + "/archive|contributions/" + contributionID + "/archive|g' \
  -e 's|certificate-packages/%s/archive|contributions/%s/archive|g' \
  -e 's|certificate-packages/a1111111-1111-1111-1111-111111111111/archive|contributions/a1111111-1111-1111-1111-111111111111/archive|g' \
  -e 's|/certificate-packages|/contribution-reviews|g' \
  -e 's|"/commands"|"/strategies"|g' \
  -e 's|"/commands/{name}"|"/strategies/{name}"|g' \
  {} +

# Also fix the Rust client API URLs that use format! style
find src/client/ -type f -name '*.rs' -exec sed -i '' \
  -e 's|{}/contributions/{}/results|{}/contributions/{}/proofs|g' \
  -e 's|{}/certificate-packages/{}/archive|{}/contributions/{}/archive|g' \
  -e 's|{}/certificate-packages|{}/contribution-reviews|g' \
  -e 's|{}/conjecture-packages/{}/seal|{}/conjectures/batches/{}/seal|g' \
  -e 's|{}/conjecture-packages|{}/conjectures|g' \
  {} +

# ── 5. Rust client method renames ──
find src/client/ -type f -name '*.rs' -exec sed -i '' \
  -e 's/submit_contribution_result/submit_proof/g' \
  -e 's/submit_package_tar/create_conjecture_tar/g' \
  -e 's/submit_package_git_url/create_conjecture_git_url/g' \
  -e 's/seal_conjecture_package/seal_conjecture_batch/g' \
  -e 's/fetch_certificate_packages/fetch_contribution_reviews/g' \
  -e 's/commands_store/strategy_store/g' \
  -e 's/commands_dir/strategies_dir/g' \
  {} +

# ── 6. Git data path strings in Go (filepath.Join args) ──
# Handle both "results") and "results", patterns
find src/server/ cmd/ -type f -name '*.go' -exec sed -i '' \
  -e 's|, "results")|, "proofs")|g' \
  -e 's|, "results",|, "proofs",|g' \
  -e 's|, "commands")|, "strategies")|g' \
  {} +

# ── 7. Scripts ──
find scripts/ -type f -name '*.sh' ! -name 'rename-*' -exec sed -i '' \
  -e 's|/certificate-packages|/contribution-reviews|g' \
  -e 's|/conjecture-packages|/conjectures|g' \
  -e 's|"/commands"|"/strategies"|g' \
  {} +

# ── 8. Docs (README + docs/) ──
for f in README.md docs/architecture.md docs/publishing-guide.md docs/deployment.md; do
  [ -f "$f" ] && sed -i '' \
    -e 's/ContributionResult/Proof/g' \
    -e 's/ContributionSummary/Contribution/g' \
    -e 's/CertificateSummary/Certificate/g' \
    -e 's/CertificatePackageInfo/ContributionReview/g' \
    -e 's/PackageRankingSummary/ContributionRanking/g' \
    -e 's|/contributions/{id}/results|/contributions/{id}/proofs|g' \
    -e 's|conjecture-packages|conjectures (POST)|g' \
    -e 's|certificate-packages|contribution-reviews|g' \
    "$f"
done

echo "✓ All text replacements done"
