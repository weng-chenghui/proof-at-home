#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# ── Rust module directory ──
if [ -d src/client/src/commands_store ]; then
  mv src/client/src/commands_store src/client/src/strategy_store
  echo "  Renamed: src/client/src/commands_store → strategy_store"
fi

# ── Go handler files ──
if [ -f src/server/handlers/commands.go ]; then
  mv src/server/handlers/commands.go src/server/handlers/strategies.go
  echo "  Renamed: handlers/commands.go → strategies.go"
fi
if [ -f src/server/handlers/packages.go ]; then
  mv src/server/handlers/packages.go src/server/handlers/conjectures_write.go
  echo "  Renamed: handlers/packages.go → conjectures_write.go"
fi

# ── Example data repo ──
if [ -d examples/data-repo/commands ]; then
  mv examples/data-repo/commands examples/data-repo/strategies
  echo "  Renamed: examples/data-repo/commands → strategies"
fi
for d in examples/data-repo/contributions/*/results; do
  [ -d "$d" ] && mv "$d" "${d%results}proofs" && echo "  Renamed: $d → ${d%results}proofs"
done

# ── Dev data repo (use git mv inside the subrepo) ──
if [ -d .dev/data/.git ]; then
  pushd .dev/data > /dev/null

  if [ -d commands ]; then
    git mv commands strategies 2>/dev/null || mv commands strategies
    echo "  Renamed: .dev/data/commands → strategies"
  fi

  for d in contributions/*/results; do
    if [ -d "$d" ]; then
      git mv "$d" "${d%results}proofs" 2>/dev/null || mv "$d" "${d%results}proofs"
      echo "  Renamed: .dev/data/$d → ${d%results}proofs"
    fi
  done

  # Commit the renames in the data subrepo
  git add -A
  git commit -m "Rename commands/ → strategies/ and results/ → proofs/" 2>/dev/null || true

  popd > /dev/null
fi

echo "✓ All directory renames done"
