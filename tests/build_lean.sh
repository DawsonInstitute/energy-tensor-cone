#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# If elan is installed, load its env to put `lake` on PATH.
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found on PATH. Install Lean 4 (elan) so 'lake build' works." >&2
  exit 1
fi

cd "$ROOT_DIR/lean"

# Fetch dependencies if any (none by default), then build.
# Filter out warnings replayed from Mathlib's own cached packages — those come
# from Mathlib internals and cannot be fixed here.  Only warnings from our own
# src/ files are shown.
tmpout=$(mktemp)
lake build >"$tmpout" 2>&1; ec=$?
# Filter lines from Mathlib's cached packages, and their multi-line linter
# continuation text (which has no path prefix and would otherwise slip through).
grep -v '\.lake/packages/' "$tmpout" \
  | grep -v 'Declarations whose name ends with' \
  || true
rm -f "$tmpout"
[ $ec -eq 0 ] || { echo "lake build failed (exit $ec)" >&2; exit $ec; }
