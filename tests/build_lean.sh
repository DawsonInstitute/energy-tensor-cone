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
# We capture stdout+stderr so we can filter noisy lines before printing.
# IMPORTANT: do NOT use "cmd; ec=$?" with set -e active — set -e fires on
# the failing command before ec is assigned.  Use an if/else instead.
tmpout=$(mktemp)
if lake build >"$tmpout" 2>&1; then
  ec=0
else
  ec=$?
fi

# Filter lines from Mathlib's cached packages, and their multi-line linter
# continuation text (which has no path prefix and would otherwise slip through).
# Also suppress the "can be disabled" advisory note for the docPrime linter —
# we don't want to disable the linter, just avoid the noisy reminder line.
grep -v '\.lake/packages/' "$tmpout" \
  | grep -v 'Declarations whose name ends with' \
  | grep -v 'linter can be disabled' \
  || true
rm -f "$tmpout"
[ $ec -eq 0 ] || { echo "lake build failed (exit $ec)" >&2; exit $ec; }
