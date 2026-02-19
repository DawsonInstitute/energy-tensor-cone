#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

# Fast test: small basis and constraint count.
# search.m reads these via Environment[] — see mathematica/search.m for defaults.
export AQEI_NUM_BASIS="2"
export AQEI_NUM_CONSTRAINTS="10"
export AQEI_DOMAIN="2.0"
export AQEI_SIGMA="0.7"
export AQEI_SEED="42"

# Prefer wolframscript; fall back to wolfram.
if command -v wolframscript >/dev/null 2>&1; then
  wolframscript -file "$ROOT_DIR/mathematica/search.m"
elif command -v wolfram >/dev/null 2>&1; then
  wolfram -script "$ROOT_DIR/mathematica/search.m"
else
  echo "ERROR: neither wolframscript nor wolfram found on PATH" >&2
  exit 1
fi

python - <<'PY'
import json
from pathlib import Path

results = Path("mathematica/results")
vertex = results / "vertex.json"

assert vertex.exists(), "vertex.json missing"

data = json.loads(vertex.read_text())
assert "numBasis" in data, "vertex.json missing numBasis"
assert "a" in data, "vertex.json missing a"
assert len(data["a"]) == data["numBasis"]
assert "activeIndices" in data
assert "constraints" in data

print(f"Mathematica tests: OK  (numBasis={data['numBasis']}, active={len(data['activeIndices'])})")
PY
