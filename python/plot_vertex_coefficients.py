#!/usr/bin/env python3

import json
from pathlib import Path

import matplotlib.pyplot as plt


def main() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    vertex_path = repo_root / "mathematica" / "results" / "vertex.json"
    out_path = repo_root / "papers" / "figures" / "vertex_coefficients.png"

    with vertex_path.open("r", encoding="utf-8") as f:
        vertex = json.load(f)

    a = vertex.get("a")
    if not isinstance(a, list) or not a:
        raise ValueError(f"Expected non-empty list 'a' in {vertex_path}")

    xs = list(range(1, len(a) + 1))

    plt.figure(figsize=(6.5, 3.2))
    plt.bar(xs, a)
    plt.xlabel("Basis coefficient index i")
    plt.ylabel(r"Coefficient $a_i$")
    plt.title("Verified vertex coefficients (finite-dimensional discretization)")
    plt.xticks(xs)
    plt.tight_layout()

    out_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(out_path, dpi=200)
    plt.close()

    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
