# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 19, 2026)**: All PRD submission review items complete. Working through documentation/tooling polish tasks.

See `TODO-completed.md` for the full history of completed tasks.

---

## Active Tasks

### B1. Fix restore vertex.json (stale N=2 data replaced certified N=6 data)
`mathematica/results/vertex.json` was corrupted to a 2-basis prototype.
Restore the N=6 certified vertex (from git commit `08accd2`).
Python tests assert `len(active_indices) == len(constraints) == 3`.

### B2. Fix Lean warnings: unused variables in AQEI.lean
`lean/src/AQEI.lean:53` has unused `γ` and `s` in `AQEI_functional`.
`lean/src/AQEI.lean:80` has unused `pos` (calculated but never referenced).
`lean/src/AQEI.lean:94` has unused `s` in `AQEI_bound_toy`.
Prefix with `_` or remove `pos` line.

### B3. Fix Lean warnings: `simpa using this` → `simp at this` in AffineToCone.lean
`lean/src/AffineToCone.lean:225` and `lean/src/FiniteToyModel.lean:109` emit
"try 'simp at this' instead of 'simpa using this'" linter warnings.
Change both to `simp [basisVec] at this`.

### B4. Fix Lean warnings: unused variables in VertexVerification.lean
`lean/src/VertexVerification.lean:49`: `n_rows` defined but never used.
`lean/src/VertexVerification.lean:54`: `h` bound in `if h : cond` but never used.
Remove/underscore-prefix unused bindings.

### B5. Suppress Mathlib-internal docPrime linter warnings in build output
`lake build` replays hundreds of `.lake/packages/mathlib/` docPrime warnings from
Mathlib's own cached builds. Filter these in `tests/build_lean.sh` so only
warnings from our own `src/` files appear in test output.

### B6. Extend manuscript with applicable real-world applications
The paper currently focuses on theoretical formalization. Add a brief
**Applications and Outlook** section (or expand existing discussion) noting
concrete near-term utility:
  - The AQEI admissible set as a design-constraint filter for quantum-optical
    metamaterial simulations (eliminates non-physical trial configurations).
  - The rational-arithmetic vertex certificate as a calibration reference for
    squeezed-vacuum experiments (provides a machine-verified energy-inequality
    bound independent of floating-point rounding, relevant to precision
    measurement contexts such as LIGO-scale interferometry).
  - The convexity proof structure as a foundation for constrained optimisation
    over physically admissible stress-energy states (relevant to AI-driven
    material discovery requiring hard physical constraints rather than soft
    penalties).
  Keep the tone conservative and let the maths speak; do not overstate scope.

---

## Completed ✅

- PRD submission review audit (H1–H3, M1–M8, L1–L6, README) — commits `1f619c8`, `ae7efc8`
- Documentation/tooling polish A1–A19 — commits `b08286f`, `db9b16f`

See `TODO-completed.md` for full details.

---

## Future Work (Not Required for Submission)

- **M7 (data consistency)**: Add test that re-runs `generate_lean_data_rat.py` and diffs against `AQEI_Generated_Data_Rat.lean` to guard against stale certified data.
- **L2 (Gaussian normalization)**: Add normalization prefactor to basis functions in `search.m` and note physical interpretation implications in paper.
- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D.
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound.
- **Infinite-dimensional theory**: Connect finite polytope certificate to full QFT.
