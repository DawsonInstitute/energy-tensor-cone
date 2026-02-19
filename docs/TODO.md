# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 19, 2026)**: All PRD submission review items complete. `lake build` succeeds with no errors across all 17 Lean files. CI pipeline active. All tests pass. Ready for PRD submission.

See `TODO-completed.md` for the full history of completed tasks.

---

## Completed ✅

All items from the comprehensive PRD submission review audit have been resolved:

| ID | Item | Commit |
|----|------|--------|
| H1 | `B_poly` circularity — tautological vertex certificate | `1f619c8` |
| H2 | N=6 vs N=100 inconsistency between paper and code | `1f619c8` |
| H3 | LP objective mismatch between paper and `search.m` | `1f619c8` |
| M1 | `mathematica_tests.sh` env vars ignored by `search.m` | `1f619c8` |
| M2 | `lean_tests.sh` axiom check non-functional; `Lean.ofReduceBool` undisclosed | `1f619c8` |
| M3 | Non-deterministic seed in `search.m` | `1f619c8` |
| M4 | `verify_vertex.py` never invoked | `1f619c8` |
| M5 | No CI pipeline | `ae7efc8` |
| M6 | `active_B` values unused in Lean proofs | `1f619c8` (via H1) |
| M7 | No data consistency test (`vertex.json` ↔ `AQEI_Generated_Data_Rat.lean`) | Deferred → Future Work |
| M8 | Integration error budget unquantified | `ae7efc8` |
| L1 | `analyze_results()` dead code | `ae7efc8` |
| L2 | Gaussian basis not normalized | Deferred → Future Work |
| L3 | "10 critical theorems" not enumerated in paper | `1f619c8` |
| L4 | Intentional `sorry` in `ConeProperties.lean` not disclosed in paper | `1f619c8` |
| L5 | Plotting scripts not tested | `ae7efc8` |
| L6 | `verification_matrix` rows duplicated across files without cross-check | `ae7efc8` |
| — | README peer-review (stale JSONs, CI entry, Lean.ofReduceBool note) | `ae7efc8` |

---

## Future Work (Not Required for Submission)

- **M7 (data consistency)**: Add test that re-runs `generate_lean_data_rat.py` and diffs against `AQEI_Generated_Data_Rat.lean` to guard against stale certified data.
- **L2 (Gaussian normalization)**: Add normalization prefactor to basis functions in `search.m` and note physical interpretation implications in paper.
- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D.
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound.
- **Infinite-dimensional theory**: Connect finite polytope certificate to full QFT.
