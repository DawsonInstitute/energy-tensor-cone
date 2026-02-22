# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.
**Current Status (February 21, 2026)**: All E-batch tasks complete. Pipeline, paper, and Lean proofs are fully consistent.
See `TODO-completed.md` for the full history of completed tasks.

---

## F-Batch: PRD Submission Stage (February 21, 2026)

- **F1**: Update README.md badge and status: DOI 18522457 → 18522456; add submitted status ✅
- **F2**: Update `.github/profile/README.md`: DOI, target venue CMP → PRD, submission status ✅
- **F3**: Remove `DawsonInstitute-dot-github` duplicate clone; remove from `energy.code-workspace` ✅
- **F4**: Update `www/index.html`: DOI, PRD submission status for energy-tensor-cone entry ✅
- **F5**: Update `aqei-bridge/README.md`: CQG → PRD, update manuscript path reference ✅
- **F6**: Update `energy/README.md`: add energy-tensor-cone entry under DawsonInstitute, update recent highlights ✅

---

## Active Tasks

See TODO-completed.md — F1–F6 completed February 21, 2026.

---

## Completed ✅

- PRD submission review audit (H1–H3, M1–M8, L1–L6, README) — commits `1f619c8`, `ae7efc8`
- Documentation/tooling polish A1–A19 — commits `b08286f`, `db9b16f`
- Build/code/paper polish B1–B6 — commit `f3658d8`
- Compilation/verification C1–C20 — commit `9028216`
- Pipeline/paper/test polish D1–D11 — commit `563c6d8`
- Build/import/filter/verification polish E1–E19 — commit `e16ed26`
- Build/import/filter/verification polish E1–E19 — see `TODO-completed.md`

See `TODO-completed.md` for full details.

---

## Future Work (Not Required for Submission)

- **M7 (data consistency)**: Add test that re-runs `generate_lean_data_rat.py` and diffs against `AQEI_Generated_Data_Rat.lean` to guard against stale certified data.
- **L2 (Gaussian normalization)**: Add normalization prefactor to basis functions in `search.m` and note physical interpretation implications in paper.
- **3+1D extension**: Generalize from 1+1D Minkowski to 3+1D.
- **Symbolic bounds**: Replace proxy bound $B_{\text{model}}$ with exact analytic Fewster-style bound.
- **Infinite-dimensional theory**: Connect finite polytope certificate to full QFT.
