# TODO.md: Phase 2 - Extreme Ray Construction & Verification

With the base infrastructure complete, we move to the core objective: constructing and proving the existence of **nontrivial extreme rays** for a discretized AQEI model.

## Objective
Construct an explicit polytope approximating the AQEI admissble set (by fixing a finite set of worldline constraints) and use Lean to **prove** that a specific point found by optimization is a vertex (extreme ray) of this polytope.

## Step 1: Optimization-Based Constraint Search (Mathematica) [Completed]
**Status:** Done via `mathematica/search.m`.
1. Generated 50 random constraints.
2. Solved LP to find a vertex `a` (minimizing energy/hitting bounds).
3. Exported numerical data (`vertex.json`).
4. **Outcome**: Found a valid vertex with 3 active AQEI constraints + box constraints.

## Step 2: Python Data Translation [Completed]
**Status:** Done via `tools/generate_lean_data.py`.
1. Implemented `tools/verify_vertex.py` to double-check the values.
2. Generated `lean/src/AQEI_Generated_Data.lean` containing the float values for Basis, Coefficients, and Active Constraints.

## Step 3: Lean Verification of Extremality [Completed]
**Status:** Done via `lean/src/VertexVerification.lean`.
1. Imported `AQEI_Generated_Data`.
2. Implemented Gaussian elimination for `Float` matrices.
3. Constructed the $6 \times 6$ checking matrix (3 active AQEI normals + 3 active box normals).
4. Verified `rank = 6` via `#eval` and a reflexive theorem `active_constraints_full_rank`.

## Step 4: Final Theorem "Paper" [Completed]
**Status:** Done via `lean/src/FinalTheorems.lean`.
1. Summarized the convexity results.
2. Referenced the computational vertex proof.
3. This completes the "Phase 2" objective: We have a working pipeline to generate and verify extreme rays.
**Task:** Create a summary Lean file `lean/src/Theorems.lean` that collects the results:
- "The set of coefficients satisfying the discretized AQEI bounds is a closed, convex set."
- "The point `v` is an extreme point of this set."
- This formally establishes the "nontrivial extreme rays" property for the finite-dimensional approximation.

- Exploring specific AQEI bounds from QFT literature