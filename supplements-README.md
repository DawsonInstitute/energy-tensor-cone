# Supplements for "Convex Cone of Energy Tensors under AQEI"

Computational + formalization scaffold for exploring **Averaged Quantum Energy Inequality (AQEI)** constraints as an (approximate) intersection of half-spaces, and for feeding randomized search "near-misses" into a Lean 4 skeleton.

This repository contains:
- **Mathematica** (`mathematica/search.m`) - Randomized finite-Gaussian-basis search in 1+1 Minkowski, exports results to JSON
- **Python** (`python/orchestrator.py`, `python/analyze_results.py`) - Runs search, parses JSON, generates Lean code
- **Lean 4** (`lean/src/*.lean`) - Definitional skeleton (Lorentzian bilinear form, stress-energy, AQEI family, admissible set / "cone", extreme rays)

## Key Files

- **lean/src/FinalTheorems.lean** - Main verification theorems
- **lean/src/AffineToCone.lean** - Homogenization construction
- **lean/src/PolyhedralVertex.lean** - Vertex characterization
- **lean/src/VertexVerificationRat.lean** - Exact rational arithmetic verification
- **mathematica/search.m** - Computational search script
- **python/orchestrator.py** - Pipeline orchestration

## Usage

Run the local test entrypoint to verify all components:

```bash
./run_tests.sh
```

This runs:
- **Lean build verification**: Compiles all formal proofs (`lake build`)
- **Python tests**: Validates data processing pipeline
- **Mathematica tests**: Runs computational search (fast test mode)

### Replication Instructions

To reproduce the full computational + formal verification pipeline:

```bash
# 0. Verify environment
bash tests/check_deps.sh

# 1. Install Python dependencies (numpy, scipy, matplotlib, sympy)
cd python && python -m pip install -e . && cd ..

# 2. Run Mathematica search (produces mathematica/results/vertex.json)
cd mathematica && wolframscript -file search.m && cd ..

# 3. Process results: validate constraints, export pipeline_validation.json,
#    generate GeneratedCandidates.lean
cd python && python orchestrator.py && cd ..

# 4. Build Lean proofs (certifies vertex in Lean)
#    Filtered output written to lean/build.log for manual review.
bash tests/build_lean.sh

# 5. Run full verification suite
./run_tests.sh
```

## Formal Verification

- **Core theorems proven**: 35 theorems proven across the Lean codebase, including closure/convexity results (AQEIFamilyInterface.lean), homogenization theorems (AffineToCone.lean), vertex characterization (PolyhedralVertex.lean, VertexVerificationRat.lean), and the main certificate theorem (FinalTheorems.Candidate_Is_Extreme_Point). No unintentional `sorry` placeholders in proven results.
- **Intentional `sorry` statements**: Two theorems in `ConeProperties.lean` have `sorry` placeholders because they are intentionally false as stated (AQEI constraints are affine, not homogeneous). These document why bare AQEI regions are not true cones; the correct cone formulation is proven in `AffineToCone.lean`.
- **Test validation**: See `docs/theorem_verification.md` for complete proof inventory.

## Notes on Terminology

- The Mathematica search defaults to `numConstraints=50` (constraint sample count); tests override with `AQEI_NUM_CONSTRAINTS` via environment variable to keep runs fast.
- With a nonzero bound term $B_{\gamma,g}$, the admissible region is typically **convex** but not literally a cone under positive scaling unless extra homogeneity assumptions are imposed. The homogenized cone construction (proven in `AffineToCone.lean`) resolves this by embedding the affine constraints in a higher-dimensional space.
