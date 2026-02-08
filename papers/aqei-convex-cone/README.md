# Anonymized Supplements for "Convex Cone of Energy Tensors under AQEI"

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

1. **Build Lean proofs**: `cd lean && lake build`
2. **Run Mathematica search**: `cd mathematica && wolframscript -file search.m`
3. **Process results**: `cd python && python orchestrator.py`
4. **Run full test suite**: `./run_tests.sh`

## Formal Verification

- **Core theorems proven**: All 10 critical theorems (closure, convexity, homogenization, vertex characterization) are fully proven in Lean with no placeholders.
- **Intentional `sorry` statements**: Two theorems in `ConeProperties.lean` have `sorry` placeholders because they are intentionally false as stated (AQEI constraints are affine, not homogeneous). These document why bare AQEI regions are not true cones; the correct cone formulation is proven in `AffineToCone.lean`.
- **Test validation**: See `docs/theorem_verification.md` for complete proof inventory.

## Notes on Terminology

- The Mathematica search defaults to `numTrials=20000`, but tests override with `AQEI_NUM_TRIALS` to keep runs fast.
- With a nonzero bound term $B_{\gamma,g}$, the admissible region is typically **convex** but not literally a cone under positive scaling unless extra homogeneity assumptions are imposed. The homogenized cone construction (proven in `AffineToCone.lean`) resolves this by embedding the affine constraints in a higher-dimensional space.
