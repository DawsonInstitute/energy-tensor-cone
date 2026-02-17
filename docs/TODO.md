# TODO.md

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI to Physical Review D.

**Current Status (February 16, 2026)**: All rigor audit tasks completed. Repository is ready for PRD submission.

## Status

✅ **All mandatory rigor tasks completed** (February 16, 2026)

The repository has undergone a comprehensive audit and all identified issues have been addressed:
- Lean code structure verified (Float for viz, Rat for proofs)
- Repository layout fully documented (all 17 Lean files)  
- violations.json validation added to Python pipeline
- Mathematica seed upgraded to high-entropy timestamp+prime
- README cleaned of past-tense, replication instructions fixed
- Theorem count corrected (35 theorems proven)
- lean_tests.sh enhanced with sorry/axiom checking

All tests pass. See `docs/TODO-completed.md` for detailed completion records.

## Next Steps (Optional Future Work)

These are stretch goals beyond the current PRD submission scope:

1. **Extend to 3+1D spacetimes**: Current work demonstrates feasibility in 1+1D; extension to physical 3+1D would require larger computational resources and additional Lean formalization.

2. **Implement full QFT stress-energy functional**: Current AQEI_functional in AQEI.lean is a stub (returns 0); implementing the full integral operator would enable direct comparison with analytic Fewster bounds.

3. **Scale computational search**: Current vertex finding uses N=6 basis elements; scaling to N=100 would provide richer geometric structure exploration.

4. **Symbolic bound derivation**: Derive analytic expressions for model-specific AQEI bounds to enable rigorous deviation analysis (currently blocked - see TODO-BLOCKED.md).

See `docs/TODO-BLOCKED.md` for tasks requiring additional research or decisions before implementation.

