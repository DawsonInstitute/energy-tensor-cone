# TODO.md

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI to Physical Review D.

**Current Status (February 16, 2026)**: All mandatory rigor audit tasks completed. Optional future work tasks 2 & 3 completed.

## Status

✅ **All mandatory rigor tasks completed** (February 16, 2026)  
✅ **Optional Tasks 2 & 3 completed** (February 16, 2026)

The repository has undergone a comprehensive audit and enhancement phase:
- Lean code structure verified (Float for viz, Rat for proofs)
- Repository layout fully documented (all 17 Lean files)  
- violations.json validation added to Python pipeline
- Mathematica seed upgraded to high-entropy timestamp+prime
- README cleaned of past-tense, replication instructions fixed
- Theorem count corrected (35 theorems proven)
- lean_tests.sh enhanced with sorry/axiom checking
- **NEW**: Toy QFT functional implemented (AQEI_functional_toy, AQEI_bound_toy)
- **NEW**: Computational search scaled from N=6 to N=100 basis elements

All tests pass. See `docs/TODO-completed.md` for detailed completion records.

## Remaining Optional Future Work

These are stretch goals beyond the current PRD submission scope:

### Task 1: Extend to 3+1D Spacetimes (Major Research Effort)

**Status**: Not started - requires significant computational and formalization resources

**Scope**: Current work demonstrates feasibility in 1+1D; extension to physical 3+1D would require:
- Larger computational resources for polytope search
- Additional Lean formalization for 3+1D Lorentz geometry
- Extended numerical integration over 4D worldlines
- Verification of rank properties in higher-dimensional constraint matrices

**Estimated Effort**: 6-12 months with dedicated compute cluster and formal verification team

**Value**: Would demonstrate methodology scales to physically realistic spacetimes

### Task 4: Symbolic Bound Derivation (Currently Blocked)

**Status**: Partially unblocked by Task 2 completion, but still requires additional research

**Blocking Issues** (see `docs/TODO-BLOCKED.md` for details):
- Need analytic bound formula consistent with Gaussian sampling model
- Need comparison implementation in Python/Mathematica
- Need tests computing deviation thresholds

**Progress Made**:
- ✅ Prerequisite #1: Toy stress-energy functional now specified (AQEI_functional_toy)
- Prerequisite #2: Still pending - derive/choose analytic bound formula
- Prerequisite #3: Still pending - implement comparison tests

**Next Steps to Unblock**:
1. Derive model-specific AQEI bound for Gaussian-basis stress-energy
2. Implement comparison in `python/analyze_results.py`
3. Add validation tests to `tests/python_tests.sh`
4. Generate deviation statistics table for paper

**Estimated Effort**: 2-4 weeks with QFT expertise

**Value**: Would enable quantitative claims about computational search saturating analytic bounds

## Completed Work Summary

**Mandatory Rigor Audit (7 tasks)** - Completed February 16, 2026
1. ✅ Audited GeneratedCandidates.lean structure (Rat data properly used)
2. ✅ Added exhaustive repository layout to README
3. ✅ Implemented violations.json validation in Python
4. ✅ Upgraded Mathematica seed to high-entropy
5. ✅ Cleaned README past-tense and replication instructions
6. ✅ Updated theorem count (35), enhanced lean_tests.sh
7. ✅ Verified all subsystems - ready for PRD submission

**Optional Future Work - Completed (2 tasks)** - Completed February 16, 2026
2. ✅ Implemented toy QFT stress-energy functional in Lean
3. ✅ Scaled computational search N=6→100

**See** `docs/TODO-completed.md` for comprehensive documentation of all completed work.

