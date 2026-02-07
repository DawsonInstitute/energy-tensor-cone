# TODO.md: Next Steps for energy-tensor-cone Project

These items focus on verification to ensure correctness, steps include cross-checks against literature, automated testing, and modular validation. This minimizes errors before referee review. Prioritize these before deeper expansions.

## Verification-Focused Steps (Priority: High – To Ensure Correctness Before Expansion)
## Verification Item 1: Cross-Check Mathematical Definitions Against Literature
**Task:** Verify core definitions (e.g., Lorentzian space, stress-energy tensor, AQEI integral) in `lean/src/` against standard QFT references. Search and perform code checks to flag discrepancies.

**Mathematical Context:** Confirm that the Lorentzian signature is (-,+,+,...) as in the Lean files, AQEI is \( I_{T,\gamma,g} = \int g(t) T(\gamma(t))(u(t), u(t)) \, dt \geq -B_{\gamma,g} \), and the cone \( C \) is convex but not necessarily scaling-invariant (as noted in README).

**Detailed Instructions:**
- Use web_search tool with query: "Averaged Quantum Energy Inequalities in QFT definitions and bounds Fewster" (reference ~/Code/asciimath/energy-tensor-cone/papers/related/fewster2007.tex).
- Compare results to Lean definitions (e.g., extract from `Lorentz.lean`: `is_timelike v := inner v v < 0`).
- Use code_execution tool to symbolically verify simple cases: Run SymPy code to compute a toy AQEI integral.
- If mismatches (e.g., signature convention), update Lean with comments/corrections.
- Document findings in `docs/verification.md` (create if needed), e.g., "Definition matches Fewster 2007 paper [cite]".
```bibtex
@article{PhysRevD.75.025007,
  title = {Averaged null energy condition in spacetimes with boundaries},
  author = {Fewster, Christopher J. and Olum, Ken D. and Pfenning, Michael J.},
  journal = {Phys. Rev. D},
  volume = {75},
  issue = {2},
  pages = {025007},
  numpages = {7},
  year = {2007},
  month = {Jan},
  publisher = {American Physical Society},
  doi = {10.1103/PhysRevD.75.025007},
  url = {https://link.aps.org/doi/10.1103/PhysRevD.75.025007}
}
```
- Commit: `git commit -m "Verify math definitions against literature"`.

**Sample Code for code_execution (Python/SymPy):**
```python
import sympy as sp

t, rho = sp.symbols('t rho')
g = sp.exp(-t**2)  # Gaussian sampling
I = sp.integrate(g * rho, (t, -sp.oo, sp.oo))  # Toy energy density integral
print(I)  # Expected: sqrt(pi) * rho if rho constant
```
- Run this to verify integral computation; compare to Mathematica logic.

## Verification Item 2: Test and Validate Recent Updates (e.g., Phase 2 in Mathematica, Toy Models in Python)
**Task:** Run end-to-end tests on latest changes (e.g., absolute value logic in `mathematica/search.m`, finite inequality proofs in Python) to ensure no regressions. Include unit tests for reproducibility.

**Detailed Instructions:**
- Run `./run_tests.sh` and inspect outputs (e.g., JSON from Mathematica).
- Add unit tests: In `tests/python_tests.sh`, use pytest to check `analyze_results.py` (e.g., mock JSON input, verify Lean generation).
- Use code_execution to simulate toy model: Execute Python code mimicking finite constraints.
- If errors (e.g., build failures in Lean), debug with `lake build --verbose`.
- Cross-verify with literature: Web_search "convex cone properties in quantum inequalities" to confirm Python/Lean proofs (e.g., closure under addition).
- Log results in `docs/verification.md`: "Phase 2 search yields X near-misses; matches expected bound saturation."
- Commit: `git commit -m "Validate recent updates with tests and literature checks"`.

**Sample Code for code_execution (Python Toy Model Check):**
```python
import numpy as np

# Toy finite constraints: Half-spaces defining cone
def check_convex(T1, T2, alpha, beta, constraints):
    T = alpha * T1 + beta * T2
    return all(c(T) >= 0 for c in constraints)

T1 = np.array([1, 0])  # Sample tensors
T2 = np.array([0, 1])
constraints = [lambda t: t[0], lambda t: t[1]]  # Simple half-spaces
print(check_convex(T1, T2, 0.5, 0.5, constraints))  # Expected: True
```

## Verification Item 3: Prove and Verify Key Theorems in Lean (e.g., Convexity with Infinite Constraints)
**Task:** Complete/verify theorems in `FinalTheorems.lean` (recently updated), using tactics to replace `sorry`. Verify against finite approximations from Python.

**Mathematical Context:** Prove \( C \) is convex: \( T_1, T_2 \in C \implies \alpha T_1 + \beta T_2 \in C \) for \( \alpha, \beta \geq 0 \), via linearity of \( I \). For infinite constraints, approximate with finite subfamilies (Hahn-Banach style).

**Detailed Instructions:**
- In `ConeProperties.lean`, extend proofs (e.g., use `linarith` for linearity).
- Use code_execution to numerically verify: Simulate infinite-to-finite approximation.
- Web_search "extreme rays in convex cones QFT" to confirm conjectures.
- If stuck, add `sorry` with comments: "Awaits topology formalization; verified numerically in Python."
- Build and test: `lake build`; ensure no errors.
- Document in `docs/verification.md`: "Convexity proven for finite case; literature match to [cite]."
- Commit: `git commit -m "Verify and complete Lean theorems"`.

**Sample Lean Proof Snippet (Add to ConeProperties.lean):**
```lean
theorem cone_convex_approx {finite_samplings : List (Worldline × SamplingFunction)} :
  -- Proof for finite subfamily intersection is convex cone
  sorry  -- Replace with: by intros; simp [linearity]; linarith
```

**Sample Code for code_execution (Numerical Verification):**
```python
import numpy as np

def I(T, gamma, g):  # Mock AQEI functional
    return np.dot(T, gamma) * g  # Simplified

B = 1.0
C_check = lambda T: all(I(T, g[0], g[1]) >= -B for g in samplings)
samplings = [(np.array([1,0]), 1), (np.array([0,1]), 1)]  # Finite approx
T1, T2 = np.array([2,2]), np.array([3,3])
print(C_check(0.5*T1 + 0.5*T2))  # Expected: True if T1,T2 in C
```

## Verification Item 4: Draft Paper with Verification Sections and Prepare for Preprint
**Task:** Create `papers/draft.tex` with verified content only. Include a "Verification and Limitations" section.

**Detailed Instructions:**
- Use provided .tex skeleton; add sections from verified math (e.g., definitions, toy proofs).
- Web_search "AQEI survey papers" for citations; include in bib.
- Add figures from Python plots (e.g., near-miss histograms).
- Review: Use browse_page on arXiv.org/search/hep-th?query=AQEI to compare similar papers.
- Commit: `git commit -m "Draft paper with verification emphasis"`.
- Once verified, upload to arXiv as preprint for early feedback (before journal).

These verification items ensure the work is robust; proceed to implementation steps only after. Update TODO.md as items complete.

See `TODO-completed.md` for completed tasks.

## Future Enhancements (Optional)

These are stretch goals beyond the initial scope:

- Scale Mathematica searches to 1e6 trials for more thorough exploration
- Generate and include histogram plots in the paper (requires running Python analysis)
- Compile draft.tex to PDF and perform final formatting review
- Prove additional infinite constraint lemmas in Lean
- Extend formalization to 3+1 dimensional spacetimes
- Target journal submission: Journal of Mathematical Physics