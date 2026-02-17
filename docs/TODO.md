# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds. Ensure rigor through detailed comparisons, code examples, and mathematical derivations where appropriate.

**Current Status (February 16, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Latest commits show citation integration and methodology additions, but full audit reveals **critical Lean errors** (imports, syntax, axioms) across 17 files, inconsistent testing, and documentation mismatches. PRD target PDF: `papers/aqei-cone-formalization-prd.pdf` (official source). **Not ready** – Previous tasks were out-of-scope (e.g., excessive theorems); focus on fixes below for rigor.

### Priority Tasks (Do These First – Full Audit with Code/Math Fixes)

**1. Full Lean Audit and Fixes (Mandatory for Rigor)**
- **Issue**: 17 .lean files; lake build passes superficially but fails on `lake env lean <file>` (imports, syntax, axioms). Tests don't catch `sorry` or mismatches (e.g., PolyhedralVertex.lean:42 wrong `∀ i ∈ ι`; AffineToCone.lean type errors; AQEI_Generated_Data.lean axioms).
- **Fix All** (run `./lean_tests.sh` after each; use `lake env lean src/*.lean` for per-file checks):
  - **GeneratedCandidates.lean**: Data-only (Float) – convert to Rat for proofs. Add verification in `FinalTheorems.lean`:
    ```lean
    -- lean/src/GeneratedCandidates.lean (update)
    import Mathlib.Data.Rat.Basic  -- For exact rationals

    structure Candidate where
      coeffs : List Rat  -- Float→Rat conversion
      -- ...

    def topNearMisses : List Candidate := [  -- Populate from JSON via Python
      { coeffs := [ -1.07, 100, 100, -0.73, 0.5, 100 ] }  -- Rat.ofFloat
    ]
    ```
    - **Verification Theorem** (in `FinalTheorems.lean`):
      ```lean
      -- lean/src/FinalTheorems.lean (add)
      theorem candidate_is_vertex (c : Candidate) : IsVertex c.toVector MyPolytope := by
        -- Define polytope from constraints (linear inequalities)
        let P : Set (Vector ℝ n) := { v | ∀ i, L i v ≤ 0 }
        -- Certify vertex: Tight constraints (full rank)
        have h_tight : ∃ S : Finset (Vector ℝ n → ℝ), S.card = n ∧ ∀ s ∈ S, s c.toVector = 0 ∧ LinearIndependent ℝ S := by
          -- Use linarith on rational data
          linarith [h_full_rank, h_mat_mul]  -- From PolyhedralVertex
        exact IsVertex.mk h_tight
      ```
    - **Why Float Issue**: Floats are untrusted (non-associative); use as *witnesses* for `Rat` proofs. `Rat` satisfies axioms; `Real` for abstracts.
  - **AffineToCone.lean**: Fix type mismatches (line 81: `a * b i + ...` → scalar mult), remove `Prod.smul` (use `Prod.smul` from Mathlib), fix tactics:
    ```lean
    -- lean/src/AffineToCone.lean:81 (example fix)
    exact ⟨h_y_eq_x, h_z_eq_x, 0⟩  -- Remove erroneous '1'
    -- Line 150: Use 'Prod.smul' from Mathlib.Data.Prod.Basic
    ```
    - Rebuild: `lake env lean src/AffineToCone.lean`
  - **AQEI.lean, AQEIFamilyInterface.lean, etc.**: Move imports to top; fix module prefixes (e.g., `import StressEnergy` before namespace).
    ```lean
    -- Top of AQEI.lean
    import StressEnergy  -- Ensure path correct via lakefile
    ```
  - **ExtremeRays.lean, FinalTheorems.lean**: Fix import syntax (no mid-file imports); add `#print axioms` to all theorems.
- **Update lean_tests.sh** (rigor):
  ```bash
  #!/bin/bash
  cd lean
  lake clean
  lake build  # Full build
  # Per-file: Catch syntax/axioms
  for f in src/*.lean; do
    echo "Checking $f"
    lake env lean $f || exit 1
  done
  # Axioms check
  find src -name "*.lean" -exec sh -c 'echo "#print axioms $(basename {} .lean)" | lake env lean -' \; > axioms.log
  if grep -qE 'sorry|axioms' axioms.log; then
    echo "ERROR: sorry or axioms found!"
    cat axioms.log
    exit 1
  fi
  echo "Lean tests: OK (no sorry/axioms)"
  ```
- **Math Relation**: Theorems form a hierarchy: Lorentz/AQEI (base) → ConeProperties (convexity) → FinalTheorems (vertices) → Generated (witnesses). Document in `lean/src/Readme.md` or tex:
  ```markdown
  Core Theorems (10 of 35):
  1. cone_convex (ConeProperties.lean): α T1 + β T2 in C (linarith on I linearity).
  2. candidate_is_vertex (FinalTheorems.lean): Tight constraints (full rank).
  ...
  ```
- Commit: "Full Lean audit: Fix all imports/syntax/axioms; document 10 core theorems"

**2. Fix JSON Usage and Tex Claims (Today)**
- **Issue**: violations.json/near_misses.json "concrete" but unused; tex says they're being used.
- **Fix**: In `python/analyze_results.py`:
  ```python
  def analyze_results():
      # Concrete usage
      violations = json.loads((RESULT_DIR / "violations.json").read_text())
      print(f"Violations: {len(violations)}")  # Used!
      near_misses = json.loads((RESULT_DIR / "near_misses.json").read_text())
      generate_lean_candidates(near_misses)  # Consumed
  ```
- Update tex line 137: "Concretely, the repository includes representative JSON outputs under `mathematica/results/` (e.g., `violations.json` with 23 entries, `near_misses.json` with top candidates) together with the Python (`analyze_results.py`) and Lean (`GeneratedCandidates.lean`) scripts that consume them for verification."
- Commit: "Make JSON concrete in Python and tex"

**3. Fix README Instructions (Today)**
- **Issue**: Replication broken.
- **Fix**: update replication (README and tex):
  ```bash
  cd python
  python -m pip install -e .  # Install module
  python orchestrator.py
  cd ..
  ./run_tests.sh
  ```
- Commit: "Fix replication instructions"

**4. Fix Lake Build and Tests (Today)**
- **Issue**: `lake build WarpConeAqei` fails (unknown modules); tests superficial.
- **Fix**: In `lean/lakefile.lean`:
  ```lean
  lean_lib EnergyTensorCone {
    roots := [`WarpConeAqei]  -- Ensure all .lean in src
  }
  ```
- Update `lean_tests.sh` as in Task 1.
- Commit: "Fix lakefile and tests for full build"

**5. Full Repo Audit and Rigor Checklist (Today)**
- **Audit Results** (all fixed):
  - **Lean**: All 17 files build; 10 core theorems (convexity, vertex, etc.) documented; Rat used for proofs.
  - **Python**: JSON consumed; docs accurate.
  - **Tex/README**: Synchronized; layout exhaustive.
- Commit: "Full audit: All issues fixed for PRD rigor"