# TODO.md: Next Steps for energy-tensor-cone Project

This document outlines the next actionable steps to advance the energy-tensor-cone repository (formerly warp-cone-aqei). Each step is self-contained, with precise instructions, mathematical explanations where needed, and code snippets in Python, Wolfram Mathematica, and Lean 4. Focus on implementation fidelity—do not deviate from the provided code or math unless explicitly noted for fixes.

Build on the existing structure and files from previous prompts (e.g., Lean sources, Mathematica script, Python orchestrator). If a file or directory doesn't exist, create it. Use the chat history in `docs/history/history.md` for context, but prioritize these steps. Incorporate any recent changes (e.g., if it updated files, verify and build upon them). If latest changes aren't reflected in the current TODO, this replacement supersedes it.

The project focuses on formalizing the convex cone of stress-energy tensors satisfying Averaged Quantum Energy Inequalities (AQEI) using Lean 4, with computational searches in Mathematica to identify extreme rays or boundary points. Progress toward a paper draft in `papers/` is integrated.

## Step 1: Verify and Update Repository Structure Post-Rename

**Task:** Update any references to the old name (warp-cone-aqei). Create missing files with placeholder content if needed. Commit and push changes.

**Detailed Instructions:**
- Navigate to `~/Code/asciimath/energy/energy-tensor-cone/`.
- Search and replace "warp-cone-aqei" with "energy-tensor-cone" in all files (e.g., using `grep -rl 'warp-cone-aqei' . | xargs sed -i 's/warp-cone-aqei/energy-tensor-cone/g'`).
- Create directories and empty files if missing:
  - `mathematica/search.m` (content from original prompt or refined in Step 3).
  - `lean/lakefile.lean` (content from Step 2).
  - `lean/src/` with files: `Lorentz.lean`, `StressEnergy.lean`, `AQEI.lean`, `ConeProperties.lean` (contents from original; copy-paste if needed).
  - `python/orchestrator.py` and `analyze_results.py` (contents from original and Step 4).
  - `tests/` with scripts: `build_lean.sh`, `python_tests.sh`, `mathematica_tests.sh`, `lean_tests.sh` (contents below).
  - `papers/` if missing: Create with `draft.md` (initial outline) and prepare for .tex.
- Update `README.md` with: "Repository for formalizing the convex cone of energy tensors under AQEI constraints using Lean 4, Mathematica searches, and Python integration."
- Run `git add .`, `git commit -m "Update structure and references post-rename to energy-tensor-cone"`, `git push origin main`.

**Code for tests/build_lean.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../lean"
lake build
if [ $? -eq 0 ]; then
  echo "Lean build successful."
else
  echo "Lean build failed."
  exit 1
fi
```

**Code for tests/python_tests.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../python"
python3 -m unittest discover -v  # Placeholder; add actual tests later
echo "Python tests passed."
```

**Code for tests/mathematica_tests.sh (bash):**
```bash
#!/bin/bash
cd "$(dirname "$0")/../mathematica"
wolframscript -file search.m
if [ $? -eq 0 ]; then
  echo "Mathematica tests successful."
else
  echo "Mathematica tests failed."
  exit 1
fi
```

**Code for tests/lean_tests.sh (bash):**
```bash
#!/bin/bash
./build_lean.sh
```

**Code for run_tests.sh (top-level bash):**
```bash
#!/bin/bash
cd tests
./build_lean.sh
./python_tests.sh
./mathematica_tests.sh
./lean_tests.sh
echo "All tests completed."
```

## Step 2: Implement and Enhance Lean Skeleton

**Task:** Ensure `lean/lakefile.lean` is set up, prove additional lemmas (e.g., convexity with finite constraints), and integrate Copilot suggestions if any.

**Mathematical Context:** Formalize the cone \( C = \{ T \mid \forall \gamma, g, I_{T,\gamma,g} \geq -B_{\gamma,g} \} \), where \( I_{T,\gamma,g} = \int g(t) T(\gamma(t))(u(t), u(t)) \, dt \). Prove convexity: For \( T_1, T_2 \in C \), \( \alpha T_1 + \beta T_2 \in C \) (\( \alpha, \beta \geq 0 \)) via linearity of \( I \).

**Detailed Instructions:**
- Create/update `lean/lakefile.lean` with code below.
- Install/update Lean 4 and Mathlib.
- Run `lake build` in `lean/`; fix errors.
- In `ConeProperties.lean`, complete proofs (replace `admit` with tactics).
- If Copilot updated files, merge changes (e.g., new lemmas).
- Commit: `git commit -m "Enhance Lean skeleton and proofs"`

**Code for lean/lakefile.lean:**
```lean
import Lake
open Lake DSL

package «energy-tensor-cone» {
}

lean_lib EnergyTensorCone {
}

@[default_target]
lean_exe «energy-tensor-cone» {
  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
```

**Example Proof Enhancement in ConeProperties.lean:**
```lean
theorem cone_convex {V : Type} [AddCommMonoid V] [Module ℝ V] {L : LorentzSpace V}
  (bounds : Worldline V L → SamplingFunction → ℝ) :
  ∀ (T1 T2 : StressEnergy V L) (α β : ℝ), 0 ≤ α → 0 ≤ β → satisfies_AQEI T1 bounds → satisfies_AQEI T2 bounds → satisfies_AQEI (α • T1 + β • T2) bounds := by
  intros T1 T2 α β hα hβ h1 h2 γ s
  unfold satisfies_AQEI
  simp [AQEI_functional]  -- Linearity: I(α T1 + β T2) = α I(T1) + β I(T2)
  linarith [h1 γ s, h2 γ s]
```

## Step 3: Scale and Refine Mathematica Search

**Task:** Update `mathematica/search.m` for larger trials, use GPU support, and export more detailed results.
How to use Mathematica's built-in GPU functions that don't require CUDALink:
```wolfram
(* These work without CUDALink *)
DeviceObject functions
TargetDevice -> "GPU"
```

**Mathematical Context:** In 1+1D, search for \( T \) violating/saturating AQEI: Minimize \( I + B \) over random \( a_i, \gamma, g \). Use finite basis to approximate extreme rays.

**Detailed Instructions:**
- Update script (from original) with higher `numTrials=100000`, add `Symmetrize`.
- Test GPU: Use `TargetDevice -> "GPU"` in integrations.
- Run: `wolframscript -file mathematica/search.m`
- Commit: `git commit -m "Scale Mathematica search"`

**Code Addition in search.m:**
```mathematica
Symmetrize[m_] := (m + Transpose[m])/2;
(* Increase numTrials *)
numTrials = 100000;
```

## Step 4: Enhance Python Integration and Analysis

**Task:** Update `python/analyze_results.py` to handle larger results, generate Lean candidates, and add plotting for paper.

**Detailed Instructions:**
- Update file with code below.
- Run `python/orchestrator.py` to test.
- Add pytest for `python_tests.sh`.
- Commit: `git commit -m "Enhance Python analysis"`

**Code for python/analyze_results.py (expanded):**
```python
import json
import matplotlib.pyplot as plt
from pathlib import Path

ROOT = Path(__file__).parent.parent
RESULT_DIR = ROOT / "mathematica" / "results"
GEN_FILE = ROOT / "lean" / "src" / "GeneratedCandidates.lean"

def generate_lean_candidates(near_misses):
    with open(GEN_FILE, 'w') as f:
        f.write("import StressEnergy\n\n")
        for i, miss in enumerate(near_misses[:5]):  # Assume near_misses is list of dicts
            a = miss.get('a', [])  # Coefficients
            f.write(f"def candidate{i+1} : StressEnergy V L := ⟨\n")
            f.write("  fun u v => " + " + ".join(f"{a[j]} * basis{j}(u,v)" for j in range(len(a))) + "\n")  # Approximate bilinear
            f.write("⟩\n\n")

def plot_results(near_misses):
    scores = [miss['val'] for miss in near_misses]
    plt.hist(scores, bins=20)
    plt.savefig(ROOT / 'papers' / 'near_misses_hist.png')

if __name__ == "__main__":
    # Load results (assume JSON)
    near_misses = json.loads((RESULT_DIR / "near_misses.json").read_text()) if (RESULT_DIR / "near_misses.json").exists() else []
    generate_lean_candidates(near_misses)
    plot_results(near_misses)
```

## Step 5: Run End-to-End Pipeline and Document

**Task:** Execute full tests, generate candidates, document in `docs/results.md`.

**Detailed Instructions:**
- Run `run_tests.sh`.
- Log outputs.
- Commit: `git commit -m "End-to-end test results"`

## Step 6: Advance Paper Draft and .tex Creation

**Task:** Expand `papers/draft.md`, create `papers/draft.tex`, prepare for submission.

**Detailed Instructions:**
- Expand markdown with sections from previous response.
- Create .tex with skeleton below.
- Add plots from Step 4.
- Commit: `git commit -m "Advance paper draft"`

**Sample .tex Code for papers/draft.tex:**
```latex
\documentclass{article}
\usepackage{amsmath, amsthm, graphicx, listings}

\title{Convex Cone of Energy Tensors under AQEI}
\author{Charles}
\date{\today}

\begin{document}
\maketitle

\begin{abstract}
Formalization and computation of AQEI cone.
\end{abstract}

\section{Introduction}
The cone \( C \) is defined as...

\includegraphics{near_misses_hist.png}

\end{document}
```

## Next Iterations
- Prove infinite constraint lemmas in Lean.
- Scale searches to 1e6 trials.
- Submit preprint to arXiv after draft completion.
- Target journal: Journal of Mathematical Physics.