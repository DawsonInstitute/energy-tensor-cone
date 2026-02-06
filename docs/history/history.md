Completed: *Run tests, commit, push* (6/6)

**Done**
- Created public repo: https://github.com/arcticoder/warp-cone-aqei
- Cloned to `~/Code/asciimath/energy/warp-cone-aqei`
- Added it to the multi-root workspace: energy/energy.code-workspace

**Repo Layout + Contents**
- Local entrypoint: run_tests.sh
- Mathematica randomized search (exports `top_near_misses.json`): search.m
- Lean skeleton (typechecks via `lake build`):  
  - Lorentz.lean  
  - StressEnergy.lean  
  - AQEI.lean  
  - ConeProperties.lean
- Python glue + Lean candidate generator:  
  - orchestrator.py  
  - analyze_results.py
- Test harness scripts: tests

**Verification**
- run_tests.sh passes end-to-end (Python smoke tests + fast Mathematica run + `lake build`).
- Initial commit pushed to `origin/main`.
<!-- ------ -->
---
