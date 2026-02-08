# TODO.md – energy-tensor-cone

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, with Lean formalization + computational evidence.

**Current Status (as of February 7, 2026)**: Paper at Zenodo (https://zenodo.org/records/18522457), LaTeX draft (`aqei-cone-formalization.tex`) with bib integration, Lean theorems advancing (some 'sorry' placeholders), Mathematica/Python pipeline functional. Journal submission in progress; address form fields below.

### Priority Tasks (Do These First)

**1. Update README.md for Publication Readiness (Today)**
- README.md:29 about Lean skeleton with 'sorry': This is acceptable for publication in society journals as long as core theorems are proven and 'sorry' are for extensions/future work. Many formal verification papers publish partial formalizations; emphasize in README/paper that it's a proof-of-concept with key lemmas verified.
- Changes to README.md: Add Zenodo DOI badge (`[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18522457.svg)](https://doi.org/10.5281/zenodo.18522457)`), link to journal submission intent, note 'sorry' as placeholders for ongoing work, and add usage instructions for replication (e.g., "Run `./run_tests.sh` to verify"). Update any outdated sections (e.g., add "Published at Zenodo").
- Commit: "Update README for Zenodo integration"

**2. Integrate Zenodo Upload into Websites and GitHub (Today)**
- Update ~/Code/asciimath/www/index.html: Add a new <li> under publications: `<li><a href="https://zenodo.org/records/18522457">Convex Cone of Energy Tensors under AQEI: Formal Verification and Computational Exploration (Zenodo, 2026)</a></li>`. Include abstract snippet and GitHub link.
- Update ~/Code/asciimath/.github/profile/README.md: Add under "Recent Publications": `- [Convex Cone of Energy Tensors under AQEI](https://zenodo.org/records/18522457) - Formal Lean proofs and Mathematica searches for QFT energy cones. Repo: [energy-tensor-cone](https://github.com/DawsonInstitute/energy-tensor-cone)`.
- Commit to those repos: "Add Zenodo paper link to institute sites"

**3. Changes to aqei-cone-formalization.tex and .bib (Today)**
- tex: Add data statement as above; fix any remaining ? citations by re-running bibtex; move file structure to appendix or shorten to "Key files: lean/src/FinalTheorems.lean (proofs), mathematica/search.m (searches) – full details at GitHub."
- bib: Verify all keys match tex citations; add any missing from prior (e.g., wald1994, hawking1973 if not present).

### Final Pre-Submission Checklist
- Full LaTeX build clean.
- Upload supplements zip (lean/src, mathematica, python, tests).