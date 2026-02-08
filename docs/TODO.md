# TODO.md – energy-tensor-cone (DawsonInstitute org)

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, combining Lean formalization, computational searches, and verification against known bounds.

**Current Status (February 8, 2026)**: Repo at https://github.com/DawsonInstitute/energy-tensor-cone. Anonymized repo at https://anonymous.4open.science/r/aqei-convex-cone-5789/. CQG submission in double-anonymous mode.

### Priority Tasks (Do These First)

**1. Anonymize Manuscript and Supplements Further for Double-Anonymous CQG (Today)**
- Per IOP checklist, you've made a good faith effort, but to strengthen: Remove **all** links (GitHub, Zenodo, anon repo) from the submission PDF/tex to avoid any traceability. Instead, state: "Code and data are provided as supplementary materials (zip file) for review; full access post-acceptance via public repositories."
- Make main repo **private** temporarily during review (git settings > Danger Zone > Make private) to prevent leaks; revert post-review.
- For supplements-anon.tar.gz README.md: Remove Zenodo badge/link, org name, and any identifiers. Update to:  
  ```
  Anonymized Supplements for "Convex Cone of Energy Tensors under AQEI"

  - Key Files: lean/src/FinalTheorems.lean (proofs), mathematica/search.m (searches), etc.
  - Usage: Run ./run_tests.sh to verify.
  ```
- This meets CQG's double-anonymous requirements (remove names, affiliations, identifiable info; supplements must be anonymized too).
- Commit: "Enhance anonymity in tex, supplements, and repo settings" (commit before privatizing).

**2. Refactor LaTeX Files for Maintainability (Today)**
- Refactor to avoid duplicating code across 3 .tex files (original, CQG, anon). Create shared files:  
  - `papers/common-preamble.tex`: \usepackage, definitions.  
  - `papers/common-content.tex`: Main body (abstract, sections, without author/affil).  
  - `papers/common-bib.tex`: Bibliography commands.  
- In each main .tex: Use `\input{common-preamble.tex}` etc. For anon version, add conditional anonymity (e.g., `\ifanon \else \author{...} \fi`; define `\newif\ifanon` in preamble).
- CQG will get the full non-anon set post-review (Word/TeX/LaTeX with all info).
- Commit: "Refactor LaTeX with shared inputs for common parts"

### Final Pre-Submission Checklist
- Anonymized PDF/supplements ready (no links/names).
- Submit to CQG.
- After submission, update README/sites with CQG status (once public).