# TODO.md – energy-tensor-cone

**Project Goal**: Submit a high-quality paper on the convex cone of stress-energy tensors satisfying AQEI, with Lean formalization + computational evidence.

**Current Status (as of February 7, 2026)**: Paper draft in LaTeX (`aqei-cone-formalization.tex`), Zotero exporting to `aqei-cone-formalization.bib`, Lean theorems in `FinalTheorems.lean`, Mathematica Phase 2 complete. Recent commits include bib updates and re-exports.

### Priority Tasks (Do These First)

**1. Ford 1978 Citation (Today)**
Cite papers/aqei-cone-formalization.bib:44-56 in the Introduction/Discussion (e.g., “The modern formulation of AQEI originates with Ford (1978)...”).
- For explicit "quantum inequality," use Ford's 1995 paper (`ford1995` in your bib), "Averaged energy conditions and quantum inequalities."
- Update references in `aqei-cone-formalization.tex` to `\cite{ford1978}`.
- Commit: "Correct Ford 1978 citation in bib and tex"

**2. Clean Up Leftover Draft Files (Today)**
- Remove duplicate/old files: `rm papers/draft.tex papers/draft.bib papers/draft.md papers/draft.aux papers/draft.bbl papers/draft.blg papers/draft.log papers/draft.out`
- Untrack them explicitly if needed: `git rm --cached papers/draft.*`
- Ensure `.gitignore` includes `*.aux *.log *.out *.bbl *.blg *.synctex.gz`
- Commit: "Remove leftover draft files and update gitignore"

**3. Fix pdflatex Compilation Errors (Today)**
- **Undefined \affiliation and \email**: Switch to Springer's journal template (svjour3.cls) for CMP compatibility, as `article.cls` doesn't support them.
  - Download Springer LaTeX template: Use web search or direct from Springer (svjour3.cls, natbib.sty).
  - Update documentclass: `\documentclass[smallextended]{svjour3}` (or similar for CMP).
  - Add `\smartqed` if needed.
- **UTF-8 Errors in Listings**: The file tree uses non-ASCII box-drawing characters (e.g., ├──, └──). Replace with ASCII equivalent or use verbatim environment.
  - Edit lines 257-285: Use simple indented text like:
    ```
    lean/
      lakefile.lean
      src/
        Lorentz.lean
        StressEnergy.lean
        ...
    ```
  - Or wrap in `\begin{verbatim} ... \end{verbatim}` instead of lstlisting.
- Run full compilation: `pdflatex aqei-cone-formalization.tex && bibtex aqei-cone-formalization && pdflatex aqei-cone-formalization.tex && pdflatex aqei-cone-formalization.tex`
- Commit: "Fix LaTeX compilation errors and template"

**4. Adjust Template for CMP Submission Requirements (Today)**
Use ~/Code/asciimath/energy/docs/journals/CMP/sn-article-template to update the latex template for CMP.
- CMP (Springer) uses svjour3.cls; affiliation/email appear under author name (as in your PDF— this is standard).
- No special first-page format; it's fine.
- For supplements: CMP allows code/data as supplementary material (zip with repo files).
- Describing file structure (lines 257-285): Appropriate for reproducibility in computational physics/math papers; keep but move to appendix or refer to GitHub repo.
- Commit: "Update LaTeX template for CMP"

**5. Fix Citation Rendering Issues (Today)**
- **[?, ?] for moura2021, community2020**: Run bibtex as above; ensure `\bibliographystyle{plain}` or Springer's style (e.g., spphys.bst).
- **Manual citations at line 191**: Replace "Fewster (2012) arXiv:1208.5399" with `\cite{fewster2012}` (assuming key is fewster2012).
- **Missing Wald (1984) and Hawking & Ellis (1973)
- Update tex: Use `\cite{wald1994}` and `\cite{hawking1973}`.
- Commit: "Fix and add missing citations"

**6. Prepare Journal Submission Supplements Zip (This Week)**
- Include: Full repo zip (or key dirs: lean/src/*.lean, mathematica/search.m, python/*.py, tests/*), generated results (e.g., mathematica/results/*), and a README-supplements.md explaining usage.
- Exclude binaries/PDFs; refer to GitHub for full repo.
- Commit: "Prepare supplements zip"

**7. Additional Edits to aqei-cone-formalization.tex (This Week)**
- Add "Verification and Limitations" section after results: Discuss 1+1D model limits, comparison to analytic bounds, future work on full QFT.
- Improve abstract: Make concise, highlight novelty (Lean + computation for AQEI cone/first formal verification of AQEI cone properties).
- Add figures if possible (e.g., near-miss plots from Python, analyze_results.py plots).
- Ensure all \cite are proper; remove inline arXiv mentions.
- Proofread for typos/math consistency.
- check overfull hboxes (e.g., line 92-93: shorten text).
- Commit: "Edits to LaTeX for polish and completeness"

**8. Additional Citations to Add (Ongoing)**
- Add if relevant: {ford1995} ("Averaged energy conditions and quantum inequalities").
- Ensure all keys match bib.
- {fewster2008}. (downloaded arxiv version to papers/related/fewster2008.tex)
- Update as needed.

**9. Git log fixes**
I didn't set the git username or email until later on in this repo development:
```bash
(base) echo_@hercules:~/Code/asciimath/energy-tensor-cone$ git log
commit 33c866233e0cf8cfaa49816d7b7ce2e7fe340982 (HEAD -> main, origin/main)
Author: Arcticoder <10162808+arcticoder@users.noreply.github.com>
Date:   Sat Feb 7 18:52:23 2026 -0800

    Add new bibliography entry for Ford's 1978 paper and update references in manuscript

commit 260d84e2169bfe723116197a7f510ae1d4f82529
Author: Arcticoder <10162808+arcticoder@users.noreply.github.com>
...

commit 732c5e102400ec9fb77c4548d95dd1f784cf69f3
Author: Your Name <you@example.com>
Date:   Sat Feb 7 07:38:49 2026 -0800
```
Fix the commit author and email so they're all from Arcticoder <10162808+arcticoder@users.noreply.github.com>.

**10. Github repo details**
Update the github repo (DawsonInstitute/energy-tensor-cone) "About" and set Topics for the repo using the `gh` command and/or github api.

### Final Pre-Submission Checklist
- Compile clean PDF.
- Upload to arXiv (categories: math-ph primary, gr-qc/hep-th cross).
- Submit to CMP
