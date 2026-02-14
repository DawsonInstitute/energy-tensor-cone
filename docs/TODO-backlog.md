# TODO-backlog.md

This file tracks lower-priority tasks for the energy-tensor-cone project.

- Add items here when they are not urgent, or when they are blocked behind higher-priority submission work.
- Move items into docs/TODO.md when they become active.
- Move completed items into docs/TODO-completed.md.

---

## Archived: Literature Expansion Planning (Feb 2026)

The references we're adding (or expanding upon) are primarily to address the CQG desk rejection's feedback on insufficient comprehensive overview of related research. Based on the project's focus (AQEI cones, formal verification, computational approximations), prioritize expanding the literature review in `papers/aqei-cone-formalization.tex` with 10-15 more citations for depth in QFT energy inequalities, convexity in cones, and formal methods. I'll list them below, grouped by category, with BibTeX entries (already added to `aqei-cone-formalization.bib`).

Of these, **only a subset need to utilize LaTeX source** for verification work (e.g., to cross-check math proofs, extract equations for comparisons, or validate Lean formalizations). BibTeX + abstracts are enough for basic citation.

### References to Add/Expand

#### Core AQEI/QEI Papers (bounds/comparisons)
- Fewster, Christopher J. “A General Worldline Quantum Inequality.” Classical and Quantum Gravity 17, no. 9 (2000): 1897. https://doi.org/10.1088/0264-9381/17/9/302.
	- **Use LaTeX? Yes, from papers/related/fewster2000.tex** – For extracting worldline integral bounds to compare Gaussian results.

- Fewster, Christopher J., and Eleni-Alexandra Kontou. “Quantum Strong Energy Inequalities.” Physical Review D 99, no. 4 (2019): 045001. https://doi.org/10.1103/PhysRevD.99.045001.
	- **Use LaTeX? Yes, from papers/related/fewster2019.tex**

- Ford, L. H., and Thomas A. Roman. “Quantum Field Theory Constrains Traversable Wormhole Geometries.” Physical Review D 53, no. 10 (1996): 5496–507. https://doi.org/10.1103/PhysRevD.53.5496.

- Fewster, Christopher J., and Jacob Thompson. “Quantum Energy Inequalities along Stationary Worldlines.” Classical and Quantum Gravity 40, no. 17 (2023): 175008. https://doi.org/10.1088/1361-6382/ace233.
	- **Use LaTeX? Yes, from papers/related/fewster2023.tex**

#### Convexity/Cones
- Ziegler, Günter M. Lectures on Polytopes. Springer, 1995. https://doi.org/10.1007/978-1-4613-8431-1.

- Rockafellar, Ralph Tyrell. Convex Analysis. Princeton University Press, 1970. https://doi.org/10.1515/9781400873173.

#### Formal Methods / Lean Context
- Moura, Leonardo de, and Sebastian Ullrich. “The Lean 4 Theorem Prover and Programming Language.” CADE 28 (2021). https://doi.org/10.1007/978-3-030-79876-5_37.

- Buzzard, Kevin, Johan Commelin, and Patrick Massot. “Formalising Perfectoid Spaces.” CPP 2020. https://doi.org/10.1145/3372885.3373830.

### Expanded List of Additional References

Added to `aqei-cone-formalization.bib` already; cite in intro/discussion.

- Mandrysch, Jan. “Numerical Results on Quantum Energy Inequalities in Integrable Models at the Two-Particle Level.” Physical Review D 109, no. 8 (2024): 085022. https://doi.org/10.1103/PhysRevD.109.085022.
	- **Use LaTeX? Yes, available in papers/related/mandrysch2024.tex**

- Bostelmann, Henning, Daniela Cadamuro, and Jan Mandrysch. “Quantum Energy Inequalities in Integrable Models with Several Particle Species and Bound States.” Annales Henri Poincaré 25, no. 10 (2024): 4497–542. https://doi.org/10.1007/s00023-023-01409-8.
	- **Use LaTeX? Yes, available in papers/related/bostelmann2024.tex**

- Kontou, Eleni-Alexandra. Wormhole Restrictions from Quantum Energy Inequalities. 2024. https://doi.org/10.48550/ARXIV.2405.05963.
	- **Use LaTeX? Yes, available in papers/related/kontou2024.tex**

- Hovhannisyan, Karen V., and Alberto Imparato. “Energy Conservation and Fluctuation Theorem Are Incompatible for Quantum Work.” Quantum 8 (2024): 1336. https://doi.org/10.22331/q-2024-05-06-1336.

Heuristic target: ~20 well-integrated references is generally sufficient for PRD; prioritize weaving them into narrative over raw count.
