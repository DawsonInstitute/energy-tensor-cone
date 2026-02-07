# TODO.md: Phase 3 - From Toy Polyhedra to the “Full” AQEI Cone

## Where we actually are

- ✅ **Abstract theorem (Lean):** If an AQEI family is given as continuous linear functionals `L : ι → E →L[ℝ] ℝ` with bounds `b : ι → ℝ`, then the admissible set `⋂ i, {x | 0 ≤ L i x + b i}` is closed and convex, and homogenization gives a closed convex cone.
- ✅ **Finite-dimensional evidence (Lean + rational arithmetic):** A discretized/polyhedral approximation (finite basis + finite constraint bank + bounding box) has a nontrivial vertex with full-rank active normals.
- ❌ **Not yet proved:** that the *physically defined* AQEI functionals on the intended infinite-dimensional stress–energy/operator space are continuous linear maps for a specified topology, and therefore that “the full AQEI set” matches the abstract admissible set above.
- ❌ **Not yet proved:** existence of nontrivial extreme rays in the full infinite-dimensional cone (this may require extra structure/assumptions; in infinite dimensions extreme rays can fail to exist or be hard to characterize).

## Phase 3 Objective

Turn the current formalization into a publishable theorem statement by making explicit assumptions (topology + continuity), and (option A) prove a correct infinite-dimensional statement under those assumptions, or (option B) revise the conjecture to a defensible finite-dimensional/projection statement and prove it cleanly.

## Step 1: Choose the model space + topology (blocking)

Pick a concrete `E` for “stress–energy tensors” and a topology that makes the AQEI maps continuous.

- Option 1 (functions): `E` as a space of smooth compactly supported symmetric tensor fields (Fréchet topology).
- Option 2 (distributions): `E` as a distribution space; AQEI functionals become pairings against test functions.
- Option 3 (operator-algebra): `E` as a Banach space of trace-class / bounded operators with weak-* topology.

Deliverables:
- A short design note in `docs/` describing the choice and why it matches AQEI literature.
- Lean definitions: the chosen `E` typeclass instances (`TopologicalSpace`, `AddCommMonoid`, `Module`).

## Step 2: Make AQEI functionals real (not placeholders)

Right now `AQEI_functional` is a stub (`= 0`) and `SamplingFunction`/`Worldline` carry placeholders.

Deliverables:
- Replace the stub with either:
  - a real integral-based definition on the chosen `E`, or
  - an explicit axiom/structure bundling “AQEI functionals are continuous linear maps” (stated clearly as an assumption).
- Prove (or assume, but explicitly) the `FactorsThrough` hypothesis used in `AQEIToInterface.lean`.

## Step 3: State the *correct* infinite-dimensional theorem

Deliverables:
- A Lean theorem in a new file that reads like:
  - “Given a topological vector space `E` and AQEI family `L` of continuous linear maps, the admissible set is closed and convex.”
  - “Homogenization yields a closed convex cone.”
This is mostly already in place, but we need to repackage it as the project’s main theorem with clear assumptions.

## Step 4: Extreme rays — pick a defensible target and prove it

Two realistic paths:

- Path A (finite-dimensional/projection theorem):
  - Prove: for the discretized polyhedral model, there exists a nontrivial vertex/extreme ray.
  - Make the statement mathematically clean (no “rank check only”): define the polyhedron and prove “`v` is a vertex” from full-rank active constraints + satisfaction.

- Path B (infinite-dimensional structure):
  - Investigate whether the full cone has nontrivial extreme rays under your topology/space choice.
  - If not generally true, revise the conjecture to “nontrivial exposed points exist for finite constraint banks / finite-dimensional slices”.

Deliverables:
- A Lean definition of `IsExtremeRay`/`IsExtremePoint` for cones/convex sets.
- A Lean lemma connecting “full-rank active constraints” to “is a vertex” for polyhedra over `ℚ`/`ℝ`.

## Step 5: Paper track (only after scope is correct)

- Keep `papers/aqei_cone_structure.md` as a *technical report draft* until Step 3 and Step 4 are fully honest and theorem-backed.
- Add a “Limitations / Assumptions” section that matches the Lean code.