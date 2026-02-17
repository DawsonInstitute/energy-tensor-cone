# On the Nontrivial Convex Structure of Averaged Quantum Energy Inequalities

## Abstract

We formalize an abstract “AQEI admissible set” as an (in general infinite) intersection of affine half-spaces cut out by continuous linear functionals on a topological real vector space. In Lean 4, we verify that this admissible set is closed and convex, and that its homogenization yields a closed convex cone in one higher dimension.

Separately, we implement a reproducible finite-dimensional toy/discretized model (Gaussian basis in 1+1D with a finite bank of sampled constraints) and exhibit a nontrivial vertex of the resulting polyhedron, verified in Lean using exact rational arithmetic on the active constraint normals.

Important scope note: connecting these abstract theorems to the *full* QFT-defined AQEI constraints over an infinite-dimensional operator/function space requires specifying the topology on the stress–energy model space and proving the AQEI functionals are continuous linear maps with respect to that topology. This project currently treats that connection as an explicit assumption (see the bridge layer).

## 1. Introduction

The averaged null energy condition (ANEC) and its generalizations, known as Averaged Quantum Energy Inequalities (AQEI), place lower bounds on the integrated stress-energy tensor along worldlines...

## 2. Formal Framework

We model the AQEI conditions as a family of affine inequalities on a topological vector space $E$:
$$ \langle L_\gamma, T \rangle + B_\gamma \ge 0 $$
where $\gamma$ indexes the set of worldlines and sampling functions.

### 2.1 Convexity and Closure (Abstract)

Using Lean 4, we have formally proven that for any family of continuous linear functionals $L$ and bounds $B$, the admissible set:
$$ \mathcal{A} = \{ T \in E \mid \forall \gamma, \langle L_\gamma, T \rangle \ge -B_\gamma \} $$
is closed and convex. The formal proofs are available in `AQEIFamilyInterface.lean` and `AffineToCone.lean`.

## 3. Existence of Extreme Rays

A central question is whether the geometry of $\mathcal{A}$ allows for "sharp" solutions that saturate multiple constraints simultaneously—nontrivial extreme rays.

### 3.1 Computational Verification (Finite-Dimensional Approximation)

We discretized the problem onto a finite basis of wave-packets and employed high-precision linear programming to search for vertices of the admissible polytope.
- **Basis**: $N=100$ Gaussian wave-packets with spin-2 polarization (scaled from initial N=6 for richer geometric exploration).
- **Constraints**: 500 randomly generated AQEI bounds (scaled proportionally).
- **Result**: We identify candidate vertices $v \in \mathbb{R}^{100}$ saturating constraint systems (including sampled AQEI constraints + box/normalization constraints used to bound the LP).

### 3.2 Formal Proof of Rank

To verify results rigorously, we export candidate solutions and active constraints to exact Rational arithmetic in Lean (`AQEI_Generated_Data_Rat.lean`). We implemented a rational Gaussian elimination algorithm (`VertexVerificationRat.lean`) and formally proved:

**Theorem 1 (Full-rank active normals in the discretized model).**
For the finite-dimensional discretization, the rank of the active constraint-normal matrix governing a candidate vertex solution $v$ matches the dimension of the basis space. In particular, within this discretized/polyhedral approximation (including the bounding box constraints), $v$ is an isolated intersection of the active supporting hyperplanes.

*Note: The formal Lean verification currently uses the N=6 basis (rank 6), while the computational search has been scaled to N=100 for richer exploration.*

## 4. Conclusion

What is proved in Lean today is a robust *abstract* convex-analytic statement: admissible sets defined by continuous affine inequalities are closed and convex, and homogenization produces a closed convex cone in one higher dimension.

What is additionally verified is the existence of a nontrivial vertex in a concrete finite-dimensional discretization. This is evidence that finite constraint banks can yield polyhedral cones with sharp boundary structure, but it is not yet a universal theorem about the full infinite-dimensional AQEI constraint set without (i) a concrete choice of model space/topology for stress–energy and (ii) a proof that the physically defined AQEI functionals extend to continuous linear functionals on that space.
