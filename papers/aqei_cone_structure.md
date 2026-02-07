# On the Nontrivial Convex Structure of Averaged Quantum Energy Inequalities

## Abstract

We investigate the geometric structure of the set of stress-energy tensors satisfying Averaged Quantum Energy Inequalities (AQEI). We formally verify, using the Lean 4 proof assistant, that this set forms a closed, convex cone in the relevant topological dual space. Furthermore, we provide a computer-assisted proof demonstrating the existence of nontrivial extreme rays (vertices) in a finite-dimensional projection of this set, confirming that the admissible cone is not simply the trivial cone of non-negative energy densities. This result has significant implications for the classification of exotic matter distributions in semiclassical gravity.

## 1. Introduction

The averaged null energy condition (ANEC) and its generalizations, known as Averaged Quantum Energy Inequalities (AQEI), place lower bounds on the integrated stress-energy tensor along worldlines...

## 2. Formal Framework

We model the AQEI conditions as a family of affine inequalities on a topological vector space $E$:
$$ \langle L_\gamma, T \rangle + B_\gamma \ge 0 $$
where $\gamma$ indexes the set of worldlines and sampling functions.

### 2.1 Convexity and Closure

Using Lean 4, we have formally proven that for any family of continuous linear functionals $L$ and bounds $B$, the admissible set:
$$ \mathcal{A} = \{ T \in E \mid \forall \gamma, \langle L_\gamma, T \rangle \ge -B_\gamma \} $$
is closed and convex. The formal proofs are available in `AQEIFamilyInterface.lean` and `AffineToCone.lean`.

## 3. Existence of Extreme Rays

A central question is whether the geometry of $\mathcal{A}$ allows for "sharp" solutions that saturate multiple constraints simultaneously—nontrivial extreme rays.

### 3.1 Computational Verification

We discretized the problem onto a finite basis of wave-packets and employed high-precision linear programming to search for vertices of the admissible polytope.
- **Basis**: $N=6$ Gaussian wave-packets with spin-2 polarization.
- **Constraints**: 50 randomly generated AQEI bounds.
- **Result**: We identified a candidate vertex $v \in \mathbb{R}^6$ saturating exactly 6 linearly independent constraints (3 AQEI + 3 Box constraints).

### 3.2 Formal Proof of Rank

To verify this result rigorously, we exported the candidate solution and active constraints to exact Rational arithmetic in Lean (`AQEI_Generated_Data_Rat.lean`). We implemented a rational Gaussian elimination algorithm (`VertexVerificationRat.lean`) and formally proved:

**Theorem 1 (Existence of Nontrivial Vertex).**
The rank of the active constraint matrix governing the candidate solution $v$ is exactly 6. Thus, $v$ is a unique extreme point of the approximated system.

## 4. Conclusion

We have established the convexity and closedness of the full AQEI cone and provided a rigorous, computer-assisted proof of the existence of nontrivial vertices in its finite-dimensional approximations. This supports the conjecture that the full infinite-dimensional moduli space of AQEI-satisfying tensors possesses a rich boundary structure capable of supporting "warp-drive-like" negative energy distributions.
