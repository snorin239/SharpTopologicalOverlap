# Formalization map

This repository proves Theorem 1.1 and a strengthening of Theorem 1.2 of
[*Sharp topological overlap in every dimension*](paper/main.pdf) for every
positive dimension. The [9 November 2026 draft](paper/sharp_topological_overlap.pdf)
and its [LaTeX source](paper/sharp_topological_overlap.tex) are the reference
for the formalization. The development also proves convergence of both
normalized finite minimum sequences.

All public results are available through `import SharpTopologicalOverlap`.
The [blueprint](docs/blueprint.md) explains the proof dependencies and the main
differences between the manuscript argument and its formal implementation.

## Public theorem statements

All declarations below belong to the namespace `SharpTopologicalOverlap`.
The natural-number constant `deletionBound d` is the manuscript's

$$
C_d=\sum_{p=1}^{d}\binom{d+1}{p+1}(d+1-p)\left\lfloor\frac dp\right\rfloor.
$$

Theorem 1.2 (`thm:finite`) is proved in
[`Finite.lean`](SharpTopologicalOverlap/Finite.lean) in every positive dimension.

```lean
theorem finite_overlap_bound {n d : ℕ} (hd : 0 < d) (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤ (overlap f : ℝ)
```

Theorem 1.1 (`thm:main`) is proved in
[`Asymptotic.lean`](SharpTopologicalOverlap/Asymptotic.lean):

```lean
theorem topologicalOverlapConstant_eq_threshold {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = overlapThreshold d
```

Here `overlapThreshold d = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1)`.
The stronger combined endpoint is:

```lean
theorem sharp_overlap_constants {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = affineOverlapConstant d ∧
      affineOverlapConstant d = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1)
```

`tendsto_normalizedMinimumOverlap` and `tendsto_normalizedAffineMinimumOverlap`
prove full sequence convergence to this value, from which the two liminf
identities follow.

## Relation to the full simplex

In the current paper, $\Delta^m$ has $m+1$ vertices, so the corresponding
Lean vertex set is `Fin (m + 1)`. Overlap depends only on the images of the
closed $d$-faces, so restriction from $\Delta^m$ to its $d$-skeleton preserves
overlap. With $N_d=C_d$, `finite_overlap_bound` applies to this restriction
whenever $m+1>N_d$ and gives

$$
\mathrm{ov}(f)\ge
\left(\frac{m+1-N_d}{d+1}\right)^{d+1}.
$$

Theorem 1.2 of the current paper subtracts $N_d\binom{m}{d}$ from this
lower bound.

For Theorem 1.1, the minimum over continuous maps of the skeleton bounds
the full-simplex continuous minimum from below. The full-simplex affine
minimum bounds it from above. Each vertex placement determines an affine
map on the full simplex by barycentric interpolation. Lean defines
`affineSkeletonMap` as its restriction, so the full-simplex affine minimum
equals the formalized affine minimum for each $m$.
[`Overlap/Affine.lean`](SharpTopologicalOverlap/Overlap/Affine.lean)

With normalization by $\binom{m+1}{d+1}$ for $m\ge d$, the two Lean limits
squeeze the paper's normalized continuous minimum to the common limit.

## Representations and conventions

- **Source and target.** Source vertices are `Fin n`. `Simplex V` is Mathlib's
  probability simplex, `Convexity.StdSimplex ℝ V`; `Skeleton V d` consists of
  points supported on at most `d + 1` vertices. A proved homeomorphism identifies
  it with the realization of the abstract skeleton and preserves every closed
  face. The target is `EuclideanSpace ℝ (Fin d)`.
- **Overlap.** `overlap f` is an attained natural-number maximum. It counts
  indexed source faces whose closed images contain a point, so distinct faces
  with coincident images are counted separately.
- **Finite minima and constants.** `minimumOverlap d n` minimizes over all
  continuous maps; `affineMinimumOverlap d n` independently minimizes over all
  vertex placements and their affine interpolation. Both minima are attained.
  Each is divided by `n.choose (d + 1)`, and its real liminf defines the
  corresponding overlap constant. Below `n = d + 1`, real division by zero
  makes the normalized terms zero; these finitely many terms do not affect
  the limits.
- **Chains and cochains.** Coefficients are `ZMod 2`. Simplicial chains use
  TauCeti's ordered chain complex. Source cochains are defined on the full
  simplex, so vertex cocycle identities are checked in degree `d + 1`.
  Singular chains and relative homology use TauCeti's actual constructions.
- **Arithmetic and analysis.** Division in `deletionBound` is natural-number
  division; subtraction and division in the overlap bound are real operations.
  The polynomial degree parameter is the edge cardinality, `d + 1` in the
  manuscript. Coordinate equivalences connect finite functions, simplex
  weights and Euclidean spaces for derivatives and Hessian indices.

## Paper-to-Lean correspondence

Every result listed here is proved. Some intermediate declarations split
or replace results from the draft to suit their role in the proofs.

| Paper item | Main Lean declarations | Source |
| --- | --- | --- |
| Deletion constant, equation `eq:C` | `deletionBound`, `deletionBound_one`, `add_one_le_of_deletionBound_lt` | [Basic](SharpTopologicalOverlap/Basic.lean) |
| Simplex, faces and skeleton, §2.1 | `Simplex`, `closedFace`, `openFace`, `Skeleton`, `skeletonRealizationHomeomorph` | [Simplex](SharpTopologicalOverlap/Simplex.lean), [Skeleton](SharpTopologicalOverlap/Skeleton.lean) |
| Overlap, Introduction | `facesAt`, `overlap`, `overlap_attained`, `overlap_le_choose` | [Overlap](SharpTopologicalOverlap/Overlap.lean) |
| Chains, cochains and cocycle parity, §2.2 | `Simplicial.Chain`, `Simplicial.Cochain`, `Simplicial.evaluation_coboundary`, `Simplicial.isCocycle_full_iff_parity` | [Simplicial](SharpTopologicalOverlap/Simplicial.lean) |
| Relative fillings and prism, §2.3 and Lemma 2.2 | `Singular.fills_of_isZero_homology`, `Singular.fills_of_homotopyRel`, `Singular.boundary_prism_zero`, `Singular.boundary_prism_succ` | [Relative](SharpTopologicalOverlap/Singular/Relative.lean), [Prism](SharpTopologicalOverlap/Singular/Prism.lean), [Deformation](SharpTopologicalOverlap/Singular/Deformation.lean) |
| Canonical comparison and supported inverse, Theorem 2.3 and Lemma 2.4 | `Comparison.canonicalHomologyComparison`, `Comparison.supportedComparison`, `Comparison.supportedQ_carriedBy` | [Provider](SharpTopologicalOverlap/Comparison/Provider.lean), [Supported](SharpTopologicalOverlap/Comparison/Supported.lean) |
| Weight polynomials, §2.4 | `WeightPolynomial.weightPolynomial`, `WeightPolynomial.hessian_eq_fderiv_fderiv`, `WeightPolynomial.realized_independenceComplex` | [Polynomial](SharpTopologicalOverlap/Polynomial.lean) |
| Intersection cochains, Lemma 3.1 and Appendix A | `IntersectionData`, `IntersectionWitness`, `exists_intersectionData` | [Intersection](SharpTopologicalOverlap/Intersection.lean), [Existence](SharpTopologicalOverlap/Intersection/Existence.lean) |
| Generic placements, Lemma A.2 | `Geometry.exists_genericPlacement` | [GenericPlacements](SharpTopologicalOverlap/Geometry/GenericPlacements.lean) |
| Spectral rigidity and face index, Lemma 4.1 and Corollary 4.2 | `Spectral.spectral_index_rigidity`, `Spectral.faceCritical_index_ge` | [Partite](SharpTopologicalOverlap/Spectral/Partite.lean), [FaceRestriction](SharpTopologicalOverlap/Spectral/FaceRestriction.lean) |
| Barrier calculus and index persistence, §5 and Lemma 5.7 | `Barrier.barrier_critical_iff`, `Barrier.exists_small_morse_tilt`, `Barrier.exists_barrier_index_persistence` | [Basic](SharpTopologicalOverlap/Barrier/Basic.lean), [Generic](SharpTopologicalOverlap/Barrier/Generic.lean), [Persistence](SharpTopologicalOverlap/Barrier/Persistence.lean) |
| Relative sublevel vanishing, Theorem 5.1 | `Sublevel.sublevel_cycle_fills`, `Sublevel.sublevel_homology_vanishes` | [Sublevel](SharpTopologicalOverlap/Sublevel.lean) |
| Compatible exceptional vertices, Lemma 6.1 | `IntersectionData.exceptionalSet_card_le`, `IntersectionData.exceptionalSet_mono`, `IntersectionData.remainingFamily_hasCocycleParity` | [Deletion](SharpTopologicalOverlap/Deletion.lean) |
| Nested weight spaces, Lemma 6.2 | `IntersectionData.weightSpace_mono`, `IntersectionData.uniform_mem_weightSpace`, `IntersectionData.weightSpace_fills`, `IntersectionData.weightSpace_homology_vanishes` | [WeightSpaces](SharpTopologicalOverlap/WeightSpaces.lean), [Vanishing](SharpTopologicalOverlap/WeightSpaces/Vanishing.lean) |
| Descending contradiction, §6 | `Descending.SimplicialDescent.false`, `Descending.FillingInputs.false` | [Algebra](SharpTopologicalOverlap/Descending/Algebra.lean), [Fillings](SharpTopologicalOverlap/Descending/Fillings.lean) |
| Finite overlap bound, Theorem 1.2 | `finite_overlap_bound` | [Finite](SharpTopologicalOverlap/Finite.lean) |
| BMN upper construction, Theorem 7.1 | `BMN.exists_configuration`, `BMN.exists_configuration_polynomial_error`, `BMN.exists_affine_overlap_bound`, `BMN.exists_affineSkeletonMap_overlap_bound` | [BMN](SharpTopologicalOverlap/BMN.lean) |
| Normalization and finite minima, Introduction and §7 | `minimumOverlap`, `affineMinimumOverlap`, `normalizedMinimumOverlap`, `normalizedAffineMinimumOverlap`, `topologicalOverlapConstant`, `affineOverlapConstant` | [Minimum](SharpTopologicalOverlap/Overlap/Minimum.lean) |
| Sharp asymptotic value, Theorem 1.1 and affine strengthening | `tendsto_normalizedMinimumOverlap`, `tendsto_normalizedAffineMinimumOverlap`, `topologicalOverlapConstant_eq_threshold`, `affineOverlapConstant_eq_threshold`, `sharp_overlap_constants` | [Asymptotic](SharpTopologicalOverlap/Asymptotic.lean) |

The geometric existence theorem constructs its subdivisions, generic placements,
target cycle and all five intersection-cochain properties from the continuous
map. The comparison and sublevel-vanishing inputs to the finite theorem are
also proved. The BMN overlap estimate has uniform error
`2 * d * choose(n - 1, d)`, which is at most `2 * d * n^d`.
For `d ≥ 2`, the geometric theorem also supplies convex position and
affine independence on every top face.

## Verification

The root build checks the complete library. The three theorem audit files
import only the public project root, restate the manuscript conclusions with
explicit constants, and print the transitive axioms of the endpoints:

```sh
lake --wfail build
lake env lean -DwarningAsError=true verification/Theorem12.lean
lake env lean -DwarningAsError=true verification/Theorem71.lean
lake env lean -DwarningAsError=true verification/Theorem11.lean
```

The library contains no `sorry`, `admit`, or project proof axioms. The target
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
See the [README](README.md) for dependency installation and cache commands.
