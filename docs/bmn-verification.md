# Theorem 7.1 verification

Theorem 7.1 is formalized in `SharpTopologicalOverlap/BMN.lean` and exported
through the public project root. Verification date: 10 November 2026.
The reference manuscript has not been edited.

## Checked statement

For every `d ≥ 2` and every `n : ℕ`, `BMN.exists_configuration` constructs
`p : Fin n → EuclideanSpace ℝ (Fin d)` satisfying:

- `ConvexIndependent ℝ p`, hence injectivity and exactly `n` image points;
- affine independence of every `(d+1)`-element source subset;
- for every query `r`,
  $$
  \#\{\sigma:|\sigma|=d+1,\ r\in\operatorname{conv}(p(\sigma))\}
  \le \left(\frac{n}{d+1}\right)^{d+1}
       +2d\binom{n-1}{d}.
  $$

`BMN.exists_configuration_polynomial_error` gives the manuscript form
with explicit uniform error `2*d*n^d`. Convex independence also proves
`BMN.convexHull_injective_of_convexIndependent`, so distinct source
subsets represent distinct spanned geometric hulls.

`BMN.exists_affine_overlap_bound` and
`BMN.exists_continuous_overlap_bound` construct actual continuous maps
on `Skeleton (Fin n) d` with the same bound. Their faces are closed,
and `image_affineSkeletonMap_face` identifies each image with its full
convex hull, including the boundary.

## Proof dependencies and boundary checks

The configuration is chosen before the query. Its coordinates come from
an explicit rapidly growing sequence, ordered first by coordinate and
then source vertex. The convex-position proof exposes each vertex by an
explicit linear functional. Positive augmented determinants prove affine
independence.

For each query inside the coordinate box, the construction deletes at
most `2*d` source vertices. It proves the two interleaving inequalities
by adjacent-transposition determinant contradictions. Closed-hull
membership supplies nonnegative replacement determinants, without an
interior-membership assumption. The type coloring, transversal count,
AM–GM bound and exact incident-face error are then constructed internally.
No coloring, determinant-sign or geometric-provider premise remains in
the final theorem.

The proofs cover empty and small configurations, query/source coordinate
equalities, closed-simplex boundaries, empty color classes, repeated
deleted neighbors, and the first-coordinate transposition. The persistent
verification harness also checks an empty configuration and the reference
normalizations `overlapThreshold 2 = 2/9` and
`overlapThreshold 3 = 3/32`.

## Normalization

`BMN.normalized_error_eq` proves, for `d+1 ≤ n`, that the error divided by
`choose(n,d+1)` is exactly `2*d*(d+1)/n`.
`BMN.tendsto_choose_div_pow` proves the factorial conversion by the finite
product of factors `1-i/n`. Consequently
`BMN.tendsto_normalized_bmn_bound` has limit
`overlapThreshold d = (d+1)!/(d+1)^(d+1)`.

`BMN.eventually_exists_normalized_overlap_lt` states that for each
`ε > 0`, every sufficiently large `n` has a continuous map whose
binomially normalized overlap is below `overlapThreshold d + ε`.
The minimum-over-maps definition and final liminf equality of Theorem 1.1
are subsequent work.

## Reproduction and axiom audit

Run from the repository root:

```powershell
lake --wfail build
lake env lean -DwarningAsError=true verification/Theorem71.lean
lake env lean -DwarningAsError=true verification/Theorem12.lean
```

All three commands passed. The full warning-free build completed 9825
jobs. Both persistent verification files passed with warnings treated as
errors; the Theorem 1.2 audit remains unchanged and successful.

Theorem 7.1's harness imports only `SharpTopologicalOverlap`. It expands
the source-face filter in the manuscript statement, checks the continuous
and normalized upper bounds, and audits the major intermediate and final
endpoints. The transitive reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The new proof dependencies contain no
`sorry`, `admit`, or project axiom replacing a proof.
