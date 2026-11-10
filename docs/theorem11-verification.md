# Strengthened Theorem 1.1 verification

Verification date: 10 November 2026. The reference manuscript is unchanged.

The public endpoint `SharpTopologicalOverlap.sharp_overlap_constants` in
[`Asymptotic.lean`](../SharpTopologicalOverlap/Asymptotic.lean) states:

```lean
theorem sharp_overlap_constants {d : ℕ} (hd : 2 ≤ d) :
    topologicalOverlapConstant d = affineOverlapConstant d ∧
      affineOverlapConstant d =
        ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1)
```

This proves the manuscript's Theorem 1.1 and its affine strengthening.
The request's `c_add` is interpreted as the affine constant `c_aff`.
Only `2 ≤ d` is a hypothesis; there are no geometric, analytic, or
asymptotic provider premises.

## Constants and source fidelity

[`Overlap/Minimum.lean`](../SharpTopologicalOverlap/Overlap/Minimum.lean)
defines the continuous minimum over all continuous maps on
`Skeleton (Fin n) d` with target `EuclideanSpace ℝ (Fin d)`. The affine
minimum ranges independently over all vertex placements and their
`affineSkeletonMap` interpolations. Every facewise affine map is the
barycentric interpolation of its vertex values, so this is the affine
map class. Repeated vertex images are allowed. Source faces remain
indexed and are counted separately, including when images coincide.
`image_affineSkeletonMap_face` identifies closed-face images with their
full convex hulls.

Both finite minima are natural infima of nonempty ranges, with explicit
zero-map or zero-placement witnesses. `minimumOverlap_attained` and
`affineMinimumOverlap_attained` prove attainment; the corresponding
comparison lemmas prove leastness. Dividing their real casts by the
nonnegative common binomial denominator therefore gives exactly the
least normalized overlaps. Both normalized sequences lie in `[0,1]`.

`topologicalOverlapConstant` and `affineOverlapConstant` are independently
defined as the real liminfs of these normalized sequences. Neither is
defined by the target formula or by the other constant.

## Proof and boundary cases

[`Overlap/Lower.lean`](../SharpTopologicalOverlap/Overlap/Lower.lean)
divides the checked `finite_overlap_bound` by `choose(n,d+1)` and proves
that its numerical lower bound tends to `overlapThreshold d`. The limit
uses the exact factorization, for `n ≥ 1`,

\[
\frac{((n-C_d)/(d+1))^{d+1}}{\binom n{d+1}}
=\left(1-\frac{C_d}{n}\right)^{d+1}
 \frac{(n/(d+1))^{d+1}}{\binom n{d+1}}.
\]

The first factor tends to one and the second to the existing factorial
threshold. Subtraction in `n-C_d` occurs in the reals. The finite lower
inequality is applied only on the eventual tail `C_d < n`.

In `Asymptotic.lean`, the affine BMN construction bounds the affine
minimum above, while the attained continuous minimum satisfies the
finite lower bound. The continuous minimum is at most the affine
minimum. The squeeze theorem proves both full limits, exported as
`tendsto_normalizedMinimumOverlap` and
`tendsto_normalizedAffineMinimumOverlap`. Their liminfs follow from
`Filter.Tendsto.liminf_eq`.

For `n < d+1` the binomial denominator is zero and both normalized terms
are zero under total real division; this finite prefix does not affect
the limits. The numerical lower-bound sequence may have negative initial
values, but only its eventual lower-bound property is used. The full
limits require `d ≥ 2`; the numerical lower-bound limit itself holds
for all natural `d`.

## Reproduction and audit

From the repository root:

```powershell
lake env lean -DwarningAsError=true SharpTopologicalOverlap/Overlap/Minimum.lean
lake env lean -DwarningAsError=true SharpTopologicalOverlap/Overlap/Lower.lean
lake env lean -DwarningAsError=true SharpTopologicalOverlap/Asymptotic.lean
lake --wfail build
lake env lean -DwarningAsError=true verification/Theorem11.lean
```

The root-import-only
[`verification/Theorem11.lean`](../verification/Theorem11.lean) expands
both liminf definitions and their natural minima, checks the strengthened
endpoint, the initial no-face terms, and both constants in dimensions
two and three (`2/9` and `3/32`). It also reports transitive axioms for
the minimum comparisons, both limits, and the final endpoints.

The full `lake --wfail build` passed (9831 jobs), and the standalone
`Asymptotic.lean` warning-as-error check passed. A Lean-source scan found
no `sorry`, `admit`, or project proof axioms. Independent reviews checked
the minimum definitions against the manuscript, the lower-limit
factorization, both squeeze arguments, and the small-size conventions.

The root-only `verification/Theorem11.lean` warning-as-error audit passed.
All twelve printed declarations, including both fully expanded liminf
statements, both full limits, and `sharp_overlap_constants`, report only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or project
proof axioms occur. The existing `verification/Theorem12.lean` and
`verification/Theorem71.lean` audits also passed again with
`-DwarningAsError=true` against the updated project root.
