# Theorem 1.2 verification

The public declaration [`SharpTopologicalOverlap.finite_overlap_bound`](../SharpTopologicalOverlap/Finite.lean)
proves Theorem 1.2 (`thm:finite`) of the [reference source](../paper/sharp_topological_overlap.tex#L66):

```lean
theorem finite_overlap_bound {n d : ℕ} (hd : 2 ≤ d) (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤ (overlap f : ℝ)
```

The constant in [`Basic.lean`](../SharpTopologicalOverlap/Basic.lean) is exactly

```lean
def deletionBound (d : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 1 d, (d + 1).choose (p + 1) * (d + 1 - p) * (d / p)
```

Thus `d / p` is the manuscript's floor, with `1 ≤ p ≤ d`.
The hypothesis is the strict natural-number inequality `C_d < n`.
In the conclusion both `n` and `C_d` are cast to `ℝ` before subtraction;
the denominator is real and the exponent is the natural number `d + 1`.

[`Skeleton.lean`](../SharpTopologicalOverlap/Skeleton.lean) defines the source by
probability vectors with support size at most `d + 1` and proves the
weights-preserving `skeletonRealizationHomeomorph` with the realized full-simplex skeleton.
[`Overlap.lean`](../SharpTopologicalOverlap/Overlap.lean) counts closed source
`d`-faces whose images contain a common point, counting distinct source faces separately.
Its `overlap_attained` proves that the maximum occurs at an actual point of `ℝ^d`.

All providers in [`Finite/Assembly.lean`](../SharpTopologicalOverlap/Finite/Assembly.lean)
are discharged: `Comparison.canonicalHomologyComparison` supplies the canonical
affine comparison, and `Sublevel.sublevel_homology_vanishes` supplies ordinary
relative singular homology over `ZMod 2` for every degree `j ≤ d`, including zero.
The sublevel theorem uses actual barrier-index persistence, Morse-band fillings,
the interior push, its prism, and the retracting neighborhood of the zero set.
The unconditional `IntersectionData.weightSpace_fills` and
`IntersectionData.weightSpace_homology_vanishes` also check independently.

The local probes `.lake/ProviderCoreAudit.lean` and `.lake/FinalProviderAudit.lean`
passed `lake env lean`. They reconstruct the finite proof from the concrete
providers, expand the entire `C_d` sum in the theorem statement, and derive
the bound for `overlapCount f y` at an attained target point `y`.
`.lake/PublicSublevelAudit.lean` also checked both public sublevel signatures.

The persistent audit [`verification/Theorem12.lean`](../verification/Theorem12.lean)
imports only the project root and checks the expanded manuscript bound,
an attained overlap point, and all public provider axioms. Run
`lake env lean verification/Theorem12.lean`; this check passed.

`#print axioms` for `finite_overlap_bound`, the canonical comparison, both
public sublevel endpoints, both weight-space endpoints, and all probe theorems
reported exactly `[propext, Classical.choice, Quot.sound]`.
The checked dependency chain has no `sorry`, `admit`, or project proof axioms;
a repository-wide Lean-source scan also found none. The reference paper is unchanged.

Targeted final-provider builds passed. The final umbrella `lake build`,
including the public `Finite` import, passed (9789 jobs).
