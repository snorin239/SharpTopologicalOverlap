# Strengthened Theorem 1.1: topological and affine overlap

The target is, for every natural number `d` with `2 ≤ d`,

\[
c_d^{\mathrm{top}}=c_d^{\mathrm{aff}}
=\frac{(d+1)!}{(d+1)^{d+1}}.
\]

The request's `c^{add}` is interpreted as `c^{aff}`, the affine constant
specified in the same request. The reference manuscript is preserved.

## Definitions and dependencies

For each `n`, take the least natural overlap among continuous maps from
`Skeleton (Fin n) d` to `EuclideanSpace ℝ (Fin d)`. For the affine version,
take the least overlap of `affineSkeletonMap d p` over all vertex placements
`p : Fin n → EuclideanSpace ℝ (Fin d)`. Placements may have coincident
vertices, and overlap continues to count indexed source faces separately.
Normalize both minima by `n.choose (d + 1)` and define each constant as
the real liminf at `Filter.atTop`, exactly as in the manuscript.

The proof establishes convergence of both sequences, which also proves
their liminf values. The dependency chain is:

1. Attained natural minima; the topological minimum is at most the affine
   minimum; both normalized sequences lie in `[0,1]`.
2. `finite_overlap_bound` gives an eventual lower bound for the normalized
   topological minimum. Its normalized numerical bound tends to
   `overlapThreshold d`, using the checked factorial asymptotic
   `BMN.tendsto_choose_div_pow`.
3. `BMN.exists_affine_overlap_bound` gives a numerical upper bound for the
   affine minimum. `BMN.tendsto_normalized_bmn_bound` proves its limit.
4. Squeeze both sequences between these convergent numerical bounds;
   apply `Filter.Tendsto.liminf_eq` to obtain the constants.

All inequalities involving a positive binomial denominator are applied
on the tail `deletionBound d < n`, which implies `d + 1 ≤ n`. The zero
denominators at small `n` use Lean's total real division and do not affect
either limit.

## Division of work, before implementation

- The minimum-definitions agent owns `Overlap/Minimum.lean`: definitions,
  attainment, finite comparisons, and normalized elementary bounds.
- The lower-limit agent owns `Overlap/Lower.lean`: normalization of
  Theorem 1.2 and convergence of its numerical lower bound.
- The statement-audit agent checks the affine class, exact quantifiers,
  library interfaces and boundary cases; it then independently verifies
  the root-import-only endpoint statements and axiom dependencies.
- The primary agent owns `Asymptotic.lean`, root exports, the final
  assembly, documentation, and the project-wide build.

## Acceptance checks

Check each new module with `lake env lean`, run the warning-free full
build, and run a root-import-only `verification/Theorem11.lean` harness.
Audit the endpoint axioms, requiring only `propext`, `Classical.choice`,
and `Quot.sound`. Check the expanded factorial statement and equality
of the two constants, and ensure no placeholders or new project axioms
were introduced.
