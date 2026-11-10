# Barrier block verification

`Barrier.exists_manifold_index_persistence` proves the uniform critical-index
bound used in Lemma 5.7 on the actual open-simplex manifold. For a finite
linearly ordered vertex type, a uniform `(d + 1)`-family with cocycle parity,
and a fixed band `0 < h₀ < h₁ < overlapThreshold d`, it supplies `δ > 0` such
that every critical point of the barrier with `0 < ε < δ` and `‖α‖ < δ`
whose barrier value lies in `[h₀, h₁]` has actual manifold Morse index at
least `d + 1`. The conclusion does not require the tilt to have zero sum.

The proof uses the following checked dependencies.

1. `Barrier.Basic` differentiates the actual polynomial, logarithmic barrier
   and linear tilt. Its chart adapters identify criticality and the actual
   manifold Morse index with the zero-sum differential and quadratic form.
   The latter is the polynomial Hessian plus
   `ε * ∑ i, xᵢ² / μᵢ²`. Positive barrier sublevels are compact, giving
   properness. `Barrier.Generic` supplies arbitrarily small zero-sum tilts
   for which the actual barrier is Morse.
2. At a critical point, provided `N * ε ≤ 1` and `‖α‖ ≤ 1`,
   `coordinate_ge_of_critical` gives `μᵢ ≥ ε / (d + 4)`.
   Consequently `critical_logBarrier_bounds` bounds the logarithmic term
   between zero and `N * ε * log ((d + 4) / ε)`, which tends to zero.
3. `faceCritical_of_critical_limit` takes limits of the multiplier equations
   only at coordinates positive at the limit. Thus limits of critical
   points as `ε → 0` and `α → 0` are critical on their own support face.
   `tendsto_critical_barrier_value` combines the preceding logarithmic
   estimate with continuity of the polynomial and tilt, so the limiting
   barrier value equals the polynomial value.
4. `Barrier.LimitIndex` fixes the support of the limiting point and pulls
   the varying barrier Hessian back to that support's tangent space.
   Every denominator in this restricted family is nonzero at the limit,
   so the family is continuous there. The library's lower semicontinuity
   of the negative index and the index inequality for a linear pullback
   yield `eventually_faceIndex_le_barrierIndex_of_tendsto`.
5. `exists_barrier_index_persistence` argues by contradiction with a
   sequence of shrinking perturbation bounds. Compactness of the closed
   probability simplex supplies a convergent subsequence of bad critical
   points. The critical-limit and value lemmas place the limit in the same
   positive strict-subthreshold band. Corollary 4.2 gives face index at
   least `d + 1`; fixed-support index persistence contradicts the chosen
   bad indices. The final theorem transports this result through the
   checked open-simplex chart and Morse-index adapters.

No convergence of the full barrier Hessian is used when coordinates
disappear at the limiting point. The continuous family is defined on the
fixed tangent space of the limiting support.

`lake env lean SharpTopologicalOverlap/Barrier/Persistence.lean` passed.
`lake build SharpTopologicalOverlap.Barrier.Persistence` passed (7988 jobs),
checking its critical-limit and fixed-support dependencies. Direct axiom
audits of both `exists_barrier_index_persistence` and
`exists_manifold_index_persistence` reported only `propext`,
`Classical.choice`, and `Quot.sound`.
