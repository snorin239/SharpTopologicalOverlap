# Verification of the relative sublevel argument

This note records the dependencies for Theorem 5.1 (`thm:weights`) in
[`paper/sharp_topological_overlap.tex`](../paper/sharp_topological_overlap.tex).
Let `V` be finite and nonempty, let `G` be a `(d + 1)`-uniform family with
cocycle parity, and put

\[
 p=p_G,\qquad \theta=\frac{(d+1)!}{(d+1)^{d+1}},\qquad
 B=\{p<\theta\},\qquad Z=\{p=0\}.
\]

The intended public endpoints in
[`Sublevel.lean`](../SharpTopologicalOverlap/Sublevel.lean) are
`sublevel_cycle_fills` and `sublevel_homology_vanishes`, for every natural
degree `j ≤ d`. The first produces, for each relative cycle `c` carried by
`B`, actual chains `w` and `b` in the same ambient probability simplex with
`c = ∂w + b`, where `w` is carried by `B` and `b` by `Z`. The second states
`IsZero` of the actual relative singular homology of `(B,Z)` over `ZMod 2`.
The source wrappers are present; their final build and axiom audit are
pending the root verification pass recorded below.

## Geometric and analytic ingredients

[`Sublevel/Neighborhood.lean`](../SharpTopologicalOverlap/Sublevel/Neighborhood.lean)
identifies `Z` with the independence precomplex in the full-simplex
realization. TauCeti's cofinal iterated simplicial neighborhoods give an open
set `U` with `Z ⊆ U ⊆ B` and an actual strong deformation retraction onto
`Z`. `Singular.fills_of_homotopyRel` consequently fills relative cycles in
`(U,Z)`. The same module chooses `0 < γ < κ/3` with `{p ≤ 4γ} ⊆ U` once a
positive margin `κ` is supplied.

[`Sublevel/Margins.lean`](../SharpTopologicalOverlap/Sublevel/Margins.lean)
handles the nonzero chain case using its nonempty compact image. It chooses
`κ > 0` such that `4κ ≤ θ` and `p ≤ θ − 4κ` on that image. The zero chain is
filled directly before taking any maximum.

[`Sublevel/PushInside.lean`](../SharpTopologicalOverlap/Sublevel/PushInside.lean)
constructs `ψ_t(μ) = (1−t)μ + tu`. Uniform continuity on the full closed
simplex gives a single `t₀ > 0` such that `|p(ψ_t μ) − p(μ)| < γ` for every
point and every `0 ≤ t ≤ t₀`. Each coordinate at time `t₀` is at least
`t₀ / |V|`, which bounds the logarithmic barrier uniformly on the pushed
simplex.

The barrier pipeline is
[`Barrier/Coordinates.lean`](../SharpTopologicalOverlap/Barrier/Coordinates.lean),
[`MorseAdapter.lean`](../SharpTopologicalOverlap/Barrier/MorseAdapter.lean),
[`Basic.lean`](../SharpTopologicalOverlap/Barrier/Basic.lean),
[`Generic.lean`](../SharpTopologicalOverlap/Barrier/Generic.lean),
[`CriticalLimit.lean`](../SharpTopologicalOverlap/Barrier/CriticalLimit.lean),
[`LimitIndex.lean`](../SharpTopologicalOverlap/Barrier/LimitIndex.lean), and
[`Persistence.lean`](../SharpTopologicalOverlap/Barrier/Persistence.lean).
The actual manifold is `Barrier.openSimplexDomain`, an open subset of the
Euclidean zero-sum hyperplane. These modules prove smoothness and properness
of the barrier, choose arbitrarily small zero-sum Morse tilts, and identify
its critical points and Morse index with the coordinate differential and
tangent Hessian used in the spectral argument. These are the barrier
properties of Lemma 5.6.

`exists_manifold_index_persistence` supplies Lemma 5.7: for
`0 < h₀ < h₁ < θ`, all sufficiently small positive barrier parameters and
sufficiently small tilts have critical index at least `d+1` in `[h₀,h₁]`.
Its compactness proof takes a limit in the closed simplex. The critical
barrier values tend to the polynomial value, and criticality passes to the
support face. Corollary 4.2 supplies the limiting face index. The Hessians
are restricted to that fixed support before applying lower semicontinuity
of the negative index. No convergence of Hessians at disappearing
coordinates is asserted.

## The actual Morse band and the return to the original cycle

[`Sublevel/Parameters.lean`](../SharpTopologicalOverlap/Sublevel/Parameters.lean)
applies persistence to `[2γ, θ−κ]`, chooses `ε > 0` with barrier error below
`γ/2` on the pushed simplex, and then chooses a zero-sum Morse tilt of norm
less than both the persistence bound and `γ/2`. Properness and the Morse
condition give regular levels

\[
 2\gamma<r_0<3\gamma,\qquad
 \theta-2\kappa<r_1<\theta-\kappa.
\]

The margins imply `r₀ < r₁`. The pushed chain image lies in the upper
barrier sublevel, and the pushed zero set lies in the lower one. The upper
sublevel maps into `B`; the lower maps into `U`. The package
`MorseBandData` records these facts, the actual continuous maps, and the
homotopy tracks of the original chain image and zero set.

[`Sublevel/Band.lean`](../SharpTopologicalOverlap/Sublevel/Band.lean)
applies TauCeti's
`IsMorse.isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex`
from `Geometry/Manifold/Morse/Cell/Band.lean`. Its hypotheses are checked for
the actual barrier: the closed band is compact by properness, both levels
are regular, every critical index in the band is at least `d+1`, and
`j ≤ d` implies `j < d+1`. Thus the actual relative homology of the two
barrier sublevels is zero. `Singular.fills_of_isZero_homology` turns this
into supported chains, exported as `barrier_band_fills`.
This specializes the Morse-band statement of Lemma 5.5.

[`Sublevel/CycleFilling.lean`](../SharpTopologicalOverlap/Sublevel/CycleFilling.lean)
first transports this filling back along the open-simplex inclusion.
`endpoint_fill_of_push` checks the map factorization and the upper and lower
carrier images. The result fills `ψ_{t₀#}c` modulo `U`. The supported prism
in [`Singular/Prism.lean`](../SharpTopologicalOverlap/Singular/Prism.lean)
then returns to `c`. Its support stays in the homotopy tracks of the chain's
own image, hence in `B`; its application to the original boundary is
carried by `U`. The residual chain is still a relative cycle modulo `Z`.
`refine_relative_filling` fills that residual chain in `(U,Z)` and combines
the two fillings. This is the final argument in Theorem 5.1, assembled in
[`Sublevel/Assembly.lean`](../SharpTopologicalOverlap/Sublevel/Assembly.lean).

Finally,
[`Singular/Vanishing.lean`](../SharpTopologicalOverlap/Singular/Vanishing.lean)
proves the converse filling criterion. It lifts cycles through the actual
short exact sequence defining relative chains, so the result is `IsZero`
of the stated homology object, rather than a substitute filling predicate
left as an unproved equivalence.

## Degree zero and verification status

The chain complexes are unaugmented. `IsRelativeCycle Z 0 c` is true for
every zero-chain, and the algebraic filling criteria use its actual zero
outgoing differential. `fill_after_push` has a separate degree-zero branch
using the zero-degree prism identity. The band theorem also allows degree
zero. Empty chains, empty families, and one-vertex simplices therefore do
not introduce a positive-degree or positive-manifold-dimension assumption.

The component modules have passed their individual Lean checks and builds;
in particular `Sublevel.Band` and `Sublevel.Parameters` built successfully,
and `Sublevel.Assembly` passed its check with the explicit
`Singular.Deformation` import. Axiom checks of `barrier_band_fills` and
`exists_morseBandData` reported exactly
`[propext, Classical.choice, Quot.sound]`. These checks cover the actual
band theorem and parameter package with their stated persistence input.
The unconditional wrappers `sublevel_cycle_fills` and
`sublevel_homology_vanishes` passed their targeted build (9532 jobs).
An independent downstream check of both public endpoints reported only
`[propext, Classical.choice, Quot.sound]`; neither retains a persistence
or other analytic provider premise.

The separate mathematical review of block W found the deletion homotopy
and face transport to have the required carrier directions. For exceptional
mass `m < 1`, the common coordinate bound has positive scale
`a = (1−(1−r)m)/(1−m)`, giving
`p(new) ≤ a^k p(old) < θ(1−new mass)^k`. This includes `m=0`. The homotopy
fixes the remaining face and hence the smaller independence carrier; its
reversal matches the library's relative deformation theorem. The face-pair
isomorphism uses the same coordinate inclusion on both spaces, with
restriction as inverse. The exact final build and axiom verification of
[`WeightSpaces/Vanishing.lean`](../SharpTopologicalOverlap/WeightSpaces/Vanishing.lean)
is root-pending at the time of this note.
