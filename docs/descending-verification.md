# Block F verification

The modules under `Descending/` implement §6.3 of the manuscript from
explicit comparison and relative filling inputs, as allowed by blueprint
§2 and execution-order item 3. The unconditional finite theorem remains
open until those providers are constructed.

`Incidence.lean` transposes the actual target simplicial boundary, proves
its square is zero, and identifies the transpose with the sum over
cofaces. This supplies both the two-step cancellation and the top-cycle
initialization. Its pairing identity is a checked finite-sum interchange.

`Algebra.lean` proves that complementary-degree simplicial descent data
are impossible. The evaluation is constant across adjacent target
degrees, vanishes at target vertices by the full-source cocycle equation,
and equals one at the top by intersection normalization.

`Fillings.lean` constructs the singular chains by induction on increasing
source degree. A layer includes its coface-cycle invariant, carriers,
filling chain and residual chain. The relative-cycle condition for the
next layer follows from boundary naturality, cancellation, and nesting.
The supported chain map then gives the required simplicial descent data.
Target vertices use source filling chains in degree `d+1`.

`FillingInputs` lists the remaining external providers explicitly:
the nested pairs, their actual relative fillers, the common initial
zero-chain in every top carrier, a degree-preserving chain map with its
prescribed value there, and annihilation on each smaller carrier. These
are proof inputs rather than axioms or existence assertions.

The primary agent checked the degree arithmetic, nesting direction,
base initialization, coface cancellation, and terminal evaluation.
All three implementation modules passed their Lean checks.
Their module build and the root `lake build` passed (9617 jobs for the
root). The transitive axiom audit of `transposeBoundary_squared`,
`cofaceSum_cycle`, `SimplicialDescent.false`,
`FillingInputs.toSimplicialDescent`, and `FillingInputs.false` found only
`propext`, `Classical.choice`, and `Quot.sound`.
