# Block H verification

The four `Singular` modules implement the singular support, relative filling,
and prism interfaces specified in blueprint §4.

`CarriedBy` is membership in the range of the actual chain map of a subspace
inclusion. `carriedBy_iff_support` uses TauCeti's concrete Finsupp equivalence
and subspace simplex range theorem to prove the exact support criterion.
Inclusion is injective, chain images are compact finite unions, and images
of sums and pushforwards obey inclusions allowing cancellation.

The relative filling proof passes to the actual short exact sequence of
relative singular chain complexes. Homology vanishing makes the relative
complex exact; a relative boundary lifts through the surjective quotient
map, and the residual kernel lifts from the subspace. Degree zero is
included using the zero outgoing differential. `fills_of_isZero_homology`
retains both subset carriers in the original ambient space.

The prism is the library's chain homotopy for the given topological
homotopy, with separate zero/successor identities. Restricting the homotopy
to source and target carriers and using naturality proves its carrier
bound. Taking the source carrier to be a chain's own image proves the
track-image bound. Strong deformation retracts give concrete fillings via
TauCeti's exact relative vanishing theorem; `fills_chain` proves the
finite nested-pair consequence directly with actual filling chains.

Each module passed `lake env lean` and its module build. The root imports
all four modules, and `lake build` passed (9609 jobs). A transitive audit
of nine endpoints (support equivalence, compact image, injective inclusion,
both relative filling interfaces, nested pairs, prism identity, prism image
bound, and deformation-retract fillings) found only `propext`,
`Classical.choice`, and `Quot.sound`.

The source manuscript was unchanged. No comparison, spectral, or sublevel
claim is assumed by this block.
