# Verification of the affine comparison and supported inverse

The comparison block proves the canonical affine homology comparison and the
supported chain map needed later in the formalization. Its public endpoint is
`SharpTopologicalOverlap.Comparison.supportedComparison`. This note records
that block's proof dependencies and checks. It makes no claim that the final
assembly of Theorem 1.2 has been completed.

The manuscript references are Theorem 2.3 (`thm:hatcher`) and Lemma 2.4
(`lem:comparison`) in
[`paper/sharp_topological_overlap.tex`](../paper/sharp_topological_overlap.tex),
Section 2.3, “Singular homology.” The numbering is also recorded in the
manuscript's checked auxiliary file. All chains have coefficients
`Simplicial.Coeff = ZMod 2` and are unaugmented.

## Public statements

Let `V` be a finite linearly ordered vertex type and `K` an
`AbstractSimplicialComplex V`. The map `affineChainMapIn K k` sends a simplicial
face with increasing vertices to its affine singular simplex in the coordinate
realization `realizedComplex K.toPreAbstractSimplicialComplex`. Its chain-map
packaging is `affineChainComplexMapIn K`. For every natural degree `k`,
`isIso_homologyMap_affineChainComplexMapIn K k` proves that the homology map of
this particular chain map is an isomorphism. This is the formalized content of
Theorem 2.3.

For `x : V`, with `V` nonempty, `supportedComparison x` provides linear maps
`rho k` from actual singular chains of the full probability simplex to
simplicial chains of the full simplex. The structure records

\[
 \partial\rho(c)=\rho(\partial c),\qquad
 \rho([u])=[x],\qquad
 \rho(S_k(|L|))\subseteq C_k(L)
\]

for every ambient precomplex `L` and every degree `k`. Here `u` is the uniform
probability vector. An ambient precomplex is permitted to omit vertices. The
additional maps `supportedQ x k` preserve the same carriers and satisfy

\[
 \partial Q_0(c)=\iota\rho_0(c)+c,
 \qquad
 \partial Q_{k+1}(c)=c+Q_k(\partial c)+\iota\rho_{k+1}(c).
\]

Thus the endpoint proves Lemma 2.4 and also exports its supporting chain
homotopy. The total order is an explicit formalization parameter; the
manuscript chooses such an order at the start of its proof.

## Why the homology isomorphism is the canonical one

[`Comparison.lean`](../SharpTopologicalOverlap/Comparison.lean) constructs
`affineSimplex` from the increasing vertex enumeration of a face. The facet
identity `affineSimplex_face` gives boundary compatibility after extension by
linearity. The implementation also proves that the affine chain map is
injective, respects inclusions of complexes, and sends a simplicial chain
carried by `L` to a singular chain carried by `realizedComplex L`.
[`Realization.lean`](../SharpTopologicalOverlap/Comparison/Realization.lean)
identifies TauCeti's weak realization with this coordinate realization by the
actual barycentric coordinates.

The remaining identification passes through the CW structure on the weak
realization. In
[`Cellular.lean`](../SharpTopologicalOverlap/Comparison/Cellular.lean), the
affine characteristic simplex of a face defines a class in the relative
homology of its skeleton modulo the preceding skeleton. Its connecting
morphism is represented by the sum of its affine facets. Consequently
`skeletalAffineClass_differential` identifies its cellular differential with
the simplicial boundary. This argument includes degree zero, whose outgoing
differential is zero.

[`CellularNaturality.lean`](../SharpTopologicalOverlap/Comparison/CellularNaturality.lean)
proves that these relative classes commute with the maps induced by strictly
increasing simplicial vertex maps. This permits reduction of an arbitrary
face to the unique top face of the full simplex on `Fin (k + 1)`.

[`CellularBasis.lean`](../SharpTopologicalOverlap/Comparison/CellularBasis.lean)
then identifies the affine relative class with the existing cellular basis
element. The proof is by induction on the degree. In degree zero, the
singular augmentation sends the point class to one, so the class is nonzero.
For the standard simplex in the next degree, the differential of its affine
class is the sum of distinct facet basis elements, already identified by the
induction hypothesis. This sum is nonzero, so the original class is nonzero.
The top cellular group of that standard simplex has one basis element. Over
`ZMod 2`, its only nonzero coefficient is one. Naturality transfers the result
to every face. The precise endpoints are `affineClassCoordinates_eq_single`
and `skeletalAffineClass_apply_eq_basis`.

[`Canonical.lean`](../SharpTopologicalOverlap/Comparison/Canonical.lean)
uses this generator identification to compare maps on cycles, rather than
selecting an unrelated isomorphism between homology groups. Its key equality
`homologyMap_affineWholePair_eq` states that the homology map of the actual
affine map, with target the whole CW pair modulo its empty base, is the
composite of

1. the map induced by the inverse of
   `TauCeti.cellularChainComplexRealizationIso K Coeff`; and
2. `TauCeti.cellularSingularHomologyIso` for the CW realization.

The first library isomorphism identifies cellular chains with ordered
simplicial chains; the second identifies cellular homology with singular
homology relative to the CW base. Their defining sources are respectively
`TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/OrderedChainComplex.lean`
and `TauCeti/AlgebraicTopology/Cellular/Comparison.lean` in the pinned dependency.
The proof uses the latter source's
`homologyπ_comp_cellularSingularHomologyIso_hom` to identify the map on cycle
classes. Removing the empty CW base and transporting through the coordinate
homeomorphism are isomorphisms. They give
`isIso_homologyMap_affineChainComplexMapIn` for the stated affine map.

## Ambient precomplexes and the induction

TauCeti's `AbstractSimplicialComplex V` contains every singleton of its vertex
type. An ambient carrier `L` in Lemma 2.4 need not contain every singleton of
the original `V`. Simply adding missing vertices would change the carrier.

[`Precomplex.lean`](../SharpTopologicalOverlap/Comparison/Precomplex.lean)
instead uses the vertex subtype `ActualVertex L = {v // {v} ∈ L}` and constructs
`actualComplex L` with exactly the faces of `L`, reindexed onto that subtype.
`actualChainEquiv` identifies its chains with the ambient simplicial chains
carried by `L`, and `actualRealizationHomeomorph` identifies its coordinate
realization with `realizedComplex L`. The singular inclusion is injective,
commutes with boundary, and lifts every singular chain carried by the latter
space. Crucially, `actualAffineChainMap_natural` proves compatibility with the
same affine generator map used above.

[`HomologyElements.lean`](../SharpTopologicalOverlap/Comparison/HomologyElements.lean)
extracts two element statements from injectivity and surjectivity of an
induced homology map: a source cycle whose image bounds already bounds, and
every target cycle is homologous to the image of a source cycle. It proves
these first for short complexes of modules and then for chain complexes in
every natural degree.
[`Provider.lean`](../SharpTopologicalOverlap/Comparison/Provider.lean) applies
them through the reindexing and inclusion maps. Its `canonical_injectivity`
and `canonical_surjectivity` retain the specified ambient carrier in both the
simplicial and singular fillings. They supply the unconditional object
`canonicalHomologyComparison`.

[`DegreeZero.lean`](../SharpTopologicalOverlap/Comparison/DegreeZero.lean)
starts the supported construction by selecting a vertex in the support of
each probability vector, selecting `x` at the uniform vector. The affine edge
from the vector to that vertex defines `QZero`. The selected vertex and the
edge lie in every closed face containing the original vector.

For a singular simplex `s`, `simplexCarrier s` is the precomplex of nonempty
subsets of supports of points in its image. It carries `s`, is contained in
every precomplex carrying `s`, and contains the carriers of all facets of
`s`. These facts retain all requested carriers simultaneously in
[`Induction.lean`](../SharpTopologicalOverlap/Comparison/Induction.lean).

Suppose the maps have been constructed through degree `k`, and let `s` have
degree `k + 1`. The old homotopy identity shows that
`ιρ(∂s) = ∂(s + Q(∂s))` inside `|simplexCarrier s|`. The canonical injectivity
statement produces a simplicial chain `t` in this carrier with
`∂t = ρ(∂s)`. The chain `s + Q(∂s) + ιt` is a singular cycle there. Canonical
surjectivity supplies a simplicial cycle `b` and a singular chain `q` in the
same carrier whose boundary is this cycle plus `ιb`. Defining `ρ(s) = t + b`
and `Q(s) = q` proves the next chain-map and homotopy identities. Linear
extension completes the degree step. The implementation maintains the
homotopy on cycles as its induction invariant and proves the full successor
identity in `boundary_nextQ`.

[`Supported.lean`](../SharpTopologicalOverlap/Comparison/Supported.lean)
instantiates this construction with the proved canonical provider. No
comparison hypothesis remains in `supportedComparison`.

## Boundary cases and verification

An empty precomplex has an empty actual vertex subtype and an empty
realization. The canonical comparison and the reindexing construction do not
require that subtype to be nonempty. A precomplex with some omitted vertices
is therefore handled without enlarging it. Only the final normalized
construction assumes a nonempty ambient vertex type, as required by its
chosen vertex `x` and uniform point.

Degree zero is ordinary, unaugmented homology throughout. The concrete
cycle-to-filling lemmas use the actual zero outgoing differential at degree
zero; the supported induction starts with the point/edge construction above.
No reduced-homology or positive-degree assumption is used to cover that case.

All comparison source modules were checked with `lake env lean` during
implementation. The completed module targets were also built successfully,
including

```text
lake build SharpTopologicalOverlap.Comparison.Canonical
lake build SharpTopologicalOverlap.Comparison.Provider
lake build SharpTopologicalOverlap.Comparison.Supported
```

The final target includes the eleven modules under `Comparison/` and the
ambient `Comparison.lean`. Separate axiom checks were run for the affine
generator identification, the equality with the cellular comparison, the
canonical homology-isomorphism instance, and the final unconditional
`supportedComparison` and `boundary_supportedQ_succ`. Each reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

A source scan of the comparison block found no `sorry`, `admit`, or project
axiom declarations. Temporary files used to print the axiom dependencies
were removed after checking.
