# Formalization status

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Vertex deletion bound $C_d$ (`eq:C`) | [`SharpTopologicalOverlap.deletionBound`](SharpTopologicalOverlap/Basic.lean) | Defined |
| Size implication $d+1\le C_d$ for $d\ge2$ | `add_one_le_deletionBound`, `add_one_lt_of_deletionBound_lt` in [`Basic.lean`](SharpTopologicalOverlap/Basic.lean) | Proved |
| Probability simplex and finite/Euclidean coordinates (§2.1) | `Simplex`, `coordinateHomeomorph`, `euclideanCoordinates` in [`Simplex.lean`](SharpTopologicalOverlap/Simplex.lean) | Implemented; coordinate bounds, sum, continuity, vertex and uniform support proved |
| Closed/open faces and realization (§2.1) | `closedFace`, `openFace`, `realizedComplex`, `closedFace_inter`, `realizedComplex_eq_iUnion_closedFace`, `isCompact_realizedComplex` | Proved; empty faces, singleton open faces, and disjoint open faces included |
| Realized source skeleton $X_{n,d}$ | `Skeleton`, `skeletonRealizationHomeomorph`, `image_faceInclusion_skeletonRealizationHomeomorph` in [`Skeleton.lean`](SharpTopologicalOverlap/Skeleton.lean) | Proved; preserves coordinates and each closed face; skeleton and its closed faces are compact |
| Overlap definition and elementary bounds (Introduction) | `facesAt`, `overlap`, `overlap_attained`, `overlap_le_choose`, `card_le_overlap_of_common_point` in [`Overlap.lean`](SharpTopologicalOverlap/Overlap.lean) | Defined and proved; counts source faces, including coincident images |
| Indexed-face counting for constant maps and absent faces | `overlap_const`, `overlap_eq_zero_of_card_lt` in [`Overlap/Constant.lean`](SharpTopologicalOverlap/Overlap/Constant.lean) | Proved, including empty vertex types and degrees above the available dimension |
| Simplicial chains, evaluation and coboundary (§2.2) | `Simplicial.Chain`, `Simplicial.Cochain`, `evaluation_coboundary`, `coboundary_coboundary` in [`Simplicial.lean`](SharpTopologicalOverlap/Simplicial.lean) | Defined and proved over `ZMod 2`; imported boundary, signless formula, actual unaugmented degree-zero differential and constant-one cocycle included |
| Cochain supports and uniform cocycles (§2.2) | `supportFamily`, `cochainOfFamily`, `isCocycle_full_iff_parity` in namespace `Simplicial` | Proved; inverse conversions and parity on every one-size-larger vertex set |
| Simplicial carriers and inclusion/restriction | `CarriedBy`, `carriedBy_boundary`, `evaluation_eq_zero_of_carriedBy`, `boundary_includeChain`, `coboundary_restrict` in namespace `Simplicial` | Proved; includes injective chain inclusions and restriction/evaluation compatibility |
| Ambient vertex-omitting subcomplexes | `SubcomplexChain`, `restrictToSubcomplex`, `evaluation_restrictToSubcomplex`, `subcomplexBoundary_squared` in [`Simplicial/Subcomplex.lean`](SharpTopologicalOverlap/Simplicial/Subcomplex.lean) | Defined and proved using carried ambient submodules; does not require adding missing vertices |
| Morse band vanishing used in Lemma 5.5 (`lem:band`) | `TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex` | Imported and [checked over $\mathbb F_2$](docs/dependency-assessment.md#build-and-verification). The simplex application is open. |
| Theorem 1.2 (`thm:finite`) | — | Open |
| Theorem 1.1 (`thm:main`) | — | Open |

The foundation work follows [the implementation plan](docs/foundation-plan.md).
The [detailed blueprint](docs/blueprint.md) specifies the subsequent modules,
intermediate statements, dependency order, and completion checks for Theorem 1.2.
Only Theorems 1.1 and 1.2 must retain their exact manuscript statements;
intermediate statements may be replaced by simpler formalization routes.

The foundation's module checks and full project build pass. A transitive axiom
audit of 38 major endpoints found only `propext`, `Classical.choice`, and
`Quot.sound`, with no placeholders or project axioms. The intended Theorem 1.2
proposition type-checks on `Skeleton (Fin n) d` with target
`EuclideanSpace ℝ (Fin d)`; this is a statement check, not a proof of the theorem.
The source closed-face identification is proved; Appendix A's later geometric
construction remains open. See [verification details](docs/foundation-verification.md).
