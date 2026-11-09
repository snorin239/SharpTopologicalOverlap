# Remaining blocks toward Theorem 1.2

Work resumed on 9 November 2026 from the checked completion of block G
(`09e3cbd`). The reference manuscript is unchanged. Each completed flowchart
block will be checked, audited, documented, and committed separately.

## Initial parallel work

* **H, singular chains (primary agent):** concrete singular support and its
  carrier/lifting API, followed by relative-cycle fillings and a
  support-controlled prism. Direct prerequisites: the existing simplex API
  and TauCeti's singular module chains, relative chains, and homotopies.
* **P, polynomials (polynomial agent):** finite-sum weight polynomials,
  smoothness and derivatives, positivity/counting bounds, restriction,
  and the independence complex. Direct prerequisites: simplex and finite
  family APIs. This supplies the spectral and weight-space branches.
* **D, deletion (deletion agent):** compatible maximal support matchings,
  cardinality bound, vanishing on complements, agreement of vertex
  cochains and restricted cocycles. Direct prerequisites: block G and
  the existing simplicial algebra.
* **C, comparison (comparison agent):** inspect the canonical comparison
  theorem in the pinned library, implement the affine chain map and its
  carrier compatibility, then its homology isomorphism and the supported
  inverse. Its singular carrier prerequisites are coordinated with H.

Each agent owns its named module and subtree. The primary agent owns root
imports, integration, documentation, validation, and commits. Agents do not
commit or edit each other's files. Dependencies and remaining gaps are
reported explicitly; a conditional interface is never counted as the final
theorem.

## Subsequent dependencies

Block H is implemented: support equivalence, compact chain images,
injective inclusion, actual relative fillings in all nonnegative degrees,
carrier-controlled prism, deformation-retract fillings and nested-pair
composition. The modules are `Singular.lean`, `Singular/Relative.lean`,
`Singular/Prism.lean`, and `Singular/Deformation.lean`.

Before starting block F, its algebraic work is divided as follows. The
primary agent first implements the finite target incidence transpose and
its square-zero and evaluation identities in `Descending/Incidence.lean`.
This uses only the checked target simplicial boundary/coboundary API and
finite face types. It will then support the descending induction on source
degree and the evaluation contradiction. The comparison agent remains
responsible for C's supported inverse; the spectral agents remain occupied
with the count/signature and covariance branches. F's input data will be
explicit, and F is conditional until all geometric and analytic providers
are constructed in the final assembly.

Block D is implemented in `Deletion.lean`: all five parts of Lemma 6.1,
including the actual remaining-vertex subtype and the exact family-image
identity, are checked. The independent review checked the global matching
choices, cardinality estimate, edge argument, and reindexing.

The next spectral work starts with a separate finite real-sum lemma
(`Spectral/Counting.lean`): a lower bound on each eigenvalue and their fixed
negative sum imply the required count, with the equality case proved
explicitly. This depends only on finite sums and real arithmetic. Its
library spectral/signature adapter will be inspected alongside that proof;
it does not yet claim the matrix or cocycle rigidity theorem.

Block P is implemented and independently inspected in `Polynomial.lean`.
Its first and second derivatives are identified with Frechet derivatives;
all counting, positivity, zero-set and restriction endpoints are checked.
The polynomial agent now owns `Spectral/Normalization.lean` and
`Spectral/Covariance.lean`: constant partials at a critical point, the
normalized Hessian eigenvector, and the finite covariance sum of squares.
These use P directly. The counting agent owns only `Spectral/Counting.lean`
and its real symmetric-operator adapter. The cocycle equality case and
final index/signature integration remain explicit subsequent tasks.

The spectral implementation now includes the projected-matrix signature
adapter and its exact equality spectrum, as well as the covariance-kernel
argument and the cocycle exchange/coloring theorem. The polynomial agent
owns the remaining part-mass calculation and spectral assembly.

The next independent work on block B starts with
`Barrier/Coordinates.lean` and `Barrier/MorseAdapter.lean`, owned by the
counting/index agent after its audit. Dependencies are the checked zero-sum
space and tangent Hessian interfaces, finite Euclidean coordinates, and
the inspected TauCeti manifold Morse definitions. The initial objectives
are the affine open-simplex chart, its boundaryless manifold instances,
and exact critical-point/Hessian/index transport. Generic Morse tilts,
barrier properness and persistence remain subsequent analytic obligations.

After P, implement spectral rigidity (including equality), then the
logarithmic barrier and index persistence. H and the barrier supply sublevel
relative vanishing. D, P, and sublevel vanishing supply the nested weight
spaces. C, H, G, and the weight spaces supply the descending contradiction
and the exact finite overlap theorem. Before starting each later block,
record its concrete dependencies and assign nonoverlapping implementation
and verification tasks.

## Completion checks

Before implementing block W, the primary agent will define all carriers in
the fixed ambient simplex: `B` by the polynomial inequality and `J` by
remaining-vertex support and the restricted-family zero condition.
Direct prerequisites are D, P, and H; the relative-filling provider will
remain explicitly conditional on the sublevel theorem until V is proved.
First prove polynomial restriction, nested inclusions and the uniform
point estimate. Then implement and check the exceptional-mass deletion
homotopy, followed by transport of actual finite-subtype sublevel fillers.
The comparison agent continues C, while the other agents continue B and
spectral equality, so no module ownership overlaps.

The abstract block F construction is now implemented in
`Descending/Incidence.lean`, `Descending/Algebra.lean`, and
`Descending/Fillings.lean`. Its endpoint is
`Descending.FillingInputs.false`; all comparison, nested-carrier, filling,
and annihilation providers are explicit inputs. Constructing those inputs
is still required before the unconditional Theorem 1.2 can be asserted.

Check each new module with `lake env lean`, expose it from
`SharpTopologicalOverlap.lean`, run `lake build`, and inspect endpoint axioms.
Update `FORMALIZATION.md` with actual declarations and proof status. Only
checked results free of placeholders and project axioms count as complete.
