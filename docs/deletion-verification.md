# Block D verification

The checked implementation in `SharpTopologicalOverlap/Deletion.lean`
proves Lemma 6.1 (`lem:covers`) of the reference manuscript.

* A maximum matching is chosen once for each positive-dimensional target
  cell. Its union hits every supported source face. Taking unions over
  target subfaces makes the exceptional sets monotone.
* `exceptionalSet_card_le` combines the intersection matching bound with
  the exact binomial count of target subfaces to give the existing
  natural-number constant `deletionBound d`.
* `remainingVertices_nonempty` uses precisely `deletionBound d < n`.
* `cochain_eq_zero_on_remaining` and
  `vertex_cochain_eq_on_remaining` give vanishing and agreement. The latter
  assumes `0 < d`, supplied by the finite theorem's `2 ≤ d`.
* `remainingFamily_hasCocycleParity` concerns the full simplex on the
  actual subtype of remaining vertices. `remainingFamily_image` identifies
  it exactly with `restrictedFamily`, defined by filtering upward support.

The primary agent inspected the matching choice, cover argument, cardinality
estimate, edge identity, subtype restriction and family-image identity.
Both `lake env lean SharpTopologicalOverlap/Deletion.lean` and
`lake build SharpTopologicalOverlap.Deletion` passed. After adding its root
import, `lake build` passed (8985 jobs).

The transitive axiom audit of `exceptionalSet_card_le`,
`remainingVertices_nonempty`, `cochain_eq_zero_on_remaining`,
`vertex_cochain_eq_on_remaining`, `remainingFamily_hasCocycleParity`, and
`remainingFamily_image` found only `propext`, `Classical.choice`, and
`Quot.sound`. No placeholder or project axiom supplies a proof.

Theorem 1.2 still requires the comparison, spectral, barrier, sublevel,
weight-space, and descending branches. This block does not assume their
conclusions.
