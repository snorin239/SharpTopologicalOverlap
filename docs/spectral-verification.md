# Spectral block verification

`Spectral.spectral_index_rigidity` proves Lemma 4.1 with the complete
equality case. `Spectral.faceCritical_index_ge` proves Corollary 4.2 on the
actual tangent space of the support, using the Frechet Hessian from block P.

The implementation follows these checked dependencies:

1. Criticality on the zero-sum space gives equal partial derivatives and
   the stationary Euler identities. Square-root coordinates identify the
   tangent form with the normalized Hessian on the root-orthogonal space.
2. A finite weighted sum of centered outer products is positive semidefinite
   and equals the covariance formula in the manuscript. The projected full
   Hessian kills the radial root vector, has the required negative trace,
   and has the global quadratic lower bound.
3. The finite eigenvalue counting lemma includes its exact equality case.
   The library's symmetric-operator eigenvalue/signature and trace results,
   with explicit linear restriction/pullback proofs, give the actual
   tangent negative index.
4. Equality makes the negative projection symmetric and idempotent. Its
   row labels have the required norms and pair-Hessian identity. The
   covariance kernel gives zero label sum on every edge, and positive pair
   terms give injectivity of labels within edges.
5. Cocycle parity proves the unique label representatives, exchange rule,
   and exact transversal characterization. The resulting surjective
   coloring is a genuine partition. An exact transversal-choice bijection
   factors the polynomial; stationary first moments give equal class
   masses and the exact threshold value.
6. Zero extension and a linear equivalence transport the restricted family,
   criticality, Frechet Hessian and negative index to the active support.

The primary agent inspected the original spectral proof, the projected
matrix strategy, index restriction argument, equality construction,
transversal factorization and stationary mass calculation. The spectral
module build passed (7352 jobs). Component axiom audits reported only
`propext`, `Classical.choice`, and `Quot.sound`.

The root `lake build` also passed (9687 jobs). Direct audits of both final
endpoints found only `propext`, `Classical.choice`, and `Quot.sound`.

This block supplies the index input for barrier persistence; it does not
assert Morse genericity, properness, relative sublevel vanishing, or the
finite overlap theorem.
