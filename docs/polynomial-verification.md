# Block P verification

`SharpTopologicalOverlap/Polynomial.lean` implements the weight polynomials
of §2.4 and the polynomial identities used in §4. The degree parameter is
the number of vertices per edge, so it is `d+1` for the main theorem.
Arbitrary families are filtered by cardinality exactly as in the paper.

The module proves smoothness, actual Frechet first and second derivative
formulas, the symmetric zero-diagonal Hessian, Euler identities, homogeneity,
nonnegativity, monotonicity, the uniform value, and restriction to active
coordinates. The sharp bound by the power of the total mass is proved by
induction through link families; it gives both the simplex bound by one
and the coordinate derivative bound. The polynomial zero set equals the
realization of the explicitly defined independence precomplex.

The primary agent inspected the recursive counting proof, derivative and
Hessian identification, independence zero criterion, and active-coordinate
restriction. `lake env lean SharpTopologicalOverlap/Polynomial.lean` and
`lake build SharpTopologicalOverlap.Polynomial` passed. The endpoint audit
of `le_sum_pow`, `simplex_le_one`, `simplex_partial_le`,
`hessian_eq_fderiv_fderiv`, `hessian_restrict_eq`, and
`realized_independenceComplex` found only `propext`, `Classical.choice`, and
`Quot.sound`.

This block does not assume or prove spectral rigidity. The matrix,
covariance, negative-index and cocycle equality arguments remain separate
proof obligations.
