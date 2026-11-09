# Foundation block implementation plan

This task implements the top block of blueprint §2: simplex, faces, chains,
and cochains. The final theorem statements and reference manuscript are preserved.

## Parallel ownership

| Workstream | Owner | Files | Acceptance criterion |
| --- | --- | --- | --- |
| Simplex geometry | Subagent 1 | `SharpTopologicalOverlap/Simplex.lean` | Coordinates, vertex and uniform points, support, closed/open faces, realization membership, continuity and compactness |
| Finite algebra | Subagent 2 | `SharpTopologicalOverlap/Simplicial.lean` and its submodules | Ordered chains over `ZMod 2`, evaluation and coboundary identities, support families, parity, restrictions and carrier annihilation |
| Skeleton and overlap | Subagent 3 | `SharpTopologicalOverlap/Skeleton.lean`, `SharpTopologicalOverlap/Overlap.lean` | Realization identification, closed-face compatibility, attained overlap, binomial and common-point bounds |
| Integration and verification | Primary agent | `Basic.lean`, root imports, status and documentation | Numerical size lemma, target-statement probe, full build and placeholder/axiom audit |

The primary agent reviews shared interfaces and reassigns completed workstreams
to independent checks or remaining concrete lemmas. Each agent checks its modules
before handoff; integration checks use the final dependency graph.

## Checks

1. Use the actual probability-simplex and ordered-chain representations on the pins.
2. Include empty vertex types, dimension zero, singleton open faces, and degrees
   above the number of vertices in the API's edge cases.
3. Count source faces even if their images coincide.
4. Check the intended Theorem 1.2 proposition on the constructed domain without
   declaring an unproved theorem.
5. Run module checks and `lake build`; check completed declarations for placeholders
   and project axioms, and update `FORMALIZATION.md` with precise achieved scope.

## Outcome

All four workstreams are implemented. The geometry/overlap branch was split into
`Simplex`, `Skeleton`, `Overlap`, and `Overlap.Constant`. The finite algebra is
geometry-independent; `Simplicial.Subcomplex` supplies the ambient interface for
vertex-omitting subcomplexes. Completed agents were reassigned to independent
source, edge-case, statement, documentation, and transitive-axiom checks.

See [the verification record](foundation-verification.md) and
[the formalization mapping](../FORMALIZATION.md). Theorems 1.1 and 1.2 and the
subsequent proof branches remain open.
