# Sharp topological overlap in Lean

This project formalizes *Sharp topological overlap in every dimension* in Lean 4
with Mathlib and TauCeti. The targets, in order, are Theorem 1.2 (the finite overlap bound)
and Theorem 1.1 (the sharp asymptotic constant). The reference is the
[9 November 2026 manuscript](paper/sharp_topological_overlap.pdf).

## Build

The project uses Lean `v4.36.0-rc2`, TauCeti `1e668f5e55bc`, and its matching
mathlib revision `1b1ccf4b088b`. The [Lake manifest](lake-manifest.json) locks
the full revisions.

With Git and Elan installed, run the following from the repository root.
The first line selects the [public TauCeti cache](lake-cache.toml) for this
shell. In PowerShell, use
`$env:LAKE_CONFIG = (Resolve-Path lake-cache.toml).Path` for that line.

```sh
export LAKE_CONFIG="$PWD/lake-cache.toml"
lake exe cache get
lake cache get --package=TauCeti --service=tauceti-public --repo=TauCetiProject/TauCeti --mappings-only
lake build
```

For subsequent builds, run `lake build`. To use the library in a Lean file,
write `import SharpTopologicalOverlap`.

## Working on the formalization

Theorem 1.2 is proved as `SharpTopologicalOverlap.finite_overlap_bound`,
with no placeholders or project proof axioms. Its transitive axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.
Theorem 1.1 is proved and strengthened to include the affine constant:
`SharpTopologicalOverlap.sharp_overlap_constants` states
`c_top = c_aff = (d+1)!/(d+1)^(d+1)` for every `d ≥ 2`.
Both normalized finite minimum sequences also converge to this value.

The [formalization status](FORMALIZATION.md) lists the checked declarations.
The [blueprint](docs/blueprint.md) gives the proof-block flowchart and dependencies;
the verification records for [Theorem 1.2](docs/finite-verification.md) and
[Theorem 1.1](docs/theorem11-verification.md) record the final checks.
Run `lake env lean verification/Theorem12.lean` and
`lake env lean verification/Theorem11.lean` to reproduce the statement
and axiom audits after building the project.
The [LaTeX source](paper/sharp_topological_overlap.tex)
provides stable labels for those results.
