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

The [formalization status](FORMALIZATION.md) lists the checked declarations.
The [blueprint](docs/blueprint.md) details the remaining formalization of
Theorem 1.2, with proposed modules, proof dependencies, and completion checks.
The [LaTeX source](paper/sharp_topological_overlap.tex)
provides stable labels for those results.
