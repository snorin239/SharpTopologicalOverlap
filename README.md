# Sharp topological overlap in Lean

This project formalizes *Sharp topological overlap in every dimension* in Lean 4
with Mathlib. The targets, in order, are Theorem 1.2 (the finite overlap bound)
and Theorem 1.1 (the sharp asymptotic constant). The reference is the
[9 November 2026 manuscript](paper/sharp_topological_overlap.pdf).

## Build

With Git and Elan installed, run these commands from the repository root on a
fresh checkout. Lean and Mathlib are pinned to `v4.32.1`.

```sh
lake exe cache get
lake build
```

For subsequent builds, run `lake build`. To use the library in a Lean file,
write `import SharpTopologicalOverlap`.

## Working on the formalization

The [formalization status](FORMALIZATION.md) lists the checked declarations.
The [blueprint](docs/blueprint.md) gives the target statements and maps their
proofs to sections of the paper. The [LaTeX source](paper/sharp_topological_overlap.tex)
provides stable labels for those results.
