# Foundation verification — 9 November 2026

The top blueprint block is implemented in `Simplex`, `Skeleton`, `Overlap`,
`Overlap.Constant`, `Simplicial`, and `Simplicial.Subcomplex`, with the numerical
size lemma in `Basic`. All are exposed through `SharpTopologicalOverlap.lean`.

## Verification

- Each implemented module was checked with `lake env lean` and built.
- `lake build` passed for the integrated project.
- A transitive `#print axioms` audit of 38 major endpoints found only `propext`,
  `Classical.choice`, and `Quot.sound`. No `sorryAx` or project axioms occur in
  these endpoint dependencies. A project source scan also found no `sorry`,
  `admit`, or axiom declarations.
- Independent source reviews checked the geometric and algebraic interfaces.
- Lean probes checked empty and singleton vertex types, open zero-faces, the
  unaugmented degree-zero differential, absence of cells above the available
  dimension, the constant-one cochain and its evaluation, and the unordered
  cocycle/parity correspondence.
- Constant-map overlap was proved equal to the full binomial face count. Thus
  distinct source faces still count separately when all their images coincide.
- The numerical probe gives `deletionBound 2 = 13`.

The temporary probes are retained under `.lake/`: `SimplexAudit.lean`,
`AlgebraAudit.lean`, `FoundationTargetProbe.lean`, and `FoundationAxiomAudit.lean`.
The module proofs themselves are the durable verification artifacts.

## Target statement check

The following proposition type-checks using the actual constructed domain:

```lean
∀ (d n : ℕ), 2 ≤ d → deletionBound d < n →
  ∀ (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))),
    (((n : ℝ) - (deletionBound d : ℝ)) / ((d : ℝ) + 1)) ^ (d + 1) ≤
      (overlap f : ℝ)
```

It is not asserted as a proved theorem. The weights-preserving skeleton
homeomorphism carries every native closed face to the closed face used by this
overlap definition. Compatibility with Appendix A's future construction will be
checked when that construction exists.

## Representation choices

The chain/cochain algebra is independent of project geometry and reuses
TauCeti's ordered chains. For a vertex-omitting ambient precomplex, chains are
the carried submodule of ambient chains and cochains are functions on its
ambient cells. Intrinsic reindexing needed by the later comparison theorem is
not part of this foundation block.

## Repeating checks on this Windows installation

The installed Elan `lake` shim stalled before Lean started during this task.
Invoking the pinned toolchain's Lake executable directly worked:

```powershell
& 'C:/Users/snori/.elan/toolchains/leanprover--lean4---v4.36.0-rc2/bin/lake.exe' build
& 'C:/Users/snori/.elan/toolchains/leanprover--lean4---v4.36.0-rc2/bin/lake.exe' env lean .lake/FoundationTargetProbe.lean
& 'C:/Users/snori/.elan/toolchains/leanprover--lean4---v4.36.0-rc2/bin/lake.exe' env lean .lake/FoundationAxiomAudit.lean
```
