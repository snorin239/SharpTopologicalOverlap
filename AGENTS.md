# Repository instructions

## Objective

Formalize Theorem 1.2 and then Theorem 1.1 of
`paper/sharp_topological_overlap.pdf` in Lean 4 with Mathlib. Use the paper
and its accompanying TeX source for mathematical intent and numbering.

## Working on Lean

- Read the relevant paper passage and `docs/blueprint.md` before choosing
  definitions. Search the pinned Mathlib for reusable declarations.
- Import new project modules through `SharpTopologicalOverlap.lean`. Check a
  module with `lake env lean <file>` and run `lake build` from the root.
- Keep the paper-to-Lean mapping in `FORMALIZATION.md` current. A result
  counts as proved when its dependencies are checked and free of placeholders
  such as `sorry`, `admit`, or project axioms standing in for proofs.
- Preserve the reference manuscript unless the user asks to edit it.

## Project-wide formalization choices

- Theorems 1.1 and 1.2 must be proved as stated. Intermediate results may
  be reformulated or replaced when a different route simplifies formalization.
- Reuse exact library results when available. When only similar results exist,
  inspect and adapt their implementations rather than rebuilding everything
  from scratch.

## Mathematical skill routing

- When asked to prove or disprove a nontrivial mathematical statement,
  invoke `$mathematical-research`.
- When asked to prepare a mathematical manuscript, proof document,
  LaTeX source, or PDF, invoke `$mathematical-writeups`.
- When asked to proofread a mathematical paper, proof, or manuscript,
  invoke `$mathematical-proofreading` and announce its use.
- Subagent provisions inside these skills apply only when the user
  explicitly requests multiagent work.
