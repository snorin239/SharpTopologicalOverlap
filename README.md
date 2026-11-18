# Sharp topological overlap in Lean

This repository contains a Lean 4 formalization, for dimensions $d\ge1$, of
Theorem 1.1 and a strengthening of Theorem 1.2 of Sergey Norin’s
[*Sharp topological overlap in every dimension*](paper/main.pdf) (current draft).

The [9 November 2026 draft](paper/sharp_topological_overlap.pdf) and its
[LaTeX source](paper/sharp_topological_overlap.tex) are the reference for the
formalization. The development also proves convergence of both normalized
finite minimum sequences.

## The statements formalized

Let $X_{n,d}$ be the $d$-dimensional skeleton of the simplex on $n$ vertices.
For a continuous map $f:|X_{n,d}|\to\mathbb R^d$, its overlap is

$$
\mathrm{ov}(f)=\max_{y\in\mathbb R^d}
\#\{\sigma\subseteq[n]:|\sigma|=d+1,\ y\in f(|\sigma|)\}.
$$

Faces are closed, and distinct source faces are counted separately even when
their images coincide. In Lean the source is `Skeleton (Fin n) d`, the target
is `EuclideanSpace ℝ (Fin d)`, and `overlap f` is a natural number.
The declarations below are in the namespace `SharpTopologicalOverlap`.

### Theorem 1.1

The topological overlap constant is the liminf, as $n\to\infty$, of the least
overlap among all continuous maps, divided by $\binom n{d+1}$. The affine
constant is defined independently by minimizing over vertex placements and
their affine interpolations. For every $d\ge1$,

$$
c_d^{\mathrm{top}}=c_d^{\mathrm{aff}}=\frac{(d+1)!}{(d+1)^{d+1}}.
$$

```lean
theorem sharp_overlap_constants {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = affineOverlapConstant d ∧
      affineOverlapConstant d =
        ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1)
```

The individual statements and full sequence limits are in
[`Asymptotic.lean`](SharpTopologicalOverlap/Asymptotic.lean).
The common constant is $1/2$ in dimension one, $2/9$ in dimension two, and
$3/32$ in dimension three.

### Theorem 1.2

Put

$$
C_d=\sum_{p=1}^{d}\binom{d+1}{p+1}(d+1-p)
\left\lfloor\frac dp\right\rfloor.
$$

For $d\ge1$ and $n>C_d$, every continuous map satisfies

$$
\mathrm{ov}(f)\ge\left(\frac{n-C_d}{d+1}\right)^{d+1}.
$$

The current paper writes $N_d$ for $C_d$ and indexes the simplex by its
dimension $m$, so $n=m+1$ in the Lean statement. Restricting a full-simplex
map to the skeleton preserves overlap. The Lean theorem therefore gives a
lower bound greater by $N_d\binom{m}{d}$ than the one stated in the current
paper. The [formalization map](FORMALIZATION.md#relation-to-the-full-simplex)
explains the passage to full-simplex maps for both theorems.
The Lean statement is in [`Finite.lean`](SharpTopologicalOverlap/Finite.lean).

```lean
theorem finite_overlap_bound {n d : ℕ} (hd : 0 < d)
    (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤
      (overlap f : ℝ)
```

`deletionBound` uses natural-number division for the floor. The subtraction
in the lower bound takes place in the reals. In dimension one, the deletion bound is $C_1=1$,
so the finite bound is $\mathrm{ov}(f)\ge ((n-1)/2)^2$ for $n>1$.

## Structure of the proof

1. Simplicial and singular chain foundations relate the concrete probability
   simplex to geometric realizations, relative homology and supported fillings.
2. Subdivision and general-position constructions produce the intersection
   cochains of Lemma 3.1 from an arbitrary continuous map.
3. The spectral estimate for uniform cocycles, followed by a logarithmic
   barrier and Morse theory, proves the relative sublevel vanishing theorem.
4. Compatible vertex deletion and nested weight spaces allow a descending
   filling argument. Evaluation against the intersection cochains proves
   the finite bound of Theorem 1.2.
5. A formalized Bukh–Matoušek–Nivasch configuration supplies the matching
   affine upper bound. Binomial normalization and the squeeze theorem prove
   both limits and Theorem 1.1.

The [paper-to-Lean map](FORMALIZATION.md) identifies the main declarations
and explains changes to intermediate proof interfaces. The
[blueprint](docs/blueprint.md) describes the modeling choices and module
dependencies. Some intermediate results are adapted to simplify their
Lean proofs.

## Building

The project pins Lean to `v4.36.0-rc2`, Mathlib to revision `1b1ccf4b088b`,
and TauCeti to revision `1e668f5e55bc`. Full revisions are recorded in
[`lake-manifest.json`](lake-manifest.json).

With Git and [Elan](https://github.com/leanprover/elan) installed, run from
the repository root:

```sh
export LAKE_CONFIG="$PWD/lake-cache.toml"
lake exe cache get
lake cache get --package=TauCeti --service=tauceti-public --repo=TauCetiProject/TauCeti --mappings-only
lake build
```

In PowerShell, replace the first line with
`$env:LAKE_CONFIG = (Resolve-Path lake-cache.toml).Path`.
The [cache configuration](lake-cache.toml) selects TauCeti's public cache.
For subsequent builds, run `lake build`. Import the full library with
`import SharpTopologicalOverlap`.

## Verification

A local Windows run of `lake --wfail build` succeeded on November 18, 2026,
at commit `bb8c37d` (9,831 Lake jobs). The project Lean source contains no
`sorry`, `admit`, or placeholder axioms. The transitive axiom audits of
Theorems 1.1, 1.2 and the geometric upper-bound construction report only
`propext`, `Classical.choice`, and `Quot.sound`.

After building, reproduce the statement checks and axiom audits with:

```sh
lake env lean -DwarningAsError=true verification/Theorem11.lean
lake env lean -DwarningAsError=true verification/Theorem12.lean
lake env lean -DwarningAsError=true verification/Theorem71.lean
```

These files import only the public project root. They check the expanded
statements, both overlap constants in dimension one, the two-vertex finite
bound, and the axioms used by the main proof dependencies.

## Acknowledgements

OpenAI Codex (GPT-6.1 Sol) prepared the Lean formalization. The paper
describes GPT-6 Astra’s role in developing the mathematical proof.

The development uses [Mathlib](https://github.com/leanprover-community/mathlib4)
and [TauCeti](https://github.com/TauCetiProject/TauCeti), which supplies
simplicial and singular chain complexes and Morse theory. The formalization
proves the intersection-cochain construction following Dotterrer, Kaufman,
and Wagner and the affine upper-bound construction of Bukh, Matoušek, and
Nivasch.

## License

Copyright 2026 Sergey Norin, except for third-party material attributed to
its respective copyright holders.

The Lean code, build files, and repository documentation are distributed
under the [Apache License 2.0](LICENSE). The manuscript PDFs and LaTeX source
in `paper/` are distributed under
[Creative Commons Attribution 4.0 International (CC BY 4.0)](paper/LICENSE).
