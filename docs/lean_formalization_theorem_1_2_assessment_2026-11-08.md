# Lean formalization assessment for Theorem 1.2

Assessment date: 8 November 2026.

Source manuscript: `C:\Users\snori\Documents\Projects\High Dimensional Brambles\research_20261108_general\sharp_topological_overlap.pdf`

**For Theorem 1.2, substantial background can be imported, especially from TauCeti. But I did not find a complete set of imports covering the proof as written.** The principal unresolved dependencies are:

1. The general-position and intersection-chain machinery in Fact 2.4.
2. The **stratified** Morse-theoretic input in Fact 4.1.
3. The simultaneous semialgebraic triangulation in Fact 6.1.

The linear algebra and much of the homological algebra are in considerably better shape. There is also promising infrastructure for the simplicial–singular comparison, although I could not verify a ready-to-use theorem with precisely the required relative and naturality properties.

I traced the finite-$n$ result through Sections 2–6, excluding the upper-bound and asymptotic arguments needed only for Theorem 1.1.

**The strongest reusable components I found are these.** Here, “verified” means that I inspected the declaration or generated documentation; it does not mean that I built the dependency locally.

| Needed in your proof | Available source | Assessment |
|---|---|---|
| Spectral theorem, eigenvalues, trace, positive semidefinite matrices | Mathlib: `Analysis.Matrix.Spectrum`, `Analysis.Matrix.PosDef` | **Verified.** Supplies the main general linear algebra behind Lemma 3.1. |
| Negative index of a possibly degenerate quadratic form | Mathlib: `LinearAlgebra.QuadraticForm.Signature` | **Verified.** Particularly useful for the index bound and its persistence under perturbation. |
| Abstract complexes and their geometric realizations | Mathlib’s `AbstractSimplicialComplex`; TauCeti: `AlgebraicTopology.SimplicialComplex.Realization.Basic` | **Verified foundations.** Some adapters to your finite face/cochain conventions remain necessary. |
| Relative singular chains, relative homology, and the exact sequence of a pair | TauCeti: `AlgebraicTopology.Singular.Relative` | **Verified.** A substantial amount of foundational topology need not be rebuilt. |
| Polynomial semialgebraic sets | TauCeti: `Geometry.RealAlgebraic.Semialgebraic.Basic` | **Verified definitions and closure lemmas.** Useful for your $B_D,J_D$; this alone does not provide triangulation. |
| Ordinary Morse deformation and cell attachment | `qinz1yang/differential-geometry`, under `DifferentialGeometry.Topology.Morse` | **Verified theorem statements.** Useful building blocks, but their boundaryless hypotheses do not directly cover your stratified simplex. |
| Passing from column homology to total homology | `the-omega-institute/trureturing`, `FiniteDegreeComparison.lean` | **Verified theorem statement and proof.** A close match for the algebra behind Lemma 6.2. |

The precise findings and remaining work are as follows.

**Mathlib already supplies the difficult general linear algebra for Section 3.** In particular, I found:

- `Matrix.IsHermitian.spectral_theorem`
- `Matrix.IsHermitian.trace_eq_sum_eigenvalues`
- `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`
- `QuadraticForm.sigNeg`
- `QuadraticForm.exists_finrank_eq_sigNeg_and_negDef`
- `QuadraticForm.le_sigNeg_of_negDef`

The signature API defines the negative index through negative-definite subspaces and includes invariance under equivalence. This is a good fit even when the Hessian has a kernel. [1–3]

Your particular spectral argument would still need formalization: the derivative identities for $p_G$, the covariance inequality, the trace argument, and especially the equality case yielding the complete $r$-partite structure. But this looks like a self-contained development over existing foundations.

I would express the covariance calculation as a **finite weighted sum of positive semidefinite rank-one matrices**. That should avoid introducing a probability-space formalization merely to express the random-edge argument.

**TauCeti is the most useful external dependency for the topology.** Its [relative singular homology module](https://taucetiproject.org/docs/TauCeti/AlgebraicTopology/Singular/Relative.html) contains actual constructions and exactness results, including:

- `TopPair.singularChainComplex`
- `TopPair.singularHomology`
- `TopPair.singularHomologyδ`
- `TopPair.singularHomology_exact_subspace`
- `TopPair.singularHomology_exact_space`
- `TopPair.singularHomology_exact_relative`

These are coefficient-general constructions; specializing to modules over `ZMod 2` is the natural direction for this project. The documentation links to [commit-pinned source](https://github.com/TauCetiProject/TauCeti/blob/37587c55da27bfad28c393969456a5b685e996fa/TauCeti/AlgebraicTopology/Singular/Relative.lean). [4]

Its [simplicial realization module](https://taucetiproject.org/docs/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Basic.html) provides `AbstractSimplicialComplex.Realization`, barycentric coordinates, carriers, face inclusions, and realization maps. Thus the geometric meaning of a finite complex need not be defined from scratch. [5]

There are three substantial geometric obstacles.

**1. Fact 2.4 needs considerably more than simplicial approximation.**

For Theorem 2.5, the required package includes:

- Approximation of an arbitrary continuous map by a PL map in strong general position, measured against the **original faces**.
- Intersection maps
  $$
  I:C_k(T;\mathbb F_2)\longrightarrow C^{d-k}(X;\mathbb F_2)
  $$
  satisfying $\delta I=I\partial$.
- The support/locality property.
- The normalization that gives evaluation $1$ on the relevant fundamental cycle.

I did not locate a completed Lean package providing this combination in arbitrary dimension. TauCeti has extensive PL, subdivision, and realization infrastructure, but the existence of those modules does not establish this intersection theorem.

A nearby GitHub project, [verified-3d-mesh-intersection](https://github.com/schildep/verified-3d-mesh-intersection), has general-position utilities and a separate chain-intersection development. Its documented scope is three-dimensional mesh geometry, so it is not a direct supplier for Fact 2.4. [6]

For this theorem, I would formulate a narrow interface for the intersection data actually consumed by Theorem 2.5. That avoids first developing a general theory of intersection products on arbitrary PL manifolds.

**2. Ordinary Morse theory does not yet discharge Fact 4.1.**

The strongest independent source I inspected was [qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry). Its source contains:

- `no_critical_values`, giving transport between sublevels across a compact critical-point-free band.
- `one_critical_point_cell_attachment`, giving the expected cell attachment across a single nondegenerate critical point.

However, the statements use a **boundaryless ambient manifold**. [7–8]

Your argument concerns the simplex stratified by all its open faces. It needs control of critical points on proper faces and their normal Morse data, not just critical points in the interior. TauCeti’s Morse roadmap also explicitly distinguishes its ordinary boundaryless theory from general boundary-critical-point theory. [9]

The narrow theorem worth targeting is:

> For a compact simplex with its face stratification, if all stratified critical points in a band have tangential index at least $r$, then the relative homology across the band vanishes in degrees below $r$.

To recover your proof, this needs the appropriate generic approximation and deformation statements, followed by the passage to the zero sublevel. I did not find a verified import supplying that package.

I would **not** begin by formalizing arbitrary Whitney-stratified spaces. The simplex case is already enough and has much simpler local normal geometry.

**3. Fact 6.1 needs simultaneous compatibility, not merely semialgebraic decomposition.**

Your triangulation must simultaneously respect every $B_D$, every $J_D$, the original faces, and the uniform point $u$. The closed marked sets must become subcomplexes, and $u$ must become a vertex.

TauCeti has genuine semialgebraic definitions and polynomial sign-set lemmas, together with substantial cylindrical algebraic decomposition infrastructure. But a CAD is not itself the required compatible triangulation. [10–11]

There is an exceptionally close match in the [TauCeti AffineMorseLefschetz roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AffineMorseLefschetz/README.md): its Layer 5 explicitly calls for `finite_semialgebraic_triangulation`, with a compact semialgebraic set and a finite family of marked subsets; closed marks become subcomplexes. **I located the target specification, but not a completed implementation.** [12]

This is a particularly useful upstream development to track, because its intended statement is almost exactly Fact 6.1.

**The simplicial–singular comparison deserves a separate check before choosing the chain model.**

Section 6 needs the relative comparison with $\mathbb F_2$ coefficients, compatible with inclusions. An abstract isomorphism between two homology groups is not sufficient for all the assembly steps.

TauCeti’s roadmap identifies a native `cellularSingularHomologyIso` for finite-dimensional relative CW complexes. Its documentation index also lists ordered simplicial chain complexes and incidence/naturality modules. This suggests that a route through cellular homology may already be largely available. I could not inspect enough of the relevant declarations to certify the complete adapter to your simplicial chains. **I would classify this as promising but unverified, rather than missing.** [13–14]

The independent [Hatcher formalization](https://github.com/Deicyde/hatcher-at) reports completed relative, triple, and excision developments. But it explicitly lists Hatcher’s Theorem 2.27—the simplicial–singular comparison—as a later milestone. It therefore does not currently settle this dependency on the evidence I inspected. [15]

**Lemma 6.2 has a particularly close external supplier.** I found
`HomologicalComplex₂.finite_degree_comparison_total_map`
in [this pinned source file](https://github.com/the-omega-institute/trureturing/blob/34b75b0a5a65b9383fdfa85a169a2e2d3db33897/D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.lean).

It proves that suitable column-homology isomorphisms in a finite triangular range, with epimorphisms on the next diagonal, induce the corresponding total-homology comparison. My reading is that applying it to the map from your relative double complex to zero should give the required vanishing. The remaining work is constructing your double complex in its interface. Alternatively, your direct highest-column elimination proof is short enough that importing a large additional dependency solely for this lemma might not pay off. [16]

The manuscript-specific development would still include the following.

| Part | Work remaining even after importing the background |
|---|---|
| Section 2 | Admissible diagrams, support envelopes, budgets, the diagram differential, and the certificate criterion |
| Section 3 | The spectral critical-point theorem, including its rigidity/equality case |
| Section 4 | Finite face-critical values, index persistence, and the deduction of relative homology vanishing |
| Section 5 | Compatible bounded covers and the mass-deletion deformation of $(B_D,J_D)$ |
| Section 6 | The diagram-indexed double complexes, the evaluation cocycle, and the final certificate assembly |

Three conventions merit attention from the outset: use **ordinary unaugmented** chains as in the manuscript; preserve multiplicities in diagram boundaries; and distinguish a cocycle on the full simplex from the automatically top-degree cocycle condition on its $d$-skeleton.

I also checked sources beyond these main candidates:

- **OpenAI’s mathematics repository:** its coboundary-expander development is relevant to finite $\mathbb F_2$ cochains. The public specification uses a custom finite-complex model and treats degree-zero coboundaries as constant cochains, so its conventions require adaptation. I did not verify an intersection-theoretic supplier there. The `ComparatorChallenges` file is a specification containing `sorry`, not the proof module to import. [17–18]
- **LeanPool:** useful for discovering and importing maintained external projects; its current repository also uses TauCeti as a dependency. I did not locate an additional exact match for the three geometric gaps. [19]
- **Zenodo:** [lean-normal-forms](https://zenodo.org/records/21497259) supplies certified matrix normal forms and finite integer-homology computations. Useful for finite computations, but it does not replace the geometric arguments here. [20]
- **Palomar, Hexagon, Reservoir, and broader GitHub searches:** no further matching completed formalization was located in the accessible results. That is a search outcome, not a proof of absence.

**My recommendation is to build around mathlib plus a pinned TauCeti snapshot**, starting with the finite diagram algebra and Lemma 3.1. Before committing to the entire formalization, settle the three geometric interfaces above and verify the relative simplicial–singular adapter.

Use explicit TauCeti submodule imports: its root `TauCeti.lean` is intentionally empty. Also, the inspected TauCeti toolchain and the independent differential-geometry release use different Lean versions, so they should not be assumed to combine unchanged. [21–23]

A conditional formalization with precisely stated geometric hypotheses would be a useful intermediate result, but a complete formalization of Theorem 1.2 must discharge those hypotheses. Based on this search, the main remaining investment is in those geometric bridges; there is no reason to redevelop the spectral theorem or relative homology from scratch.

This assessment is based on source and documentation inspection, not a successful combined build or transitive axiom audit. Direct Palomar browser access was blocked by the session’s authorization gate, so that part of the search was limited to accessible public and indexed records.

## Sources

The numbered references replace the chat citation widgets with ordinary Markdown links. Repository links to moving branches reflect the material inspected on 8 November 2026; the two explicitly pinned source links retain their revisions.

1. [Mathlib: Matrix spectrum](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html).
2. [Mathlib: Positive definite and positive semidefinite matrices](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/PosDef.html).
3. [Mathlib: Quadratic-form signature](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/QuadraticForm/Signature.html).
4. [TauCeti: Relative singular homology](https://taucetiproject.org/docs/TauCeti/AlgebraicTopology/Singular/Relative.html); [pinned source](https://github.com/TauCetiProject/TauCeti/blob/37587c55da27bfad28c393969456a5b685e996fa/TauCeti/AlgebraicTopology/Singular/Relative.lean).
5. [TauCeti: Simplicial-complex realization](https://taucetiproject.org/docs/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Basic.html).
6. [verified-3d-mesh-intersection: Documented specification boundaries](https://github.com/schildep/verified-3d-mesh-intersection/blob/main/CLAUDE.md).
7. [DifferentialGeometry: No critical values](https://github.com/qinz1yang/differential-geometry/blob/main/DifferentialGeometry/Topology/Morse/RegularLevel/NoCriticalValues.lean).
8. [DifferentialGeometry: Smooth handle and cell attachment](https://github.com/qinz1yang/differential-geometry/blob/main/DifferentialGeometry/Topology/Morse/Attachment/SmoothHandle.lean).
9. [TauCeti: Morse theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/MorseTheory/README.md).
10. [TauCeti: Semialgebraic sets](https://taucetiproject.org/docs/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Basic.html).
11. [TauCeti: Cylindrical algebraic decomposition](https://taucetiproject.org/docs/TauCeti/Geometry/RealAlgebraic/CAD/Basic.html).
12. [TauCeti: Affine Morse–Lefschetz roadmap, Layer 5](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AffineMorseLefschetz/README.md).
13. [TauCeti: Algebraic topology roadmap, Stage 4](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AlgebraicTopology/README.md).
14. [TauCeti documentation module index](https://taucetiproject.org/docs/navbar.html).
15. [Hatcher formalization: §2.1 status and source notes](https://deicyde.github.io/hatcher-at/sources/hatcher-2-1.html).
16. [trureturing: Finite-degree comparison of total complexes, pinned source](https://github.com/the-omega-institute/trureturing/blob/34b75b0a5a65b9383fdfa85a169a2e2d3db33897/D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.lean).
17. [OpenAI mathematics: Coboundary expanders formalization scope](https://github.com/openai/math/blob/main/lean/docs/177.md).
18. [OpenAI mathematics: Coboundary expanders comparator specification](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/CoboundaryExpanders.lean).
19. [LeanPool](https://github.com/LeanPool/lean-pool).
20. [lean-normal-forms v1.2.2, Zenodo](https://zenodo.org/records/21497259).
21. [TauCeti root module](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti.lean).
22. [TauCeti toolchain](https://github.com/TauCetiProject/TauCeti/blob/main/lean-toolchain).
23. [DifferentialGeometry README and release/toolchain instructions](https://github.com/qinz1yang/differential-geometry).

