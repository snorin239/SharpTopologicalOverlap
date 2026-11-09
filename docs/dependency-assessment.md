# Lean dependencies for sharp topological overlap

Assessed 9 November 2026 against the [current manuscript](../paper/sharp_topological_overlap.pdf) and its [TeX source](../paper/sharp_topological_overlap.tex). For $d\ge 2$ and $n>C_d$, Theorem 1.2 gives $\operatorname{ov}(f)\ge ((n-C_d)/(d+1))^{d+1}$ for every continuous $f$ from the realized $d$-skeleton to $\mathbb R^d$. Theorem 1.1 identifies the liminf of the normalized minimum with $\theta=(d+1)!/(d+1)^{d+1}$.

The project pins Lean 4.36.0-rc2, mathlib `1b1ccf4b088b`, and TauCeti `1e668f5e55bc`. All nine dependency revisions in TauCeti's manifest match the project lockfile. The paper-specific declaration is the definition of $C_d$. [Project manifest](../lake-manifest.json) · [Formalization status](../FORMALIZATION.md)

## Package decision

**TauCeti is the project's direct topology dependency.** The pinned revision contains the ordinary Morse band theorem needed in §5, arbitrarily small retracting neighborhoods of finite subcomplexes, relative singular chains, and ordered simplicial homology. **Use DifferentialGeometry as a source for selected Euclidean subdivision and placement lemmas.** The main comparison still to formalize is the isomorphism induced by the *specific affine chain map* in Theorem 2.3. Appendix A also requires an arbitrary-dimensional intersection-cochain construction. [Morse band][band] · [Retracting neighborhoods][neighborhood] · [Ordered comparison][ordered] · [Geometric subdivision][fine]

| Package and inspected revision | Lean / mathlib revision | Recommended use |
| --- | --- | --- |
| [TauCeti `1e668f5e55bc`][tc-tree] | 4.36.0-rc2 / `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` | Imported through the [project root](../SharpTopologicalOverlap.lean). The root names the four TauCeti modules explicitly. [Toolchain][tc-tool] · [Manifest][tc-lock] · [Package configuration][tc-lake] |
| [qinz1yang/differential-geometry `fd2f07fba4c6`][dg-tree] | 4.35.0-rc3 / `c55e6e786f49471c72fbddbec5415808896aec1e` | Port or upstream the geometric lemmas needed for §2.1 and Appendix A when working with mathlib's embedded complexes. Its [single-critical-point cell attachment][dg-attach] is a fallback for the ordinary Morse step. A direct import alongside TauCeti would require aligning their toolchains and mathlib APIs. [Toolchain][dg-tool] · [Manifest][dg-lock] |
| [Deicyde/hatcher-at `4ab64991caeb`][ha-tree] | 4.34.1 / `d13f23b723b8a846827a245b89c10fc7d3f11612` | Consult for Theorem 2.3. It proves that the identity simplex generates the relative homology of the standard simplex modulo its boundary. Its roadmap explicitly defers Hatcher 2.27. Consider porting that generator argument if needed for the comparison below. [Generator theorem][generator] · [Roadmap][ha-road] · [Toolchain][ha-tool] · [Manifest][ha-lock] |

The previous project pin was Lean 4.32.1. The last TauCeti snapshot before its move from 4.32.0 to 4.33.0-rc1 lacked the inspected relative chains, Morse band, iterated-neighborhood and ordered comparison modules. [Older tree][tc-old] · [Toolchain transition][tc-bump]

### Build and verification

On Windows, `lake build` passed with 8,833 jobs. Both project source files also passed `lake env lean` individually. A downstream file importing `SharpTopologicalOverlap` and `Mathlib.Data.ZMod.Basic` checked the Morse band conclusion on a finite-dimensional boundaryless manifold with coefficient object `ModuleCat.of (ZMod 2) (ZMod 2)`. Under the compact-band and regular-endpoint hypotheses, an index bound of $d+1$ gives vanishing for every $j\le d$. The application to the particular logarithmic barrier still requires the hypotheses proved in Lemmas 5.6–5.7.

Lean's `#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound` for that specialization and each of the following upstream declarations. These checks can be repeated after `import SharpTopologicalOverlap`.

```lean
#print axioms TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex
#print axioms AbstractSimplicialComplex.exists_iteratedOpenSimplicialNeighborhood_subset
#print axioms AbstractSimplicialComplex.exists_deformation_iteratedOpenSimplicialNeighborhood
#print axioms TauCeti.orderedSimplicialHomologyIsoSingularHomology
#print axioms TauCeti.singularChains_d_simplexChain
#print axioms TopPair.shortExact_singularChainComplexShortComplex
```

## Theorem 1.2, by proof dependency

The November 9 proof applies ordinary Morse theory on the **open** simplex, retracts a neighborhood of a simplicial zero set, and fills singular chains down the face poset. These changes retire the earlier draft's dependencies on stratified Morse theory, simultaneous semialgebraic triangulation of the weight spaces, and comparison of total double complexes.

| Paper item | Library support and remaining work |
| --- | --- |
| §1 and §2.1, Lemma 2.1 (`lem:sd`) | Represent the skeleton by points of `Convexity.StdSimplex ℝ (Fin n)` with `μ.weights.support.card ≤ d + 1`. A closed face allows support *contained* in the face. Mathlib's `PreAbstractSimplicialComplex` allows unused ambient vertices, important for subcomplexes such as $I_{G_\tau}$ on $[n]$. TauCeti identifies a finite abstract realization with its coordinate image and supplies the subdivision homeomorphism. DifferentialGeometry's `hasMeshLE.barycentricSubdivisionIter_of_face_card_le` gives exactly the factor $(m/(m+1))^j$ from a bound of $m+1$ vertices per face, even in a higher-dimensional ambient space. Identify subdivided faces inside each original face to reuse this in Appendix A. [Standard simplex][simplex] · [Abstract complexes][abstract] · [Finite realization][finite] · [Subdivision homeomorphism][sd] · [Mesh theorem][fine] |
| §2.2–2.3, Lemma 2.2 (`lem:prism`) | Use ordinary, unaugmented chains over `ZMod 2`. TauCeti supplies singular chains on generators, the boundary on a generator, relative chains as a cokernel, homotopy invariance for pairs and exactness for triples. Sections 5–6 use the prism with image in $H(\operatorname{im}c\times[0,1])$ and require a filling $c=\partial w+c'$ with $c'$ supported in the subspace. [Module chains][chains] · [Relative chains][relative] · [Homotopies of pairs][pairs] · [Triples][triple] |
| §2.3, Theorem 2.3 and Lemma 2.4 (`thm:hatcher`, `lem:comparison`) | The absolute comparison for the affine characteristic-simplex map on **each** ordered finite subcomplex is the input. The output is one chain map $\rho$ on the full simplex, preserving all subcomplexes and taking the uniform point to a prescribed vertex. [Ordered comparison][ordered] · [Naturality][natural] |
| §3, Lemma 3.1 (`lem:intersection`), proved in Appendix A | Formalize the five intersection-cochain properties together. DifferentialGeometry covers fine geometric subdivision and perturbation to affine independence. The simultaneous placement conditions, parity of intersection endpoints, and passage back to the original continuous map are further work. [Fine subdivisions][fine] · [Finite placements][position] |
| §2.4 and §4, Lemma 4.1 and Corollary 4.2 (`lem:spectral`, `cor:index`) | Pinned mathlib supplies `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`, `Matrix.IsHermitian.spectral_theorem`, `trace_eq_sum_eigenvalues` in the same namespace, rank-one positive semidefiniteness, and `QuadraticForm.sigNeg` with its negative-subspace characterization. Use finite weighted sums of centered outer products for the covariance. The project must identify the restricted Hessian, obtain at least $d$ negative directions at a full-support critical point of a nonempty cocycle's polynomial, and prove rigidity when there are exactly $d$. The cocycle parity argument gives complete $(d+1)$-partiteness and equal part masses, hence value $\theta=(d+1)!/(d+1)^{d+1}$. Restricting to the support then gives at least $d+1$ negative directions at every face-critical point with $0<p_G<\theta$. [Euler identity][euler] · [Spectrum][spectrum] · [Rank-one PSD][psd] · [Signature][signature] |
| §5.1–5.2, Lemmas 5.2, 5.5–5.7 and Theorems 5.3–5.4 (`lem:sard` through `lem:persistence`) | For 5.2 apply mathlib's `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` to the critical set in affine coordinates. Nonempty open sets have positive volume, so regular values are dense. TauCeti's band theorem supplies 5.5 directly, including multiple critical points at the same value. The logarithmic barrier estimates, its small Morse tilt, and persistence on a limiting support are project work. [Equal-dimensional Sard][sard] · [Morse band][band] · [Morse index][index] |
| §5.3, Theorem 5.1 (`thm:weights`) | The target is $H_j(\{p_G<\theta\},\{p_G=0\};\mathbb F_2)=0$ for $0\le j\le d$. Identify the zero set with the independence complex. TauCeti's `exists_iteratedOpenSimplicialNeighborhood_subset` and `exists_deformation_iteratedOpenSimplicialNeighborhood` give a retracting open neighborhood inside the strict sublevel. Push the compact image of a relative cycle toward the uniform point, choose barrier parameters and regular levels for that cycle, then transfer its filling back by the prism. Handle the empty cocycle separately. [Iterated neighborhoods][neighborhood] · [Regular values on a compact band][regular] |
| §6, Lemmas 6.1–6.2 and Theorem 1.2 (`lem:covers`, `lem:carriers`, `thm:finite`) | For each positive-dimensional face choose a maximal disjoint support family. The union of its vertices over subfaces yields the monotone $S_\tau$ and the stated bound $C_d$. Off $S_\tau$ the vertex cochains agree and define $G_\tau$. Deleting the exceptional mass by the displayed homotopy reduces $H_j(B_\tau,J_\tau)=0$ to Theorem 5.1. Under the strict contrary bound the uniform point lies in every $B_\tau$. Fill from dimension $d$ down to zero. The cycle condition and the two intermediate faces in each codimension-two interval cancel the boundary terms over $\mathbb F_2$. Evaluate via $\rho$ to obtain $1=E_d=\cdots=E_0=0$. These are project lemmas over finite sets and the preceding chain operations. [Current proof, §6](../paper/sharp_topological_overlap.tex#L446) |

### From the Morse band to a filling

The declaration to import for Lemma 5.5 is
`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex`
in `TauCeti.Geometry.Manifold.Morse.Cell.Band`. Take the coefficient category to be `ModuleCat (ZMod 2)` and its coefficient object to be the rank-one module. Use the open simplex as an open subset of the affine hyperplane $\sum_i\mu_i=1$, with tangent model $\sum_i x_i=0$. The theorem takes regular endpoints, compactness of their closed band, and a lower index bound at every critical point there. Set its cutoff to $d+1$ and take $j<d+1$. Properness of the barrier supplies compactness. The imported proof already assembles the regular and critical levels of Theorems 5.3 and 5.4. [Band theorem][band] · [Deformation on a regular band][deform] · [Relative homology across a critical level][critical]

For Lemmas 5.6–5.7, identify the projected gradient derivative with the tangent Hessian, so a regular tilt gives TauCeti's Morse predicate. Its Euclidean Morse index is `sigNeg` of the Hessian quadratic form. The key estimate is on a fixed negative subspace in the limiting face. The barrier terms $\varepsilon x_i^2/\mu_i^2$ tend uniformly to zero there because those coordinates stay positive. The full Hessians need not converge as other coordinates tend to zero. This identifies precisely where the spectral result enters the imported theorem. [Euclidean Morse index][eindex] · [Manifold Morse index][index]

For the chain interface, specialize the relative short exact sequence to modules. Lift a boundary in the quotient degreewise to obtain $w$, then lift the remaining kernel element from the subspace to obtain $c'$. Include degree zero, where every 0-chain is a cycle. For the prism, restrict the homotopy to the image of the chain and take its image as codomain. Naturality of the chain homotopy under the two inclusions supplies the support bound. This is also needed for the prism on $\partial c$, which must stay in the smaller space. [Relative short exact sequence][relative] · [Exactness on elements][exact] · [Prism naturality][prism] · [Chains in a subspace][subspace]

### The affine comparison and the PL construction

**Theorem 2.3 and Lemma 2.4.** TauCeti's `orderedSimplicialHomologyIsoSingularHomology` factors through cellular chains. For the manuscript's induction one must show that $H_*(\iota_L)$ is an isomorphism for the map taking each ordered face to its affine singular simplex. The naturality module identifies the ordered and cellular chain maps under inclusions. I found no declaration identifying the displayed homology isomorphism with $H_*(\iota_L)$. A concrete way to finish is to identify each affine simplex with the relative generator for its cell, then use the exact sequences for consecutive skeleta. TauCeti supplies the characteristic-pair homology isomorphism, and hatcher-at proves the identity-simplex generator theorem in its own model. [Ordered comparison][ordered] · [Characteristic pairs][cell] · [Identity-simplex generator][generator]

Once this is established, apply injectivity and surjectivity on the smallest subcomplex $L_s$ containing the image of each singular simplex $s$, as in Lemma 2.4. This produces a *single* $\rho$ commuting with boundary, carrying $S_*(|L|)$ into $C_*(L)$ for every $L$, and satisfying $\rho([u])=x$. The degree-$d+1$ chains in the final evaluation require the full simplex. A carrier $L_s$ can omit vertices of $[n]$. To apply the ordered comparison, reindex it as an `AbstractSimplicialComplex` on its actual vertex subtype and identify its ordered chains and realization with those included in the ambient simplex. The neighborhood theorem used in §5 already accepts a `PreAbstractSimplicialComplex` as its subcomplex. [Paper construction](../paper/sharp_topological_overlap.tex#L171) · [Subcomplex realization][subcomplex]

**Lemma 3.1.** The project needs a finite $d$-complex $T$, a $d$-cycle $\zeta$, and degree-$d-\dim\tau$ cochains $a_\tau$ on the full source simplex. Their five obligations are the facet coboundary identity, the vertex cocycle identity on $(d+1)$-faces, $\sum_{\tau\in\zeta} a_\tau=\mathbf 1$, a *single* common point in the original images of all $d$-faces containing any support face from any subface of a fixed $\tau$, and a matching bound $\lfloor d/p\rfloor$ on the support of each $p$-face cochain for $p>0$. Consequently the entire family $P_\tau$ of those $d$-faces has size at most $\operatorname{ov}(f)$. The matching bound gives the deletion count in §6. [Lemma 3.1](../paper/sharp_topological_overlap.tex#L216)

Appendix A gives the construction to follow. Prove the subdivided fundamental-chain boundary identity (A.1). In A.2 affine-independent perturbation supplies G2. G1 excludes a common intersection for disjoint families whose dimensions sum to less than $d(s-1)$ for $s$ members. Against each fixed target simplex, G3 excludes intersections below complementary dimension and G4 gives spanning direction spaces at or above it. Use one small perturbation for disjoint source faces and a second after subdividing the target simplex. Quantitative separation for finitely many compact images preserves joint incidence for the *original* map. In complementary dimensions count points modulo two. In dimensions summing to $d+1$ count the two ends of each nonempty intersection segment to obtain the coboundary identity. Cone the target boundary to close the fundamental chain, and use the edge path to the cone vertex for the full-simplex cocycle identity. I found reusable subdivision and general-position lemmas, but no Lean theorem giving these five conclusions together. [Appendix A](../paper/sharp_topological_overlap.tex#L589) · [Geometric mesh and refinement][fine] · [Affine-independent perturbations][position] · [TauCeti affine-chain mesh][chainmesh]

## Theorem 1.1 and the additional dependency in §7

The finite theorem gives the lower bound for every map. Use the attained finite range of the overlap count, a constant map to witness nonemptiness of the minimum, and `Nat.choose_le_pow_div`. For fixed $d$, eventually $n>C_d$, so the normalized minimum is at least $\theta(1-C_d/n)^{d+1}$. Take the liminf. [Binomial bound][choosebound]

For the upper bound, budget a separate formalization of **Bukh–Matoušek–Nivasch, Theorem 1.3** (paper Theorem 7.1, `thm:bmn`). I found no Lean implementation of the all-dimensional construction. A sufficient interface gives, for each fixed $d$, a constant $K_d$ and configurations of $n$ points for all sufficiently large $n$ such that *every* query point belongs to the closed convex hulls of at most $(n/(d+1))^{d+1}+K_dn^d$ indexed $(d+1)$-subsets. In the original §2 construction determinant signs give affine independence. After discarding at most $2d$ points for a given query, a containing simplex uses one point of each type. The product bound and the discarded subsets account for the main term and the error. Convex position is optional for this application. [BMN, Theorem 1.3 and §2][bmn]

Send the source vertices to the configuration and extend affinely. The image of each closed face is its convex hull. Mathlib supplies the barycentric description of finite convex hulls and `isEquivalent_choose`, namely $\binom nk\sim n^k/k!$ for fixed $k$. This gives the upper bound for the same liminf and the factor $(d+1)!$ in the paper's normalization. [Convex combinations][convex] · [Binomial asymptotic][choose]

## First implementation milestones

1. **Connect relative homology to the paper's fillings.** Use the rank-one coefficient module over `ZMod 2` and the relative short exact sequence to extract $c=\partial w+c'$ with $c'$ carried by the subspace. Check the degree-zero case and the support control for the prism before using these operations in §§5–6.
2. **Settle the two chain and geometry interfaces early.** On a finite ordered complex prove that the affine generator map induces the comparison, then construct $\rho$. For Appendix A, test subdivision on original faces and the point/segment parity identity before assembling general $T,\zeta,a_\tau$. These results determine the representations used in §6.
3. **Develop the independent pieces on the current pin.** State the overlap on the realized skeleton, prove §4's index and equality case, and implement the finite cochain and matching arguments. With the topology interfaces in place, assemble the barrier proof and descending fillings to finish Theorem 1.2. The BMN construction can proceed separately for Theorem 1.1.

[tc-tree]: https://github.com/TauCetiProject/TauCeti/tree/1e668f5e55bc20f2eb87f4ba49b48833470290d1
[tc-tool]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/lean-toolchain
[tc-lock]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/lake-manifest.json
[tc-lake]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/lakefile.toml
[tc-old]: https://github.com/TauCetiProject/TauCeti/tree/278ce66c349a60e7f96489c26b6d611be277f921/TauCeti
[tc-bump]: https://github.com/TauCetiProject/TauCeti/commit/a98ea8771fe237edca2339dfcb6d1beb4b9a2320
[dg-tree]: https://github.com/qinz1yang/differential-geometry/tree/fd2f07fba4c6c102ba626c59153ad98da8f0d442
[dg-tool]: https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/lean-toolchain
[dg-lock]: https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/lake-manifest.json
[ha-tree]: https://github.com/Deicyde/hatcher-at/tree/4ab64991caebe9666448db7980d349030bb18508
[ha-tool]: https://github.com/Deicyde/hatcher-at/blob/4ab64991caebe9666448db7980d349030bb18508/lean-toolchain
[ha-lock]: https://github.com/Deicyde/hatcher-at/blob/4ab64991caebe9666448db7980d349030bb18508/lake-manifest.json
[ha-road]: https://github.com/Deicyde/hatcher-at/blob/4ab64991caebe9666448db7980d349030bb18508/blueprint/roadmap/homology/simplicial-and-singular/README.md
[generator]: https://github.com/Deicyde/hatcher-at/blob/4ab64991caebe9666448db7980d349030bb18508/Hatcher/Singular/RelativeSimplexFundamentalClass.lean#L709-L717
[band]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Morse/Cell/Band.lean#L119-L132
[deform]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Morse/Deformation/Homology.lean
[critical]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Morse/Cell/Homology.lean#L106-L120
[index]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Morse/Index.lean#L78-L107
[eindex]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Analysis/Calculus/Morse/Index.lean#L272-L283
[regular]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Morse/Exhaustion.lean#L46-L62
[neighborhood]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Subdivision/IteratedNeighborhood.lean
[ordered]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/OrderedChainComplex.lean#L181-L190
[natural]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/CWComplex/Naturality.lean
[cell]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Cellular/CharacteristicMap.lean#L353-L363
[finite]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Finite.lean#L86-L105
[subcomplex]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Subcomplex.lean
[sd]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialComplex/Subdivision/Homeomorph.lean
[chains]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/ModuleChains/Basic.lean
[relative]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/Relative.lean
[pairs]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/Homotopy/Invariance.lean
[triple]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/Triple.lean
[prism]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/SimplicialSet/Homology/HomotopyInvariance.lean#L44-L58
[subspace]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/Subspace.lean#L29-L40
[chainmesh]: https://github.com/TauCetiProject/TauCeti/blob/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/AlgebraicTopology/Singular/Subdivision/Small/Basic.lean#L110-L146
[dg-attach]: https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/DifferentialGeometry/Topology/Morse/Attachment/SmoothHandle.lean#L932-L955
[fine]: https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/DifferentialGeometry/Topology/SimplicialComplex/Barycentric/Subdivision/FineSubdivision.lean#L106-L173
[position]: https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/DifferentialGeometry/Analysis/Convex/FiniteGeneralPosition.lean#L64-L76
[simplex]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Geometry/Convex/ConvexSpace/Defs.lean#L51-L66
[abstract]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean#L48-L57
[exact]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L46-L72
[euler]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean#L72-L75
[spectrum]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Analysis/Matrix/Spectrum.lean#L143-L242
[psd]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L451-L455
[signature]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean#L96-L112
[sard]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/MeasureTheory/Function/Jacobian.lean#L643-L654
[choosebound]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Data/Nat/Choose/Bounds.lean#L32-L36
[choose]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Analysis/SpecialFunctions/Choose.lean#L43-L52
[convex]: https://github.com/leanprover-community/mathlib4/blob/1b1ccf4b088b32fa3f23f2de1127433254a81e1e/Mathlib/Analysis/Convex/Combination.lean#L412-L423
[bmn]: https://kam.mff.cuni.cz/~matousek/first_sel_lemma.pdf
