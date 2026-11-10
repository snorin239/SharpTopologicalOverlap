module

public import SharpTopologicalOverlap.Simplex
public import SharpTopologicalOverlap.Simplicial.Subcomplex
public import SharpTopologicalOverlap.Singular
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-! # The canonical affine map from ordered simplicial chains

The generators are mapped to the affine singular simplices with the same
increasing vertex list. All chains land in the fixed ambient probability
simplex, allowing subcomplexes which omit vertices.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Convexity
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V]
variable {K : AbstractSimplicialComplex V} {k : ℕ}

/-- The singular chain module of the ambient probability simplex. -/
abbrev SingularChain (V : Type) (k : ℕ) :=
  ((TauCeti.singularChains Coeff).obj (TopCat.of (Simplex V))).X k

/-- The affine singular simplex associated with the increasing list of a face. -/
def affineSimplex (s : Cell K k) :
    (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k⦌ :=
  ((TopCat.of (Simplex V)).toSSetObjEquiv _).symm
    ⟨fun μ => μ.map s.vertexEmbedding, StdSimplex.continuous_map ℝ _⟩

@[simp] theorem affineSimplex_apply (s : Cell K k) (μ : Simplex (Fin (k + 1))) :
    (TopCat.of (Simplex V)).toSSetObjEquiv _ (affineSimplex s) μ =
      μ.map s.vertexEmbedding := by
  simp [affineSimplex]

/-- Taking a singular facet agrees with deleting the corresponding ordered vertex. -/
@[simp] theorem affineSimplex_face (s : Cell K (k + 1)) (j : Fin (k + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Simplex V))).δ j (affineSimplex s) =
      affineSimplex (s.face j) := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  change (μ.map j.succAbove).map s.vertexEmbedding =
    μ.map (s.face j).vertexEmbedding
  rw [← StdSimplex.map_comp, AbstractSimplicialComplex.RealizationCell.vertexEmbedding_face]

/-- The linear extension of the affine face generators. -/
def affineChainMap (k : ℕ) : Chain K k →ₗ[Coeff] SingularChain V k :=
  Finsupp.linearCombination Coeff (fun s => TauCeti.simplexChain (affineSimplex s) 1)

@[simp] theorem affineChainMap_single (s : Cell K k) (r : Coeff) :
    affineChainMap k (Finsupp.single s r) =
      TauCeti.simplexChain (affineSimplex s) r := by
  rw [affineChainMap, Finsupp.linearCombination_single]
  exact (TauCeti.simplexChain_eq_smul _ r).symm

/-- Distinct ordered cells give distinct affine singular simplices. -/
theorem affineSimplex_injective : Function.Injective (affineSimplex (K := K) (k := k)) := by
  intro s t hst
  have hv : ⇑s.vertexEmbedding = ⇑t.vertexEmbedding := by
    funext j
    apply StdSimplex.single_injective (R := ℝ)
    have hj := congrArg (fun σ =>
      (TopCat.of (Simplex V)).toSSetObjEquiv _ σ (StdSimplex.single j)) hst
    change (StdSimplex.single (R := ℝ) j).map s.vertexEmbedding =
      (StdSimplex.single (R := ℝ) j).map t.vertexEmbedding at hj
    simpa only [StdSimplex.map_single] using hj
  apply cell_vertices_injective
  change s.1.1 = t.1.1
  rw [← s.image_vertexEmbedding, ← t.image_vertexEmbedding, hv]

/-- On concrete coefficients the affine comparison is the injective map of its basis. -/
theorem coefficients_affineChainMap (c : Chain K k) :
    Singular.coefficients (TopCat.of (Simplex V)) k (affineChainMap k c) =
      Finsupp.mapDomain affineSimplex c := by
  have he :
      (Singular.coefficients (TopCat.of (Simplex V)) k).toLinearMap.comp
        (affineChainMap (K := K) k) = Finsupp.lmapDomain Coeff Coeff affineSimplex := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, affineChainMap_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact SSet.chainsLinearEquivFinsupp_ιChainComplex _ _ _
  exact LinearMap.congr_fun he c

/-- The affine chain map is already injective before passing to homology. -/
theorem affineChainMap_injective : Function.Injective (affineChainMap (K := K) k) := by
  intro c b h
  apply Finsupp.mapDomain_injective affineSimplex_injective
  rw [← coefficients_affineChainMap, ← coefficients_affineChainMap, h]

/-- Singular boundary, with successor degrees kept explicit. -/
abbrev singularBoundary (k : ℕ) : SingularChain V (k + 1) →ₗ[Coeff] SingularChain V k :=
  (((TauCeti.singularChains Coeff).obj (TopCat.of (Simplex V))).d (k + 1) k).hom

theorem singularBoundary_affineChainMap (c : Chain K (k + 1)) :
    singularBoundary k (affineChainMap (k + 1) c) = affineChainMap k (boundary k c) := by
  have he : (singularBoundary (V := V) k).comp (affineChainMap (K := K) (k + 1)) =
      (affineChainMap (K := K) k).comp (boundary (K := K) k) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      affineChainMap_single, singularBoundary, TauCeti.singularChains_d_simplexChain,
      boundary_single, map_sum, affineSimplex_face]
    congr 1
    funext j
    simp [show (-1 : Coeff) = 1 by decide, ← Int.cast_smul_eq_zsmul Coeff]
  exact LinearMap.congr_fun he c

/-- An affine face generator stays in the closed coordinate face it represents. -/
theorem affineSimplex_mem_closedFace (s : Cell K k) (μ : Simplex (Fin (k + 1))) :
    (TopCat.of (Simplex V)).toSSetObjEquiv _ (affineSimplex s) μ ∈ closedFace s.1.1 := by
  rw [affineSimplex_apply]
  intro v hv
  change v ∈ (μ.weights.mapDomain s.vertexEmbedding).support at hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact s.vertexEmbedding_mem i

/-- A face belonging to a subcomplex has its entire affine generator there. -/
theorem affineSimplex_mem_realizedComplex (L : PreAbstractSimplicialComplex V)
    (s : Cell K k) (hs : s.1.1 ∈ L) (μ : Simplex (Fin (k + 1))) :
    (TopCat.of (Simplex V)).toSSetObjEquiv _ (affineSimplex s) μ ∈ realizedComplex L :=
  (L.isRelLowerSet_faces hs).2 (affineSimplex_mem_closedFace s μ) (support_nonempty _)

/-- The ordered affine generator is independent of which ambient complex contains its face. -/
theorem affineSimplex_includeCell {M : AbstractSimplicialComplex V}
    (h : K ≤ M) (s : Cell K k) : affineSimplex (includeCell h s) = affineSimplex s := by
  have hv : ⇑(includeCell h s).vertexEmbedding = ⇑s.vertexEmbedding := by
    apply (Finset.orderEmbOfFin_unique s.2 (includeCell h s).vertexEmbedding_mem
      (includeCell h s).strictMono_vertexEmbedding).trans
    exact (Finset.orderEmbOfFin_unique s.2 s.vertexEmbedding_mem
      s.strictMono_vertexEmbedding).symm
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  change μ.map (includeCell h s).vertexEmbedding = μ.map s.vertexEmbedding
  rw [hv]

theorem affineChainMap_includeChain {M : AbstractSimplicialComplex V}
    (h : K ≤ M) (c : Chain K k) : affineChainMap k (includeChain h c) = affineChainMap k c := by
  have he : (affineChainMap (K := M) k).comp (includeChain h) = affineChainMap (K := K) k := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [affineSimplex_includeCell]
  exact LinearMap.congr_fun he c

/-- A singular generator is carried by every subspace containing its image. -/
theorem singularSimplex_carriedBy {X : TopCat.{0}} (A : Set X)
    (s : Singular.Simplex X k) (r : Coeff)
    (hs : Set.range (X.toSSetObjEquiv _ s) ⊆ A) :
    Singular.CarriedBy A (TauCeti.simplexChain s r) := by
  apply (Singular.carriedBy_iff_support _ _).mpr
  intro t ht
  change t ∈ ((TopCat.toSSet.obj X).chainsLinearEquivFinsupp Coeff k
    ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of Coeff Coeff) s r)).support at ht
  rw [SSet.chainsLinearEquivFinsupp_ιChainComplex] at ht
  have hts : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact hts ▸ hs

/-- The canonical affine comparison preserves the given ambient subcomplex. -/
theorem affineChainMap_carriedBy (L : PreAbstractSimplicialComplex V) (c : Chain K k)
    (hc : CarriedBy L c) : Singular.CarriedBy (realizedComplex L) (affineChainMap k c) := by
  classical
  have hsum : affineChainMap k c =
      ∑ s ∈ c.support, TauCeti.simplexChain (affineSimplex s) (c s) := by
    conv_lhs => rw [← c.sum_single]
    simp only [Finsupp.sum, map_sum, affineChainMap_single]
  rw [hsum]
  apply Submodule.sum_mem
  intro s hs
  apply singularSimplex_carriedBy
  rintro μ ⟨t, rfl⟩
  exact affineSimplex_mem_realizedComplex L s (hc s hs) t

/-- The affine comparison as a morphism of the actual chain complexes. -/
def affineChainComplexMap (K : AbstractSimplicialComplex V) :
    TauCeti.orderedSimplicialChainComplex K Coeff ⟶
      (TauCeti.singularChains Coeff).obj (TopCat.of (Simplex V)) :=
  ChainComplex.ofHom (fun k =>
    eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff k) ≫
      ModuleCat.ofHom (affineChainMap (K := K) k)) fun k => by
    simp only [TauCeti.orderedSimplicialChainComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [cancel_epi]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact singularBoundary_affineChainMap c

/-- The least precomplex whose realization contains the image of a singular simplex. -/
def simplexCarrier (s : (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k⦌) :
    PreAbstractSimplicialComplex V where
  faces := {τ | τ.Nonempty ∧ ∃ μ : Simplex (Fin (k + 1)),
    τ ⊆ support ((TopCat.of (Simplex V)).toSSetObjEquiv _ s μ)}
  isRelLowerSet_faces := by
    rintro τ ⟨hτ, μ, hμ⟩
    exact ⟨hτ, fun σ hστ hσ => ⟨hσ, μ, hστ.trans hμ⟩⟩

omit [LinearOrder V] in
@[simp] theorem mem_simplexCarrier
    (s : (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k⦌) (τ : Finset V) :
    τ ∈ simplexCarrier s ↔ τ.Nonempty ∧ ∃ μ : Simplex (Fin (k + 1)),
      τ ⊆ support ((TopCat.of (Simplex V)).toSSetObjEquiv _ s μ) := Iff.rfl

omit [LinearOrder V] in
/-- The image really lies in the carrier, including at boundary points. -/
theorem singularSimplex_mem_simplexCarrier
    (s : (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k⦌)
    (μ : Simplex (Fin (k + 1))) :
    (TopCat.of (Simplex V)).toSSetObjEquiv _ s μ ∈ realizedComplex (simplexCarrier s) :=
  ⟨support_nonempty _, μ, Finset.Subset.refl _⟩

omit [LinearOrder V] in
/-- Any precomplex carrying the simplex contains the least carrier. -/
theorem simplexCarrier_le
    (s : (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k⦌)
    (L : PreAbstractSimplicialComplex V)
    (hL : ∀ μ : Simplex (Fin (k + 1)),
      (TopCat.of (Simplex V)).toSSetObjEquiv _ s μ ∈ realizedComplex L) :
    simplexCarrier s ≤ L := by
  rintro τ ⟨hτ, μ, hμ⟩
  exact (L.isRelLowerSet_faces (hL μ)).2 hμ hτ

omit [LinearOrder V] in
/-- Passing to a singular facet decreases the least carrier. -/
theorem simplexCarrier_face_le
    (s : (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋k + 1⦌) (j : Fin (k + 2)) :
    simplexCarrier ((TopCat.toSSet.obj (TopCat.of (Simplex V))).δ j s) ≤ simplexCarrier s := by
  rintro τ ⟨hτ, μ, hμ⟩
  exact ⟨hτ, μ.map j.succAbove, hμ⟩

end SharpTopologicalOverlap.Comparison
