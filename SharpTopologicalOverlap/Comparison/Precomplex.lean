module

public import SharpTopologicalOverlap.Comparison.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedMap
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Comparison for precomplexes on their actual vertices

A precomplex may omit ambient vertices. Reindexing it on the vertices whose
singletons are faces gives an abstract complex without adding any faces.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Convexity
open SharpTopologicalOverlap.Simplicial
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

variable {V : Type} [LinearOrder V]

attribute [local instance 1] Classical.propDecidable

/-- The vertices actually present in a precomplex. -/
abbrev ActualVertex (L : PreAbstractSimplicialComplex V) := {v : V // {v} ∈ L}

theorem singleton_mem_of_mem_face (L : PreAbstractSimplicialComplex V)
    {e : Finset V} (he : e ∈ L) {v : V} (hv : v ∈ e) : {v} ∈ L :=
  L.isRelLowerSet_faces.mem_of_le he (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)

/-- The same complex, with its vertex type reduced to actual singleton faces. -/
def actualComplex (L : PreAbstractSimplicialComplex V) : AbstractSimplicialComplex (ActualVertex L) where
  faces := {e | e.map (Function.Embedding.subtype _) ∈ L}
  isRelLowerSet_faces := by
    intro e he
    refine ⟨?_, ?_⟩
    · simpa only [Finset.map_nonempty] using (L.isRelLowerSet_faces he).1
    · intro s hse hs
      apply L.isRelLowerSet_faces.mem_of_le he (Finset.map_subset_map.mpr hse)
      exact Finset.map_nonempty.mpr hs
  singleton_mem v := by
    change ({v} : Finset (ActualVertex L)).map (Function.Embedding.subtype _) ∈ L
    simpa only [Finset.map_singleton, Function.Embedding.subtype_apply] using v.2

@[simp] theorem mem_actualComplex (L : PreAbstractSimplicialComplex V)
    (e : Finset (ActualVertex L)) :
    e ∈ actualComplex L ↔ e.map (Function.Embedding.subtype _) ∈ L := Iff.rfl

/-- The increasing vertex inclusion into the ambient full simplex. -/
def actualInclusion (L : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex.SimplicialMap (actualComplex L).toPreAbstractSimplicialComplex
      (⊤ : AbstractSimplicialComplex V).toPreAbstractSimplicialComplex where
  toFun := Subtype.val
  map_face' e he := by
    change (e.image Subtype.val).Nonempty
    exact Finset.image_nonempty.mpr ((actualComplex L).isRelLowerSet_faces he).1

theorem actualInclusion_strictMono (L : PreAbstractSimplicialComplex V) :
    StrictMono (actualInclusion L) := fun _ _ h => h

/-- Map an actual cell to the identical ambient face. -/
def actualCell (L : PreAbstractSimplicialComplex V) (k : ℕ) (s : Cell (actualComplex L) k) :
    SubcomplexCell (⊤ : AbstractSimplicialComplex V) L k :=
  ⟨s.map (actualInclusion L) (actualInclusion_strictMono L).injective.injOn, by
    rw [AbstractSimplicialComplex.RealizationCell.map_face,
      TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply]
    change s.1.1.image (actualInclusion L) ∈ L
    have hs : s.1.1.map (Function.Embedding.subtype _) ∈ L := s.1.2
    simpa only [actualInclusion, PreAbstractSimplicialComplex.SimplicialMap.coe_mk,
      Finset.map_eq_image, Function.Embedding.coe_subtype] using hs⟩

@[simp] theorem actualCell_vertices (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (s : Cell (actualComplex L) k) :
    (actualCell L k s).1.1.1 = s.1.1.map (Function.Embedding.subtype _) := by
  simp only [actualCell, AbstractSimplicialComplex.RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply,
    actualInclusion, PreAbstractSimplicialComplex.SimplicialMap.coe_mk, Finset.map_eq_image,
    Function.Embedding.coe_subtype]

theorem actualCell_injective (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Function.Injective (actualCell L k) := by
  intro s t h
  apply cell_vertices_injective
  apply Finset.map_injective (Function.Embedding.subtype _)
  simpa only [actualCell_vertices] using
    congrArg (fun c : SubcomplexCell (⊤ : AbstractSimplicialComplex V) L k => c.1.1.1) h

theorem actualCell_surjective (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Function.Surjective (actualCell L k) := by
  intro s
  let e := s.1.1.1
  have he : ∀ v ∈ e, {v} ∈ L := fun v hv => singleton_mem_of_mem_face L s.2 hv
  have hmap : (e.subtype (fun v => {v} ∈ L)).map (Function.Embedding.subtype _) = e :=
    Finset.subtype_map_of_mem he
  let t : Cell (actualComplex L) k := ⟨⟨e.subtype (fun v => {v} ∈ L), by
    change (e.subtype (fun v => {v} ∈ L)).map (Function.Embedding.subtype _) ∈ L
    rw [hmap]
    exact s.2⟩, by
      rw [← Finset.card_map (Function.Embedding.subtype _), hmap]
      exact s.1.2⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply cell_vertices_injective
  change (actualCell L k t).1.1.1 = s.1.1.1
  rw [actualCell_vertices L k t]
  exact hmap

/-- Cells are unchanged by reindexing on the actual vertices. -/
def actualCellEquiv (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Cell (actualComplex L) k ≃ SubcomplexCell (⊤ : AbstractSimplicialComplex V) L k :=
  Equiv.ofBijective (actualCell L k) ⟨actualCell_injective L k, actualCell_surjective L k⟩

/-- The concrete carried-chain equivalence, using the same face coefficients. -/
def actualChainEquiv (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Chain (actualComplex L) k ≃ₗ[Coeff] SubcomplexChain (⊤ : AbstractSimplicialComplex V) L k :=
  (Finsupp.domLCongr (actualCellEquiv L k)).trans
    (Finsupp.supportedEquivFinsupp (R := Coeff) (M := Coeff)
      ({s | s.1.1 ∈ L} : Set (Cell (⊤ : AbstractSimplicialComplex V) k))).symm

@[simp] theorem actualChainEquiv_single (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (s : Cell (actualComplex L) k) (r : Coeff) :
    (actualChainEquiv L k (Finsupp.single s r)).1 = Finsupp.single (actualCell L k s).1 r := by
  simp [actualChainEquiv, Finsupp.domLCongr_apply, actualCellEquiv]
  exact Finsupp.supportedEquivFinsupp_symm_single
    ({s | s.1.1 ∈ L} : Set (Cell (⊤ : AbstractSimplicialComplex V) k)) (actualCell L k s) r

theorem actualCell_face (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (s : Cell (actualComplex L) (k + 1)) (j : Fin (k + 2)) :
    (actualCell L k (s.face j)).1 = (actualCell L (k + 1) s).1.face j := by
  exact s.face_map (actualInclusion L) ((actualInclusion_strictMono L).strictMonoOn _) j

theorem boundary_actualChainEquiv (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Chain (actualComplex L) (k + 1)) :
    boundary k (actualChainEquiv L (k + 1) c).1 = (actualChainEquiv L k (boundary k c)).1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c b hc hb => simp only [map_add, Submodule.coe_add, hc, hb]
  | single s r => simp [boundary_single, actualCell_face]

section Realization

variable [Fintype V]

/-- The map of ambient probability simplices induced by actual vertex inclusion. -/
def actualSimplexInclusion (L : PreAbstractSimplicialComplex V) :
    C(Simplex (ActualVertex L), Simplex V) :=
  ⟨fun μ => μ.map Subtype.val, StdSimplex.continuous_map ℝ _⟩

theorem support_actualSimplexInclusion (L : PreAbstractSimplicialComplex V)
    (μ : Simplex (ActualVertex L)) :
    support (actualSimplexInclusion L μ) = (support μ).map (Function.Embedding.subtype _) := by
  exact Finsupp.support_mapDomain_embedding (Function.Embedding.subtype _) μ.weights

@[simp] theorem actualSimplexInclusion_coordinate (L : PreAbstractSimplicialComplex V)
    (μ : Simplex (ActualVertex L)) (i : ActualVertex L) :
    (actualSimplexInclusion L μ).weights i.1 = μ.weights i :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective μ.weights i

/-- Reindexing introduces no change in the realization's coordinates. -/
def actualRealizationInclusion (L : PreAbstractSimplicialComplex V) :
    C(realizedComplex (actualComplex L).toPreAbstractSimplicialComplex, realizedComplex L) := by
  have hmem : ∀ μ : realizedComplex (actualComplex L).toPreAbstractSimplicialComplex,
      actualSimplexInclusion L μ.1 ∈ realizedComplex L := by
    intro μ
    change support (actualSimplexInclusion L μ.1) ∈ L
    rw [support_actualSimplexInclusion]
    exact μ.2
  exact ⟨fun μ => ⟨actualSimplexInclusion L μ.1, hmem μ⟩,
    ((actualSimplexInclusion L).continuous.comp continuous_subtype_val).subtype_mk hmem⟩

theorem actualRealizationInclusion_injective (L : PreAbstractSimplicialComplex V) :
    Function.Injective (actualRealizationInclusion L) := by
  intro μ ν h
  apply Subtype.ext
  apply StdSimplex.ext
  ext i
  have hi := congrArg (fun x : realizedComplex L => x.1.weights i.1) h
  change (actualSimplexInclusion L μ.1).weights i.1 = (actualSimplexInclusion L ν.1).weights i.1 at hi
  simpa only [actualSimplexInclusion_coordinate] using hi

theorem sum_actual_coordinates (L : PreAbstractSimplicialComplex V) (μ : realizedComplex L) :
    (∑ i : ActualVertex L, μ.1.weights i.1) = 1 := by
  let S := Finset.univ.filter fun v => {v} ∈ L
  rw [← Finset.sum_subtype S (by simp [S]) (fun v => μ.1.weights v)]
  calc
    (∑ i ∈ S, μ.1.weights i) = ∑ i : V, μ.1.weights i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_contra h
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        singleton_mem_of_mem_face L μ.2 (mem_support.mpr h)⟩
    _ = 1 := sum_coordinates μ.1

/-- Restrict a realization point to its actual vertex coordinates. -/
def actualRealizationRestriction (L : PreAbstractSimplicialComplex V)
    (μ : realizedComplex L) : Simplex (ActualVertex L) :=
  coordinateHomeomorph.symm ⟨fun i : ActualVertex L => μ.1.weights i.1,
    fun i => coordinate_nonneg μ.1 i.1, sum_actual_coordinates L μ⟩

@[simp] theorem actualRealizationRestriction_coordinate (L : PreAbstractSimplicialComplex V)
    (μ : realizedComplex L) (i : ActualVertex L) :
    (actualRealizationRestriction L μ).weights i = μ.1.weights i.1 := by
  change (coordinateHomeomorph (actualRealizationRestriction L μ)).1 i = _
  simp only [actualRealizationRestriction, Homeomorph.apply_symm_apply]

theorem actualRealizationRestriction_inclusion (L : PreAbstractSimplicialComplex V)
    (μ : realizedComplex L) : actualSimplexInclusion L (actualRealizationRestriction L μ) = μ.1 := by
  apply StdSimplex.ext
  ext i
  by_cases hi : {i} ∈ L
  · exact (actualSimplexInclusion_coordinate L _ ⟨i, hi⟩).trans
      (actualRealizationRestriction_coordinate L μ ⟨i, hi⟩)
  · have hzero : (actualSimplexInclusion L (actualRealizationRestriction L μ)).weights i = 0 := by
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨j, rfl⟩
      exact hi j.2
    rw [hzero]
    symm
    by_contra h
    exact hi (singleton_mem_of_mem_face L μ.2 (mem_support.mpr h))

theorem actualRealizationRestriction_mem (L : PreAbstractSimplicialComplex V)
    (μ : realizedComplex L) :
    actualRealizationRestriction L μ ∈ realizedComplex (actualComplex L).toPreAbstractSimplicialComplex := by
  change (support (actualRealizationRestriction L μ)).map (Function.Embedding.subtype _) ∈ L
  rw [← support_actualSimplexInclusion, actualRealizationRestriction_inclusion]
  exact μ.2

theorem actualRealizationInclusion_surjective (L : PreAbstractSimplicialComplex V) :
    Function.Surjective (actualRealizationInclusion L) := by
  intro μ
  exact ⟨⟨actualRealizationRestriction L μ, actualRealizationRestriction_mem L μ⟩,
    Subtype.ext (actualRealizationRestriction_inclusion L μ)⟩

/-- The actual realization is homeomorphic to precisely the original ambient subspace. -/
def actualRealizationHomeomorph (L : PreAbstractSimplicialComplex V) :
    realizedComplex (actualComplex L).toPreAbstractSimplicialComplex ≃ₜ realizedComplex L := by
  letI : CompactSpace (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex) :=
    isCompact_iff_compactSpace.mp (isCompact_realizedComplex _)
  exact (Equiv.ofBijective (actualRealizationInclusion L)
    ⟨actualRealizationInclusion_injective L, actualRealizationInclusion_surjective L⟩).toHomeomorphOfContinuousClosed
        (actualRealizationInclusion L).continuous
        (actualRealizationInclusion L).continuous.isClosedMap

@[simp] theorem actualRealizationHomeomorph_apply (L : PreAbstractSimplicialComplex V)
    (μ : realizedComplex (actualComplex L).toPreAbstractSimplicialComplex) :
    actualRealizationHomeomorph L μ = actualRealizationInclusion L μ := rfl

def actualRealizationMap (L : PreAbstractSimplicialComplex V) :
    TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex) ⟶
      TopCat.of (realizedComplex L) := TopCat.ofHom (actualRealizationInclusion L)

def actualRealizationInverse (L : PreAbstractSimplicialComplex V) :
    TopCat.of (realizedComplex L) ⟶
      TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex) :=
  TopCat.ofHom ⟨(actualRealizationHomeomorph L).symm, (actualRealizationHomeomorph L).symm.continuous⟩

@[simp] theorem actualRealizationMap_inverse (L : PreAbstractSimplicialComplex V) :
    actualRealizationMap L ≫ actualRealizationInverse L = 𝟙 _ := by
  ext μ : 1
  exact (actualRealizationHomeomorph L).symm_apply_apply μ

@[simp] theorem actualRealizationInverse_map (L : PreAbstractSimplicialComplex V) :
    actualRealizationInverse L ≫ actualRealizationMap L = 𝟙 _ := by
  ext μ : 1
  exact (actualRealizationHomeomorph L).apply_symm_apply μ

/-- Singular chains of the two coordinate realizations agree by an actual homeomorphism. -/
def actualSingularHomeomorphEquiv (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k ≃ₗ[Coeff]
      Singular.Chain (TopCat.of (realizedComplex L)) k where
  toLinearMap := Singular.pushforward (actualRealizationMap L) k
  invFun := Singular.pushforward (actualRealizationInverse L) k
  left_inv c := by
    change Singular.pushforward (actualRealizationInverse L) k
      (Singular.pushforward (actualRealizationMap L) k c) = c
    rw [← Singular.pushforward_comp, actualRealizationMap_inverse, Singular.pushforward_id]
  right_inv c := by
    change Singular.pushforward (actualRealizationMap L) k
      (Singular.pushforward (actualRealizationInverse L) k c) = c
    rw [← Singular.pushforward_comp, actualRealizationInverse_map, Singular.pushforward_id]

theorem boundary_actualSingularHomeomorphEquiv (L : PreAbstractSimplicialComplex V)
    (k : ℕ) (c : Singular.Chain
      (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) (k + 1)) :
    Singular.boundary k (actualSingularHomeomorphEquiv L (k + 1) c) =
      actualSingularHomeomorphEquiv L k (Singular.boundary k c) :=
  Singular.boundary_pushforward (actualRealizationMap L) c

/-- Include the actual realization's singular chains in the original ambient simplex. -/
def actualSingularInclusion (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k →ₗ[Coeff]
      SingularChain V k :=
  (Singular.pushforward (Singular.inclusion (X := TopCat.of (Simplex V)) (realizedComplex L)) k).comp
    (actualSingularHomeomorphEquiv L k).toLinearMap

theorem actualSingularInclusion_injective (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Function.Injective (actualSingularInclusion L k) :=
  (Singular.inclusion_injective (X := TopCat.of (Simplex V)) (realizedComplex L)).comp (actualSingularHomeomorphEquiv L k).injective

theorem actualSingularInclusion_carriedBy (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k) :
    Singular.CarriedBy (realizedComplex L) (actualSingularInclusion L k c) :=
  ⟨actualSingularHomeomorphEquiv L k c, rfl⟩

theorem exists_actualSingular_lift (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : SingularChain V k) (hc : Singular.CarriedBy (realizedComplex L) c) :
    ∃ b : Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k,
      actualSingularInclusion L k b = c := by
  obtain ⟨b, hb⟩ := hc
  exact ⟨(actualSingularHomeomorphEquiv L k).symm b, by
    change Singular.pushforward (Singular.inclusion (X := TopCat.of (Simplex V)) (realizedComplex L)) k
      (actualSingularHomeomorphEquiv L k ((actualSingularHomeomorphEquiv L k).symm b)) = c
    rw [LinearEquiv.apply_symm_apply]
    exact hb⟩

theorem boundary_actualSingularInclusion (L : PreAbstractSimplicialComplex V)
    (k : ℕ) (c : Singular.Chain
      (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) (k + 1)) :
    singularBoundary k (actualSingularInclusion L (k + 1) c) =
      actualSingularInclusion L k (Singular.boundary k c) := by
  exact (Singular.boundary_pushforward _ _).trans
    (congrArg (Singular.pushforward (Singular.inclusion (X := TopCat.of (Simplex V)) (realizedComplex L)) k)
      (boundary_actualSingularHomeomorphEquiv L k c))

theorem actualCell_vertexEmbedding (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (s : Cell (actualComplex L) k) :
    ⇑(actualCell L k s).1.vertexEmbedding = Subtype.val ∘ s.vertexEmbedding := by
  simpa only [actualCell, actualInclusion, PreAbstractSimplicialComplex.SimplicialMap.coe_mk] using
    s.vertexEmbedding_map (actualInclusion L) ((actualInclusion_strictMono L).strictMonoOn _)

theorem actualAffineSimplex_natural (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (s : Cell (actualComplex L) k) :
    (TopCat.toSSet.map (actualRealizationMap L ≫ Singular.inclusion (X := TopCat.of (Simplex V)) (realizedComplex L))).app _
      (affineSimplexIn s) = affineSimplex (actualCell L k s).1 := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  change (μ.map s.vertexEmbedding).map Subtype.val = μ.map (actualCell L k s).1.vertexEmbedding
  rw [← StdSimplex.map_comp, actualCell_vertexEmbedding]

theorem actualSingularInclusion_eq_pushforward (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k) :
    actualSingularInclusion L k c =
      Singular.pushforward (actualRealizationMap L ≫ Singular.inclusion (X := TopCat.of (Simplex V)) (realizedComplex L)) k c :=
  (Singular.pushforward_comp _ _ c).symm

/-- Naturality for the exact affine comparison on the reindexed complex. -/
theorem actualAffineChainMap_natural (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Chain (actualComplex L) k) :
    actualSingularInclusion L k (affineChainMapIn (actualComplex L) k c) =
      affineChainMap k (actualChainEquiv L k c).1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c b hc hb => simp only [map_add, Submodule.coe_add, hc, hb]
  | single s r =>
      simp only [affineChainMapIn_single, actualSingularInclusion_eq_pushforward,
        Singular.pushforward, TauCeti.singularChains_map_f_simplexChain,
        actualChainEquiv_single, affineChainMap_single]
      exact congrArg (fun σ => TauCeti.simplexChain σ r) (actualAffineSimplex_natural L k s)

end Realization

end SharpTopologicalOverlap.Comparison
