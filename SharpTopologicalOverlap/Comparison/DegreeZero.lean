module

public import SharpTopologicalOverlap.Comparison
public import SharpTopologicalOverlap.Singular
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

/-! # Normalized degree-zero comparison

This is the base case of the supported inverse construction: the uniform
point is sent to a prescribed vertex, and every other point is sent to a
vertex in its support. The affine edge gives the required homotopy.
-/

@[expose] public noncomputable section

open CategoryTheory Convexity
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V]

/-- The degree-zero basis cell at a vertex of the full simplex. -/
def vertexCell (v : V) : Cell (⊤ : AbstractSimplicialComplex V) 0 :=
  (fullCellEquiv V 0).symm ⟨{v}, by simp⟩

omit [LinearOrder V] [Fintype V] [Nonempty V] in
@[simp] theorem vertexCell_vertices (v : V) : (vertexCell v).1.1 = {v} := rfl

/-- A vertex selected in the point's support, with the uniform value prescribed. -/
def selectedVertex (x : V) (μ : Simplex V) : V := by
  classical
  exact if μ = uniform then x else (support_nonempty μ).choose

omit [LinearOrder V] in
theorem selectedVertex_mem_support (x : V) (μ : Simplex V) :
    selectedVertex x μ ∈ support μ := by
  classical
  by_cases h : μ = uniform
  · simp [selectedVertex, h]
  · simpa [selectedVertex, h] using (support_nonempty μ).choose_spec

omit [LinearOrder V] in
@[simp] theorem selectedVertex_uniform (x : V) : selectedVertex x uniform = x := by
  simp [selectedVertex]

/-- The linear degree-zero map, on the actual singular chain module. -/
def rhoZero (x : V) : SingularChain V 0 →ₗ[Coeff] Chain (⊤ : AbstractSimplicialComplex V) 0 :=
  TauCeti.chainsDesc fun s =>
    Finsupp.single (vertexCell (selectedVertex x (TopCat.toSSetObj₀Equiv s))) 1

omit [LinearOrder V] in
@[simp] theorem rhoZero_pointChain (x : V) (μ : Simplex V) :
    rhoZero x (TauCeti.pointChain Coeff μ) =
      Finsupp.single (vertexCell (selectedVertex x μ)) 1 := by
  simp [rhoZero, TauCeti.pointChain]

omit [LinearOrder V] in
@[simp] theorem rhoZero_uniform (x : V) :
    rhoZero x (TauCeti.pointChain Coeff (uniform : Simplex V)) =
      Finsupp.single (vertexCell x) 1 := by simp

omit [LinearOrder V] in
/-- The selected vertex remains in every precomplex containing the point. -/
theorem selectedVertex_mem (x : V) (μ : Simplex V) (L : PreAbstractSimplicialComplex V)
    (hμ : μ ∈ realizedComplex L) : {selectedVertex x μ} ∈ L :=
  (L.isRelLowerSet_faces hμ).2 (Finset.singleton_subset_iff.mpr (selectedVertex_mem_support x μ))
    (Finset.singleton_nonempty _)

/-- The affine singular edge between two probability vectors. -/
def affineEdge (μ ν : Simplex V) :
    (TopCat.toSSet.obj (TopCat.of (Simplex V))) _⦋1⦌ :=
  ((TopCat.of (Simplex V)).toSSetObjEquiv _).symm
    (StdSimplex.continuousAffineMapMk ![μ, ν])

omit [LinearOrder V] [Fintype V] [Nonempty V] in
@[simp] theorem affineEdge_face_zero (μ ν : Simplex V) :
    (TopCat.toSSet.obj (TopCat.of (Simplex V))).δ (0 : Fin 2) (affineEdge μ ν) =
      TopCat.toSSetObj₀Equiv.symm ν := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  have ht : t = StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
  subst t
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [affineEdge, Equiv.apply_symm_apply,
    StdSimplex.map_single, StdSimplex.continuousAffineMapMk_apply,
    StdSimplex.affineMapMk_single]
  rw [TopCat.toSSetObj₀Equiv_symm_apply, Equiv.apply_symm_apply]
  rfl

omit [LinearOrder V] [Fintype V] [Nonempty V] in
@[simp] theorem affineEdge_face_one (μ ν : Simplex V) :
    (TopCat.toSSet.obj (TopCat.of (Simplex V))).δ (1 : Fin 2) (affineEdge μ ν) =
      TopCat.toSSetObj₀Equiv.symm μ := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  have ht : t = StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
  subst t
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [affineEdge, Equiv.apply_symm_apply,
    StdSimplex.map_single, StdSimplex.continuousAffineMapMk_apply,
    StdSimplex.affineMapMk_single]
  rw [TopCat.toSSetObj₀Equiv_symm_apply, Equiv.apply_symm_apply]
  rfl

omit [LinearOrder V] [Fintype V] [Nonempty V] in
theorem singularBoundary_affineEdge (μ ν : Simplex V) :
    singularBoundary 0 (TauCeti.simplexChain (affineEdge μ ν) (1 : Coeff)) =
      TauCeti.pointChain Coeff ν + TauCeti.pointChain Coeff μ := by
  change ((TauCeti.singularChains Coeff).obj (TopCat.of (Simplex V))).d 1 0
    (TauCeti.simplexChain (affineEdge μ ν) 1) = _
  simp only [TauCeti.singularChains_d_simplexChain, TauCeti.pointChain]
  simp [← Int.cast_smul_eq_zsmul Coeff, show (-1 : Coeff) = 1 by decide]

omit [Fintype V] [Nonempty V] in
@[simp] theorem affineSimplex_vertexCell (v : V) :
    affineSimplex (vertexCell v) = TopCat.toSSetObj₀Equiv.symm (vertex v) := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  have ht : t = StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
  subst t
  rw [affineSimplex_apply]
  have hv : (vertexCell v).vertexEmbedding 0 = v :=
    Finset.mem_singleton.mp ((vertexCell v).vertexEmbedding_mem 0)
  simp only [StdSimplex.map_single, hv]
  rfl

/-- The affine edge to the selected support vertex, extended linearly. -/
def QZero (x : V) : SingularChain V 0 →ₗ[Coeff] SingularChain V 1 :=
  TauCeti.chainsDesc fun s =>
    TauCeti.simplexChain
      (affineEdge (TopCat.toSSetObj₀Equiv s)
        (vertex (selectedVertex x (TopCat.toSSetObj₀Equiv s)))) 1

omit [LinearOrder V] in
@[simp] theorem QZero_pointChain (x : V) (μ : Simplex V) :
    QZero x (TauCeti.pointChain Coeff μ) =
      TauCeti.simplexChain (affineEdge μ (vertex (selectedVertex x μ))) 1 := by
  simp [QZero, TauCeti.pointChain]

theorem singularBoundary_QZero (x : V) (c : SingularChain V 0) :
    singularBoundary 0 (QZero x c) = affineChainMap 0 (rhoZero x c) + c := by
  have he : (singularBoundary (V := V) 0).comp (QZero x) =
      (affineChainMap (K := (⊤ : AbstractSimplicialComplex V)) 0).comp (rhoZero x) +
        LinearMap.id := by
    apply TauCeti.singularChains_linearMap_ext
    intro s
    have hs : s = TopCat.toSSetObj₀Equiv.symm (TopCat.toSSetObj₀Equiv s) :=
      (Equiv.symm_apply_apply _ _).symm
    rw [hs]
    change singularBoundary 0 (QZero x (TauCeti.pointChain Coeff _)) =
      affineChainMap 0 (rhoZero x (TauCeti.pointChain Coeff _)) + TauCeti.pointChain Coeff _
    rw [QZero_pointChain, singularBoundary_affineEdge, rhoZero_pointChain,
      affineChainMap_single, affineSimplex_vertexCell]
  exact LinearMap.congr_fun he c

omit [Fintype V] [Nonempty V] in
/-- An affine edge between points in a coordinate face stays in that face. -/
theorem affineEdge_mem_closedFace (μ ν : Simplex V) (σ : Finset V)
    (hμ : μ ∈ closedFace σ) (hν : ν ∈ closedFace σ) (t : Simplex (Fin 2)) :
    (TopCat.of (Simplex V)).toSSetObjEquiv _ (affineEdge μ ν) t ∈ closedFace σ := by
  change support (StdSimplex.continuousAffineMapMk ![μ, ν] t) ⊆ σ
  rw [StdSimplex.continuousAffineMapMk_apply]
  intro i hi
  by_contra h
  have hμi : μ.weights i = 0 := Finsupp.notMem_support_iff.mp (fun hi => h (hμ hi))
  have hνi : ν.weights i = 0 := Finsupp.notMem_support_iff.mp (fun hi => h (hν hi))
  have hz : (StdSimplex.affineMapMk ![μ, ν] t).weights i = 0 := by
    simp [StdSimplex.weights_affineMapMk_apply, Fin.sum_univ_two, hμi, hνi]
  exact (mem_support.mp hi) hz

/-- Expand a singular chain in its concrete finite support. -/
theorem chain_eq_sum_simplexChain {X : TopCat.{0}} {k : ℕ} (c : Singular.Chain X k) :
    c = ∑ s ∈ (Singular.coefficients X k c).support,
      TauCeti.simplexChain s (Singular.coefficients X k c s) := by
  apply (Singular.coefficients X k).injective
  have hcoeff (s : Singular.Simplex X k) (r : Coeff) :
      Singular.coefficients X k (TauCeti.simplexChain s r) = Finsupp.single s r :=
    SSet.chainsLinearEquivFinsupp_ιChainComplex (TopCat.toSSet.obj X) s r
  simp only [map_sum, hcoeff]
  exact (Singular.coefficients X k c).sum_single.symm

/-- Degree zero preserves every ambient subcomplex simultaneously. -/
theorem rhoZero_carriedBy (x : V) (L : PreAbstractSimplicialComplex V)
    (c : SingularChain V 0) (hc : Singular.CarriedBy (realizedComplex L) c) :
    CarriedBy L (rhoZero x c) := by
  classical
  have hc' := (Singular.carriedBy_iff_support _ _).mp hc
  change rhoZero x c ∈ carriedSubmodule L
  rw [chain_eq_sum_simplexChain c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [rhoZero, TauCeti.chainsDesc_simplexChain]
  apply carriedBy_smul
  change Finsupp.single (vertexCell (selectedVertex x (TopCat.toSSetObj₀Equiv s))) (1 : Coeff) ∈
    carriedSubmodule L
  apply Finsupp.single_mem_supported
  apply selectedVertex_mem
  rw [TopCat.toSSetObj₀Equiv_apply]
  exact hc' s hs ⟨default, rfl⟩

/-- The degree-zero homotopy is also carried by every such subcomplex. -/
theorem QZero_carriedBy (x : V) (L : PreAbstractSimplicialComplex V)
    (c : SingularChain V 0) (hc : Singular.CarriedBy (realizedComplex L) c) :
    Singular.CarriedBy (realizedComplex L) (QZero x c) := by
  classical
  have hc' := (Singular.carriedBy_iff_support _ _).mp hc
  rw [chain_eq_sum_simplexChain c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [QZero, TauCeti.chainsDesc_simplexChain]
  apply Singular.carriedBy_smul
  apply singularSimplex_carriedBy
  rintro μ ⟨t, rfl⟩
  have hμ : TopCat.toSSetObj₀Equiv s ∈ realizedComplex L := by
    rw [TopCat.toSSetObj₀Equiv_apply]
    exact hc' s hs ⟨default, rfl⟩
  apply (L.isRelLowerSet_faces hμ).2 _ (support_nonempty _)
  apply affineEdge_mem_closedFace
  · exact Finset.Subset.refl _
  · exact (vertex_mem_closedFace).mpr (selectedVertex_mem_support x _)

end SharpTopologicalOverlap.Comparison
