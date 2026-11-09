module

public import SharpTopologicalOverlap.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Probability simplices and their faces

The geometric simplex is Mathlib's finitely supported probability simplex.
Both closed and open faces use the support convention of the manuscript;
in particular an open zero-dimensional face contains its vertex.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

/-- The probability simplex on a vertex type. -/
abbrev Simplex (V : Type*) := Convexity.StdSimplex ℝ V

variable {V : Type*}

instance [Finite V] : T2Space (Simplex V) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).t2Space

/-- The usual finite-coordinate presentation of the probability simplex. -/
abbrev CoordinateSimplex (V : Type*) [Fintype V] :=
  {w : V → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- Coordinates identify the finitely supported and finite-function simplex presentations. -/
def coordinateHomeomorph [Fintype V] : Simplex V ≃ₜ CoordinateSimplex V := by
  have h : Set.range (fun μ : Simplex V => (μ.weights : V → ℝ)) =
      {w : V → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext w
    simp
  exact (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).toHomeomorph.trans
    (Homeomorph.setCongr h)

@[simp] theorem coordinateHomeomorph_apply [Fintype V] (μ : Simplex V) :
    (coordinateHomeomorph μ).1 = (μ.weights : V → ℝ) := rfl

/-- The coordinate change from the sup-norm function space to Euclidean space. -/
abbrev euclideanCoordinates [Fintype V] : (V → ℝ) ≃L[ℝ] EuclideanSpace ℝ V :=
  (EuclideanSpace.equiv V ℝ).symm

/-- The finite coordinate support of a probability vector. -/
def support (μ : Simplex V) : Finset V := μ.weights.support

@[simp] theorem mem_support {μ : Simplex V} {i : V} :
    i ∈ support μ ↔ μ.weights i ≠ 0 := Finsupp.mem_support_iff

theorem support_nonempty (μ : Simplex V) : (support μ).Nonempty :=
  μ.support_weights_nonempty

theorem coordinate_nonneg (μ : Simplex V) (i : V) : 0 ≤ μ.weights i :=
  μ.weights_nonneg i

theorem mem_support_iff_coordinate_pos {μ : Simplex V} {i : V} :
    i ∈ support μ ↔ 0 < μ.weights i := by
  rw [mem_support]
  exact ⟨fun h => (coordinate_nonneg μ i).lt_of_ne' h, ne_of_gt⟩

theorem coordinate_le_one (μ : Simplex V) (i : V) : μ.weights i ≤ 1 :=
  μ.weights_apply_le_one i

theorem sum_coordinates [Fintype V] (μ : Simplex V) : ∑ i, μ.weights i = 1 :=
  μ.total_of_fintype

theorem continuous_coordinate (i : V) :
    Continuous (fun μ : Simplex V => μ.weights i) :=
  Convexity.StdSimplex.continuous_weights_apply ℝ i

/-- The coordinate vertex concentrated at `i`. -/
abbrev vertex (i : V) : Simplex V := Convexity.StdSimplex.single i

@[simp] theorem support_vertex (i : V) : support (vertex i) = {i} := by
  simp [support, vertex]

/-- The uniform probability vector. -/
abbrev uniform [Fintype V] [Nonempty V] : Simplex V :=
  Convexity.StdSimplex.barycenter

@[simp] theorem coordinate_uniform [Fintype V] [Nonempty V] (i : V) :
    (uniform : Simplex V).weights i = (Fintype.card V : ℝ)⁻¹ :=
  Convexity.StdSimplex.weights_barycenter_apply i

@[simp] theorem support_uniform [Fintype V] [Nonempty V] :
    support (uniform : Simplex V) = Finset.univ := by
  ext i
  simp [coordinate_uniform, Fintype.card_ne_zero]

/-- The closed face on `σ`, including the empty face as the empty set. -/
def closedFace (σ : Finset V) : Set (Simplex V) := {μ | support μ ⊆ σ}

/-- The open face on `σ`, including each vertex in its open zero-face. -/
def openFace (σ : Finset V) : Set (Simplex V) := {μ | support μ = σ}

@[simp] theorem mem_closedFace {σ : Finset V} {μ : Simplex V} :
    μ ∈ closedFace σ ↔ support μ ⊆ σ := Iff.rfl

@[simp] theorem mem_openFace {σ : Finset V} {μ : Simplex V} :
    μ ∈ openFace σ ↔ support μ = σ := Iff.rfl

theorem openFace_subset_closedFace (σ : Finset V) : openFace σ ⊆ closedFace σ := by
  intro μ hμ
  exact (mem_openFace.mp hμ) ▸ Finset.Subset.refl σ

theorem closedFace_mono {σ τ : Finset V} (h : σ ⊆ τ) :
    closedFace σ ⊆ closedFace τ := fun _ hμ => Finset.Subset.trans hμ h

@[simp] theorem closedFace_empty : closedFace (∅ : Finset V) = ∅ := by
  ext μ
  simp only [mem_closedFace, Finset.subset_empty, Set.mem_empty_iff_false, iff_false]
  exact (support_nonempty μ).ne_empty

@[simp] theorem openFace_empty : openFace (∅ : Finset V) = ∅ := by
  ext μ
  simp only [mem_openFace, Set.mem_empty_iff_false, iff_false]
  exact (support_nonempty μ).ne_empty

@[simp] theorem closedFace_univ [Fintype V] : closedFace (Finset.univ : Finset V) = Set.univ := by
  ext μ
  simp

@[simp] theorem vertex_mem_closedFace {σ : Finset V} {i : V} :
    vertex i ∈ closedFace σ ↔ i ∈ σ := by
  simp

@[simp] theorem vertex_mem_openFace (i : V) : vertex i ∈ openFace {i} := by
  simp

@[simp] theorem openFace_singleton (i : V) : openFace {i} = {vertex i} := by
  ext μ
  exact Convexity.StdSimplex.support_weights_eq_singleton

@[simp] theorem closedFace_singleton (i : V) : closedFace {i} = {vertex i} := by
  ext μ
  rw [mem_closedFace, (support_nonempty μ).subset_singleton_iff]
  exact Convexity.StdSimplex.support_weights_eq_singleton

theorem closedFace_nonempty_iff (σ : Finset V) : (closedFace σ).Nonempty ↔ σ.Nonempty := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact (support_nonempty μ).mono hμ
  · rintro ⟨i, hi⟩
    exact ⟨vertex i, vertex_mem_closedFace.mpr hi⟩

theorem openFace_disjoint {σ τ : Finset V} (h : σ ≠ τ) :
    Disjoint (openFace σ) (openFace τ) := by
  rw [Set.disjoint_left]
  intro μ hσ hτ
  exact h ((mem_openFace.mp hσ).symm.trans (mem_openFace.mp hτ))

@[simp] theorem closedFace_inter [DecidableEq V] (σ τ : Finset V) :
    closedFace (σ ∩ τ) = closedFace σ ∩ closedFace τ := by
  ext μ
  simp [Finset.subset_inter_iff]

theorem mem_closedFace_iff_coordinate_eq_zero {σ : Finset V} {μ : Simplex V} :
    μ ∈ closedFace σ ↔ ∀ i ∉ σ, μ.weights i = 0 := by
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (mem_support.mpr hn))
  · intro h i hi
    by_contra hn
    exact (mem_support.mp hi) (h i hn)

theorem isClosed_closedFace (σ : Finset V) : IsClosed (closedFace σ) := by
  have h : closedFace σ = ⋂ i, ⋂ (_ : i ∉ σ), {μ : Simplex V | μ.weights i = 0} := by
    ext μ
    rw [mem_closedFace_iff_coordinate_eq_zero]
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_coordinate i) continuous_const

theorem isCompact_closedFace [Finite V] (σ : Finset V) : IsCompact (closedFace σ) :=
  (isClosed_closedFace σ).isCompact

/-- A complex's realization, viewed inside the ambient probability simplex. -/
def realizedComplex (K : PreAbstractSimplicialComplex V) : Set (Simplex V) :=
  {μ | support μ ∈ K}

@[simp] theorem mem_realizedComplex {K : PreAbstractSimplicialComplex V} {μ : Simplex V} :
    μ ∈ realizedComplex K ↔ support μ ∈ K := Iff.rfl

theorem realizedComplex_eq_iUnion_closedFace (K : PreAbstractSimplicialComplex V) :
    realizedComplex K = ⋃ σ ∈ K, closedFace σ := by
  ext μ
  simp only [mem_realizedComplex, Set.mem_iUnion, mem_closedFace]
  constructor
  · intro h
    exact ⟨support μ, h, Finset.Subset.refl _⟩
  · rintro ⟨σ, hσ, hμ⟩
    exact (K.isRelLowerSet_faces hσ).2 hμ (support_nonempty μ)

theorem realizedComplex_eq_iUnion_openFace (K : PreAbstractSimplicialComplex V) :
    realizedComplex K = ⋃ σ ∈ K, openFace σ := by
  ext μ
  simp only [mem_realizedComplex, Set.mem_iUnion, mem_openFace]
  constructor
  · intro h
    exact ⟨support μ, h, rfl⟩
  · rintro ⟨σ, hσ, hμ⟩
    exact hμ ▸ hσ

theorem isCompact_realizedComplex [Fintype V] (K : PreAbstractSimplicialComplex V) :
    IsCompact (realizedComplex K) := by
  rw [realizedComplex_eq_iUnion_closedFace]
  exact Set.toFinite K.faces |>.isCompact_biUnion fun σ _ => isCompact_closedFace σ

end SharpTopologicalOverlap
