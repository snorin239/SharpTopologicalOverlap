module

public import SharpTopologicalOverlap.Geometry.Placements
public import SharpTopologicalOverlap.Geometry.Subdivision
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph
public import TauCeti.Analysis.Normed.Affine.Centroid
public import Mathlib.Order.Prod.Lex.Basic

/-! # The concrete iterated barycentric subdivision model

Every step uses the abstract barycentric subdivision and its canonical
realization homeomorphism. The ambient coordinate maps compose linearly,
so the resulting vertex positions, face carriers, mesh and interpolation
all refer to these same subdivision indices.
-/

@[expose] public noncomputable section

open AbstractSimplicialComplex TauCeti.SetLike Finsupp Convexity
open scoped Topology

namespace SharpTopologicalOverlap.Geometry

universe u

variable {V : Type u}

/-- An actual finite abstract complex with its canonical coordinate realization
in the original complex. The iteration below constructs all these fields. -/
structure BarycentricModel (K : AbstractSimplicialComplex V) where
  Vertex : Type u
  vertexFintype : Fintype Vertex
  vertexLinearOrder : LinearOrder Vertex
  complex : AbstractSimplicialComplex Vertex
  homeomorph : complex.Realization ≃ₜ K.Realization
  linearMap : (Vertex →₀ ℝ) →ₗ[ℝ] (V →₀ ℝ)
  homeomorph_val : ∀ x, (homeomorph x).1 = linearMap x.1

attribute [instance] BarycentricModel.vertexFintype BarycentricModel.vertexLinearOrder

namespace BarycentricModel

variable {K : AbstractSimplicialComplex V}

@[implicit_reducible] def initial [Fintype V] [LinearOrder V] (K : AbstractSimplicialComplex V) :
    BarycentricModel K where
  Vertex := V
  vertexFintype := inferInstance
  vertexLinearOrder := inferInstance
  complex := K
  homeomorph := Homeomorph.refl _
  linearMap := LinearMap.id
  homeomorph_val _ := rfl

/-- One genuine barycentric subdivision, retaining the composed original-coordinate map. -/
@[instance_reducible] def faceRankLinearOrder (M : BarycentricModel K) :
    LinearOrder (Face M.complex.toPreAbstractSimplicialComplex) := by
  let Q := Face M.complex.toPreAbstractSimplicialComplex
  let : Fintype Q := Fintype.ofFinite _
  let e := Fintype.equivFin Q
  exact LinearOrder.lift' (fun σ : Q => toLex (σ.1.card, e σ)) (by
    intro σ τ h
    apply e.injective
    exact congrArg (fun p : ℕ ×ₗ Fin (Fintype.card Q) => (ofLex p).2) h)

/-- One genuine barycentric subdivision, retaining the composed original-coordinate map. -/
@[implicit_reducible] def step (M : BarycentricModel K) : BarycentricModel K := by
  let Q := Face M.complex.toPreAbstractSimplicialComplex
  let : Fintype Q := Fintype.ofFinite _
  refine {
    Vertex := Q
    vertexFintype := inferInstance
    vertexLinearOrder := M.faceRankLinearOrder
    complex := TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      M.complex.toPreAbstractSimplicialComplex
    homeomorph := (barycentricSubdivisionRealizationHomeomorph M.complex).trans M.homeomorph
    linearMap := M.linearMap.comp (barycentricSubdivisionLinearMap M.complex)
    homeomorph_val := ?_ }
  intro x
  rw [Homeomorph.trans_apply, M.homeomorph_val,
    barycentricSubdivisionRealizationHomeomorph_apply,
    barycentricSubdivisionRealizationMap_val]
  rfl

/-- The subdivision order places every proper subface before the full face. -/
theorem step_lt_of_card_lt (M : BarycentricModel K)
    (σ τ : Face M.complex.toPreAbstractSimplicialComplex) (h : σ.1.card < τ.1.card) :
    @LT.lt M.step.Vertex M.step.vertexLinearOrder.toLT σ τ := by
  let : Fintype (Face M.complex.toPreAbstractSimplicialComplex) := Fintype.ofFinite _
  change toLex (σ.1.card, Fintype.equivFin _ σ) < toLex (τ.1.card, Fintype.equivFin _ τ)
  exact Prod.Lex.left _ _ h

/-- The original realization point of a subdivision vertex. -/
def vertexPoint (M : BarycentricModel K) (q : M.Vertex) : K.Realization :=
  M.homeomorph (AbstractSimplicialComplex.vertex M.complex q)

@[simp] theorem vertexPoint_val (M : BarycentricModel K) (q : M.Vertex) :
    (M.vertexPoint q).1 = M.linearMap (Finsupp.single q 1) := by
  rw [vertexPoint, M.homeomorph_val, vertex_val]

/-- Original coordinates of the model's realization map are globally linear
combinations of its own vertex positions. -/
theorem linearMap_eq_vertexPoint (M : BarycentricModel K) :
    M.linearMap = Finsupp.linearCombination ℝ (fun q => (M.vertexPoint q).1) := by
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  simp

theorem homeomorph_val_sum (M : BarycentricModel K) (x : M.complex.Realization) :
    (M.homeomorph x).1 = ∑ q ∈ x.1.support, x.1 q • (M.vertexPoint q).1 := by
  rw [M.homeomorph_val, M.linearMap_eq_vertexPoint, Finsupp.linearCombination_apply,
    Finsupp.sum]

/-- Every active fine vertex lies in every original closed face containing
the realized point. Positivity prevents cancellation of coordinate support. -/
theorem active_vertex_support_subset (M : BarycentricModel K) (x : M.complex.Realization)
    {σ : Finset V} (hx : (M.homeomorph x).1.support ⊆ σ)
    {q : M.Vertex} (hq : q ∈ x.1.support) : (M.vertexPoint q).1.support ⊆ σ := by
  intro v hv
  apply hx
  apply Finsupp.mem_support_iff.mpr
  have hqpos := Realization.pos_of_mem_support M.complex x hq
  have hvpos := Realization.pos_of_mem_support K (M.vertexPoint q) hv
  have hsum : x.1 q * (M.vertexPoint q).1 v ≤ (M.homeomorph x).1 v := by
    rw [M.homeomorph_val_sum]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.single_le_sum (fun r _ =>
      mul_nonneg (Realization.nonneg M.complex x r)
        (Realization.nonneg K (M.vertexPoint r) v)) hq
  exact ne_of_gt ((mul_pos hqpos hvpos).trans_le hsum)

/-- A fine point whose active vertices are carried by an original face is
itself carried by that face. -/
theorem homeomorph_support_subset (M : BarycentricModel K) (x : M.complex.Realization)
    (σ : Finset V) (hσ : ∀ q ∈ x.1.support, (M.vertexPoint q).1.support ⊆ σ) :
    (M.homeomorph x).1.support ⊆ σ := by
  intro v hv
  by_contra hvσ
  have hzero (q : M.Vertex) (hq : q ∈ x.1.support) : (M.vertexPoint q).1 v = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun h => hvσ (hσ q hq h)
  apply (Finsupp.mem_support_iff.mp hv)
  rw [M.homeomorph_val_sum]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_zero (fun q hq => by rw [hzero q hq, mul_zero])

/-- The next subdivision's face-barycenter vertex retains every original
face carrying all vertices of that face. -/
theorem step_vertexPoint_support_subset (M : BarycentricModel K)
    (ρ : Face M.complex.toPreAbstractSimplicialComplex) (σ : Finset V)
    (hσ : ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ) :
    (M.step.vertexPoint ρ).1.support ⊆ σ := by
  change (M.homeomorph ((barycentricSubdivisionRealizationHomeomorph M.complex)
    (AbstractSimplicialComplex.vertex
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        M.complex.toPreAbstractSimplicialComplex) ρ))).1.support ⊆ σ
  apply M.homeomorph_support_subset
  intro q hq
  rw [barycentricSubdivisionRealizationHomeomorph_apply,
    barycentricSubdivisionRealizationMap_vertex, Finsupp.mem_support_iff,
    faceBarycenter_apply] at hq
  have hqρ : q ∈ ρ.1 := by
    by_contra hnot
    simp only [ite_eq_right hnot, ne_eq, not_true_eq_false] at hq
  exact hσ q hqρ

/-- Every actual fine face lies in one original face, simultaneously for all
its vertices. This applies in particular to the sphere's original target faces. -/
theorem exists_originalFace_carrier (M : BarycentricModel K)
    (ρ : Face M.complex.toPreAbstractSimplicialComplex) :
    ∃ σ : Face K.toPreAbstractSimplicialComplex,
      ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ.1 := by
  classical
  let x : M.complex.Realization := faceInclusion M.complex ρ
    ⟨faceBarycenter M.complex ρ, faceBarycenter_mem M.complex ρ⟩
  have hxval : x.1 = faceBarycenter M.complex ρ := faceInclusion_val _ _ _
  refine ⟨carrier K (M.homeomorph x), fun q hq => ?_⟩
  rw [carrier_val]
  apply active_vertex_support_subset M x (Finset.Subset.refl _)
  rw [hxval, Finsupp.mem_support_iff, faceBarycenter_apply, ite_eq_left hq]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr
    (M.complex.isRelLowerSet_faces.prop_of_mem ρ.2).card_pos.ne')

end BarycentricModel

/-- The concrete iterated barycentric source complex, starting from `K`. -/
@[implicit_reducible] def barycentricModel [Fintype V] [LinearOrder V] (K : AbstractSimplicialComplex V) :
    ℕ → BarycentricModel K
  | 0 => .initial K
  | j + 1 => (barycentricModel K j).step

@[simp] theorem barycentricModel_zero [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) : barycentricModel K 0 = .initial K := rfl

@[simp] theorem barycentricModel_succ [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (j : ℕ) :
    barycentricModel K (j + 1) = (barycentricModel K j).step := rfl

end SharpTopologicalOverlap.Geometry
