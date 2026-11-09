module

public import SharpTopologicalOverlap.Geometry.BarycentricGeometry
public import SharpTopologicalOverlap.Geometry.BarycentricApproximation
public import SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! # The actual affine geometry of the distinguished target patch -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.TargetGeometry

open AbstractSimplicialComplex Set Finsupp
open scoped BigOperators
attribute [local instance] Convexity.ConvexSpace.ofModule

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev sphere (d : ℕ) := AbstractSimplicialComplex.standardSuccSimplexBoundary d

def patch (d : ℕ) : Finset (Fin (d + 2)) := Finset.univ.erase (Fin.last (d + 1))

def basePosition (D : Affine.Simplex ℝ E d) : Fin (d + 2) → E :=
  Fin.lastCases 0 D.points

def affineMap (D : Affine.Simplex ℝ E d) : (Fin (d + 2) →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ (basePosition D)

theorem affineMap_eq_sum (D : Affine.Simplex ℝ E d) (μ : Fin (d + 2) →₀ ℝ) :
    affineMap D μ = ∑ i : Fin (d + 1), μ i.castSucc • D.points i := by
  rw [affineMap, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rw [Fin.sum_univ_castSucc]
  simp only [basePosition, Fin.lastCases_castSucc, Fin.lastCases_last, smul_zero, add_zero]

/-- The affine image of an actual subdivision vertex of the target sphere. -/
def position (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d)) (q : M.Vertex) : E :=
  affineMap D (M.vertexPoint q).1

theorem position_eq_sum (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d))
    (q : M.Vertex) :
    position D M q = ∑ i : Fin (d + 1), (M.vertexPoint q).1 i.castSucc • D.points i :=
  affineMap_eq_sum D _

/-- A fine target face lies in the distinguished original facet. -/
def InPatch (M : BarycentricModel (sphere d)) (σ : Finset M.Vertex) : Prop :=
  ∀ q ∈ σ, (M.vertexPoint q).1.support ⊆ patch d

theorem InPatch.mono {M : BarycentricModel (sphere d)} {σ τ : Finset M.Vertex}
    (hτ : InPatch M τ) (hστ : σ ⊆ τ) : InPatch M σ :=
  fun q hq => hτ q (hστ hq)

theorem last_eq_zero_of_support_subset_patch {μ : Fin (d + 2) →₀ ℝ}
    (hμ : μ.support ⊆ patch d) : μ (Fin.last (d + 1)) = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro h
  have := hμ h
  simp [patch] at this

theorem sum_castSucc_eq_one {μ : Fin (d + 2) →₀ ℝ}
    (hsum : μ.sum (fun _ r => r) = 1) (hlast : μ (Fin.last (d + 1)) = 0) :
    ∑ i : Fin (d + 1), μ i.castSucc = 1 := by
  have hsum' : ∑ i : Fin (d + 2), μ i = 1 := by
    exact (Finsupp.sum_fintype μ (fun _ r => r) (fun _ => rfl)).symm.trans hsum
  rw [Fin.sum_univ_castSucc, hlast, add_zero] at hsum'
  exact hsum'

/-- The affine realization of the distinguished facet is injective. -/
theorem affineMap_injective_on_patch_vectors (D : Affine.Simplex ℝ E d)
    {μ ν : Fin (d + 2) →₀ ℝ}
    (hμsum : μ.sum (fun _ r => r) = 1) (hνsum : ν.sum (fun _ r => r) = 1)
    (hμlast : μ (Fin.last (d + 1)) = 0) (hνlast : ν (Fin.last (d + 1)) = 0)
    (heq : affineMap D μ = affineMap D ν) : μ = ν := by
  obtain ⟨c⟩ := SimplexParity.exists_coordinates D.independent
  have hμ := sum_castSucc_eq_one hμsum hμlast
  have hν := sum_castSucc_eq_one hνsum hνlast
  have hμmap : affineMap D μ = Finset.univ.affineCombination ℝ D.points
      (fun i : Fin (d + 1) => μ i.castSucc) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hμ, affineMap_eq_sum]
  have hνmap : affineMap D ν = Finset.univ.affineCombination ℝ D.points
      (fun i : Fin (d + 1) => ν i.castSucc) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hν, affineMap_eq_sum]
  have hcoord (i : Fin (d + 1)) : μ i.castSucc = ν i.castSucc := by
    rw [← c.read _ hμ i, ← hμmap, heq, hνmap, c.read _ hν i]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hμlast, hνlast]
  · exact hcoord j

theorem position_mem_target_hull (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (q : M.Vertex)
    (hq : (M.vertexPoint q).1.support ⊆ patch d) :
    position D M q ∈ convexHull ℝ (range D.points) := by
  rw [position, affineMap_eq_sum]
  exact (convex_convexHull ℝ _).sum_mem
    (fun i _ => Realization.nonneg _ (M.vertexPoint q) i.castSucc)
    (sum_castSucc_eq_one (Realization.sum_eq_one _ _)
      (last_eq_zero_of_support_subset_patch hq))
    (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))

theorem patch_cell_affineIndependent (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (σ : TauCeti.SetLike.Face M.complex)
    (hσ : InPatch M σ.1) : AffineIndependent ℝ (fun q : σ.1 => position D M q) := by
  classical
  have hsub : range (fun q : σ.1 => (M.vertexPoint q).1) ⊆
      convexHull ℝ ((fun v => Finsupp.single v (1 : ℝ)) '' (patch d : Set (Fin (d + 2)))) := by
    rintro _ ⟨q, rfl⟩
    exact mem_standardSimplex_iff.mpr ⟨Realization.nonneg _ _,
      Realization.sum_eq_one _ _, hσ q q.2⟩
  have hconv : convexHull ℝ (range (fun q : σ.1 => (M.vertexPoint q).1)) ⊆
      convexHull ℝ ((fun v => Finsupp.single v (1 : ℝ)) '' (patch d : Set (Fin (d + 2)))) :=
    convexHull_min hsub (convex_convexHull ℝ _)
  have hinj : Set.InjOn (affineMap D) (convexHull ℝ (range (fun q : σ.1 => (M.vertexPoint q).1))) := by
    intro μ hμ ν hν heq
    obtain ⟨_, hμsum, hμsub⟩ := mem_standardSimplex_iff.mp (hconv hμ)
    obtain ⟨_, hνsum, hνsub⟩ := mem_standardSimplex_iff.mp (hconv hν)
    exact affineMap_injective_on_patch_vectors D hμsum hνsum
      (last_eq_zero_of_support_subset_patch hμsub) (last_eq_zero_of_support_subset_patch hνsub) heq
  have h := (M.cell_affineIndependent σ).map_of_injOn_convexHull (affineMap D).toAffineMap hinj
  simpa only [position, Function.comp_def, LinearMap.coe_toAffineMap] using h

theorem continuous_targetMap (D : Affine.Simplex ℝ E d) :
    Continuous (fun μ : (sphere d).Realization => affineMap D μ.1) := by
  simp only [affineMap_eq_sum]
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i.castSucc).comp (continuous_realization_coe (sphere d))).smul continuous_const)

theorem patch_mem_sphere (d : ℕ) : patch d ∈ sphere d := by
  apply AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mpr
  refine ⟨Finset.card_pos.mp (by simp [patch]), ?_⟩
  exact Finset.erase_ssubset (Finset.mem_univ _)

/-- Insert zero weight at the vertex at infinity. -/
def patchPoint (w : Convexity.StdSimplex ℝ (Fin (d + 1))) : (sphere d).Realization := by
  let μ : Fin (d + 2) →₀ ℝ := Finsupp.equivFunOnFinite.symm (Fin.lastCases 0 w.weights)
  have hμ (i : Fin (d + 2)) : μ i = Fin.lastCases 0 (fun j => w.weights j) i := rfl
  have hn (i : Fin (d + 2)) : 0 ≤ μ i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [hμ, Fin.lastCases_last, le_refl]
    · simpa only [hμ, Fin.lastCases_castSucc, Finsupp.zero_apply] using w.nonneg j
  have hsum : μ.sum (fun _ r => r) = 1 := by
    rw [Finsupp.sum_fintype μ (fun _ r => r) (fun _ => rfl), Fin.sum_univ_castSucc]
    simp only [hμ, Fin.lastCases_last, Fin.lastCases_castSucc, add_zero]
    exact (Finsupp.sum_fintype w.weights (fun _ r => r) (fun _ => rfl)).symm ▸ w.total
  have hsupp : μ.support ⊆ patch d := by
    intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    subst i
    exact Finsupp.mem_support_iff.mp hi (by simp only [hμ, Fin.lastCases_last])
  letI : DecidableEq (Fin (d + 2)) := Classical.decEq _
  refine ⟨μ, mem_realization_iff.mpr ⟨patch d, patch_mem_sphere d, ?_⟩⟩
  rw [Finset.coe_image]
  exact mem_standardSimplex_iff.mpr ⟨hn, hsum, hsupp⟩

@[simp] theorem patchPoint_castSucc (w : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) : (patchPoint w).1 i.castSucc = w.weights i := by
  simp [patchPoint]

@[simp] theorem patchPoint_last (w : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (patchPoint w).1 (Fin.last (d + 1)) = 0 := by simp [patchPoint]

theorem patchPoint_support_subset (w : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (patchPoint w).1.support ⊆ patch d := by
  intro i hi
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  intro h
  subst i
  exact Finsupp.mem_support_iff.mp hi (patchPoint_last w)

theorem affineMap_patchPoint (D : Affine.Simplex ℝ E d)
    (w : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    affineMap D (patchPoint w).1 =
      Convexity.StdSimplex.affineMapMk (R := ℝ) D.points w := by
  rw [affineMap_eq_sum, Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  simp only [patchPoint_castSucc]

def patchVertices (M : BarycentricModel (sphere d)) (σ : Finset M.Vertex) : Finset M.Vertex := by
  classical
  exact σ.filter (fun q => (M.vertexPoint q).1.support ⊆ patch d)

@[simp] theorem mem_patchVertices {M : BarycentricModel (sphere d)}
    {σ : Finset M.Vertex} {q : M.Vertex} :
    q ∈ patchVertices M σ ↔ q ∈ σ ∧ (M.vertexPoint q).1.support ⊆ patch d := by
  classical
  simp [patchVertices]

theorem patchVertices_subset (M : BarycentricModel (sphere d)) (σ : Finset M.Vertex) :
    patchVertices M σ ⊆ σ := fun _ h => (mem_patchVertices.mp h).1

theorem patchVertices_mono (M : BarycentricModel (sphere d)) {σ τ : Finset M.Vertex}
    (h : σ ⊆ τ) : patchVertices M σ ⊆ patchVertices M τ := by
  intro q hq
  exact mem_patchVertices.mpr ⟨h (mem_patchVertices.mp hq).1, (mem_patchVertices.mp hq).2⟩

theorem patchVertices_eq_self {M : BarycentricModel (sphere d)} {σ : Finset M.Vertex}
    (hσ : InPatch M σ) : patchVertices M σ = σ := by
  classical
  exact Finset.filter_eq_self.mpr hσ

/-- A globally monotone geometric carrier, using the inside vertices also on
outer cone cells. Those outer carriers will be shown to lie in the boundary. -/
def targetCells (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d))
    (σ : Finset M.Vertex) : Set E :=
  convexHull ℝ (position D M '' (patchVertices M σ : Set M.Vertex))

theorem targetCells_mono (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d))
    {σ τ : Finset M.Vertex} (h : σ ⊆ τ) : targetCells D M σ ⊆ targetCells D M τ :=
  convexHull_mono (Set.image_mono (patchVertices_mono M h))

theorem targetCells_eq_hull_of_inPatch (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) {σ : Finset M.Vertex} (hσ : InPatch M σ) :
    targetCells D M σ = convexHull ℝ (position D M '' (σ : Set M.Vertex)) := by
  rw [targetCells, patchVertices_eq_self hσ]

theorem targetCells_subset_full_hull (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (σ : Finset M.Vertex) :
    targetCells D M σ ⊆ convexHull ℝ (position D M '' (σ : Set M.Vertex)) :=
  convexHull_mono (Set.image_mono (patchVertices_subset M σ))

theorem isCompact_targetCells (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (σ : Finset M.Vertex) : IsCompact (targetCells D M σ) :=
  ((patchVertices M σ).finite_toSet.image (position D M)).isCompact_convexHull ℝ

end SharpTopologicalOverlap.Geometry.TargetGeometry
