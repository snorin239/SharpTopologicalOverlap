module

public import SharpTopologicalOverlap.Intersection.Refinement
public import SharpTopologicalOverlap.Geometry.FaceInterpolation

/-! # Actual local intersection indicators and their refinement

The local contribution is the indicator of nonempty hull intersection. Its
pullback uses an actual simplicial chain refinement, with the same vertex
indices as the continuous interpolation.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open SharpTopologicalOverlap.Simplicial
open AbstractSimplicialComplex Set

attribute [local instance] Classical.propDecidable

variable {Q E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {L : AbstractSimplicialComplex Q} {k : ℕ}

/-- The complementary intersection count on one actual fine source simplex. -/
def localIndicator (y : Q → E) (B : Set E) : Cochain L k := by
  classical
  exact fun u => if (convexHull ℝ (y '' (u.1.1 : Set Q)) ∩ B).Nonempty then 1 else 0

@[simp] theorem localIndicator_ne_zero (y : Q → E) (B : Set E) (u : Cell L k) :
    localIndicator y B u ≠ 0 ↔
      (convexHull ℝ (y '' (u.1.1 : Set Q)) ∩ B).Nonempty := by
  classical
  simp [localIndicator]

@[simp] theorem localIndicator_empty (y : Q → E) :
    (localIndicator y (∅ : Set E) : Cochain L k) = 0 := by
  classical
  funext u
  simp [localIndicator]

@[simp] theorem localIndicator_vertex (y : Q → E) (B : Set E) (v : Q) :
    localIndicator y B (RealizationCell.vertex L v) = if y v ∈ B then 1 else 0 := by
  classical
  simp [localIndicator, RealizationCell.vertex_val, Set.singleton_inter_nonempty]

/-- A target set disjoint from the whole interpolated source misses every
source child, in every degree. -/
theorem localIndicator_eq_zero_of_range_disjoint (y : Q → E) (B : Set E)
    (hB : Disjoint (Set.range (Geometry.interpolate L y)) B) :
    (localIndicator y B : Cochain L k) = 0 := by
  classical
  funext u
  have hmiss : ¬ (convexHull ℝ (y '' (u.1.1 : Set Q)) ∩ B).Nonempty := by
    rintro ⟨z, hz, hzB⟩
    rw [← image_interpolate_faceInclusion L y u.1] at hz
    obtain ⟨x, _, hx⟩ := hz
    exact Set.disjoint_left.mp hB ⟨x, hx⟩ hzB
  simp [localIndicator, hmiss]

theorem localIndicator_eq_zero_of_range_subset (y : Q → E) (B C : Set E)
    (hsource : Set.range (Geometry.interpolate L y) ⊆ C) (hB : Disjoint C B) :
    (localIndicator y B : Cochain L k) = 0 :=
  localIndicator_eq_zero_of_range_disjoint y B (hB.mono hsource Set.Subset.rfl)

variable {n d : ℕ}

/-- Sum the actual local indicators on a refined source face, then regard it
as a cochain on the full source simplex in the same degree. -/
def refinedIndicator (hk : k ≤ d)
    (R : Chain (skeletonComplex (Fin n) d) k →ₗ[Coeff] Chain L k)
    (y : Q → E) (B : Set E) : Cochain (⊤ : AbstractSimplicialComplex (Fin n)) k :=
  extendSkeletonCochain hk (pullbackCochain R (localIndicator y B))

/-- Every supported original face has an actual image point in the target
cell. Chain cancellation cannot create a support without a local witness. -/
theorem refinedIndicator_support_incidence
    (hk : k ≤ d)
    (R : Chain (skeletonComplex (Fin n) d) k →ₗ[Coeff] Chain L k)
    (y : Q → E) (B : Set E) (e : L.Realization ≃ₜ Skeleton (Fin n) d)
    (hcarrier : ∀ (s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) k)
      (u : Cell L k), u ∈ (R (Finsupp.single (skeletonCellEquiv hk s) 1)).support →
        ∀ x ∈ Set.range (faceInclusion L u.1), e x ∈ skeletonFace d s.1.1) :
    ∀ σ ∈ supportFamily (refinedIndicator hk R y B),
      ((Geometry.interpolate L y ∘ e.symm) '' skeletonFace d σ ∩ B).Nonempty := by
  classical
  intro σ hσ
  have hcard := supportFamily_uniform (refinedIndicator hk R y B) σ hσ
  let s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) k :=
    (fullCellEquiv (Fin n) k).symm ⟨σ, hcard⟩
  have hs : refinedIndicator hk R y B s ≠ 0 :=
    (mem_supportFamily (refinedIndicator hk R y B) s).mp hσ
  change pullbackCochain R (localIndicator y B) (skeletonCellEquiv hk s) ≠ 0 at hs
  obtain ⟨u, hu, hi⟩ := exists_supported_cell_of_pullbackCochain_ne_zero R _ _ hs
  obtain ⟨z, hz, hzB⟩ := (localIndicator_ne_zero y B u).mp hi
  exact ⟨z, hull_subset_original_face_image L y e σ u.1 (hcarrier s u hu) hz, hzB⟩

end SharpTopologicalOverlap.Geometry
