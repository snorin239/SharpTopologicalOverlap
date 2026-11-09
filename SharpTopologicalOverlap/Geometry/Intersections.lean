module

public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import TauCeti.Analysis.Convex.OpenSimplex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Complementary intersections

The point-intersection part of Appendix A, Step 3. Spanning directions and
complementary dimensions give a unique affine intersection. Excluding proper
faces puts every convex-hull intersection in both open simplices. The open
simplex uses intrinsic interior, including its vertex in dimension zero.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Module

attribute [local instance] Classical.decEq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spanning subspaces of complementary dimensions have disjoint directions. -/
theorem disjoint_of_sup_eq_top_of_finrank_add [FiniteDimensional ℝ E]
    (S T : Submodule ℝ E) (hspan : S ⊔ T = ⊤)
    (hdim : finrank ℝ S + finrank ℝ T = finrank ℝ E) : Disjoint S T := by
  have h := S.finrank_sup_add_finrank_inf_eq T
  rw [hspan, finrank_top, hdim] at h
  exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp (by omega))

/-- Complementary simplices whose directions span have one affine intersection. -/
theorem affineSpan_inter_eq_singleton [FiniteDimensional ℝ E]
    {p q : ℕ} (s : Affine.Simplex ℝ E p) (t : Affine.Simplex ℝ E q)
    (hdim : p + q = finrank ℝ E)
    (hspan : (affineSpan ℝ (range s.points)).direction ⊔
      (affineSpan ℝ (range t.points)).direction = ⊤) :
    ∃ x : E, (affineSpan ℝ (range s.points) : Set E) ∩
      (affineSpan ℝ (range t.points) : Set E) = {x} := by
  apply AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl
    ⟨s.points 0, s.mem_affineSpan_range 0⟩
    ⟨t.points 0, t.mem_affineSpan_range 0⟩
  refine ⟨disjoint_of_sup_eq_top_of_finrank_add _ _ hspan ?_,
    codisjoint_iff.mpr hspan⟩
  have hs : finrank ℝ (affineSpan ℝ (range s.points)).direction = p := by
    rw [direction_affineSpan]
    exact s.independent.finrank_vectorSpan (Fintype.card_fin _)
  have ht : finrank ℝ (affineSpan ℝ (range t.points)).direction = q := by
    rw [direction_affineSpan]
    exact t.independent.finrank_vectorSpan (Fintype.card_fin _)
  rw [hs, ht]
  exact hdim

/-- Convex hulls in complementary affine spans meet in at most one point. -/
theorem convexHull_inter_subsingleton [FiniteDimensional ℝ E]
    {p q : ℕ} (s : Affine.Simplex ℝ E p) (t : Affine.Simplex ℝ E q)
    (hdim : p + q = finrank ℝ E)
    (hspan : (affineSpan ℝ (range s.points)).direction ⊔
      (affineSpan ℝ (range t.points)).direction = ⊤) :
    (convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points)).Subsingleton := by
  obtain ⟨x, hx⟩ := affineSpan_inter_eq_singleton s t hdim hspan
  intro a ha b hb
  have ha' : a ∈ (affineSpan ℝ (range s.points) : Set E) ∩
      (affineSpan ℝ (range t.points) : Set E) :=
    ⟨convexHull_subset_affineSpan _ ha.1, convexHull_subset_affineSpan _ ha.2⟩
  have hb' : b ∈ (affineSpan ℝ (range s.points) : Set E) ∩
      (affineSpan ℝ (range t.points) : Set E) :=
    ⟨convexHull_subset_affineSpan _ hb.1, convexHull_subset_affineSpan _ hb.2⟩
  rw [hx] at ha' hb'
  exact (Set.mem_singleton_iff.mp ha').trans (Set.mem_singleton_iff.mp hb').symm

/-- A simplex point missing all opposite faces has positive barycentric weights.
The assertion also covers a singleton simplex. -/
theorem mem_intrinsicInterior_of_notMem_opposite_faces
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E))
    (hfaces : ∀ v ∈ s, x ∉ convexHull ℝ (↑(s.erase v) : Set E)) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.mp hx
  have hpos : ∀ v ∈ s, 0 < w v := by
    intro v hv
    apply (hw₀ v hv).lt_of_ne'
    intro hzero
    apply hfaces v hv
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun y hy => hw₀ y (Finset.mem_of_mem_erase hy), ?_, ?_⟩
    · simpa [hzero] using (Finset.sum_erase_add s w hv).trans hw₁
    · simpa [hzero] using (Finset.sum_erase_add s (fun y => w y • y) hv).trans hwx
  rw [← Finset.setOfPred_mem, ← Subtype.range_coe_subtype,
    hs.mem_intrinsicInterior_convexHull_iff]
  refine ⟨fun v => w v, fun v => hpos v v.2, ?_, ?_⟩
  · simpa only [Finset.sum_coe_sort] using hw₁
  · rw [Finset.affineCombination_eq_linear_combination _ _ _
      (by simpa only [Finset.sum_coe_sort] using hw₁)]
    change (∑ v : s, w (v : E) • (v : E)) = x
    exact (Finset.sum_coe_sort s (fun y => w y • y)).trans hwx

/-- Below-complementary face exclusion forces every meeting point into both
open simplices. This is the proper-face step in Appendix A, property A4. -/
theorem inter_subset_intrinsicInterior_inter
    {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hsource : ∀ v ∈ s, Disjoint (convexHull ℝ (↑(s.erase v) : Set E))
      (convexHull ℝ (t : Set E)))
    (htarget : ∀ v ∈ t, Disjoint (convexHull ℝ (s : Set E))
      (convexHull ℝ (↑(t.erase v) : Set E))) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩
      intrinsicInterior ℝ (convexHull ℝ (t : Set E)) := by
  intro x hx
  exact ⟨mem_intrinsicInterior_of_notMem_opposite_faces hs hx.1
      (fun v hv h => Set.disjoint_left.mp (hsource v hv) h hx.2),
    mem_intrinsicInterior_of_notMem_opposite_faces ht hx.2
      (fun v hv h => Set.disjoint_left.mp (htarget v hv) hx.1 h)⟩

end SharpTopologicalOverlap.Geometry
