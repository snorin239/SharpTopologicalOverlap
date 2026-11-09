module

public import TauCeti.Analysis.Normed.Affine.AddTorsor.Bases
public import TauCeti.Analysis.Convex.OpenSimplex
public import Mathlib.Analysis.Convex.Combination

/-! # Ambient continuous barycentric coordinates and closed faces -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.SimplexParity

open Set
open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous affine coordinate functions reading all affine combinations of
an independently indexed simplex. Existence is proved below. -/
structure Coordinates (p : ι → E) where
  coord : ι → E →ᴬ[ℝ] ℝ
  read : ∀ w : ι → ℝ, ∑ i, w i = 1 → ∀ i,
    coord i (Finset.univ.affineCombination ℝ p w) = w i
  vertex_self : ∀ i, coord i (p i) = 1
  vertex_ne : ∀ i j, i ≠ j → coord i (p j) = 0

theorem exists_coordinates {p : ι → E} (hp : AffineIndependent ℝ p) :
    Nonempty (Coordinates p) := by
  obtain ⟨f, hf, hself, hne⟩ := hp.exists_continuousAffineMap_apply_affineCombination
  exact ⟨⟨f, hf, hself, hne⟩⟩

variable {p : ι → E} (c : Coordinates p) [DecidableEq ι]

namespace Coordinates

omit [DecidableEq ι] in
theorem sum_coord {x : E} (hx : x ∈ affineSpan ℝ (range p)) :
    ∑ i, c.coord i x = 1 := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  simpa only [c.read w hw] using hw

omit [DecidableEq ι] in
theorem affineCombination_coord {x : E} (hx : x ∈ affineSpan ℝ (range p)) :
    Finset.univ.affineCombination ℝ p (fun i => c.coord i x) = x := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  simp only [c.read w hw]

theorem coord_nonneg_of_mem_hull {x : E} (hx : x ∈ convexHull ℝ (range p)) (i : ι) :
    0 ≤ c.coord i x := by
  apply (convexHull_min (s := range p) ?_
    ((convex_Ici (0 : ℝ)).affine_preimage (c.coord i).toAffineMap)) hx
  rintro _ ⟨j, rfl⟩
  change 0 ≤ c.coord i (p j)
  by_cases hij : i = j
  · subst j
    rw [c.vertex_self]
    exact zero_le_one
  · rw [c.vertex_ne i j hij]

omit [DecidableEq ι] in
theorem coord_zero_of_mem_face_span (A : Finset ι) {x : E}
    (hx : x ∈ affineSpan ℝ (p '' (A : Set ι))) {i : ι} (hi : i ∉ A) :
    c.coord i x = 0 := by
  let Z : AffineSubspace ℝ E := (AffineSubspace.mk' (0 : ℝ) (⊥ : Submodule ℝ ℝ)).comap
    (c.coord i).toAffineMap
  have hsub : p '' (A : Set ι) ⊆ Z := by
    rintro _ ⟨j, hj, rfl⟩
    change c.coord i (p j) ∈ AffineSubspace.mk' (0 : ℝ) (⊥ : Submodule ℝ ℝ)
    rw [AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, Submodule.mem_bot]
    exact c.vertex_ne i j (fun h => hi (h ▸ hj))
  have hxZ := (show affineSpan ℝ (p '' (A : Set ι)) ≤ Z from affineSpan_le.mpr hsub) hx
  change c.coord i x ∈ AffineSubspace.mk' (0 : ℝ) (⊥ : Submodule ℝ ℝ) at hxZ
  simpa only [AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, Submodule.mem_bot] using hxZ

omit [DecidableEq ι] in
theorem sum_face_coord (A : Finset ι) {x : E}
    (hx : x ∈ affineSpan ℝ (range p)) (hz : ∀ i ∉ A, c.coord i x = 0) :
    ∑ i ∈ A, c.coord i x = 1 := by
  rw [← c.sum_coord hx]
  exact Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => hz i hi)

omit [DecidableEq ι] in
theorem sum_face_coord_smul (A : Finset ι) {x : E}
    (hx : x ∈ affineSpan ℝ (range p)) (hz : ∀ i ∉ A, c.coord i x = 0) :
    ∑ i ∈ A, c.coord i x • p i = x := by
  calc
    (∑ i ∈ A, c.coord i x • p i) = ∑ i, c.coord i x • p i :=
      Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => by rw [hz i hi, zero_smul])
    _ = x := by
      rw [← Finset.affineCombination_eq_linear_combination _ _ _ (c.sum_coord hx)]
      exact c.affineCombination_coord hx

omit [DecidableEq ι] in
theorem mem_face_span_iff (A : Finset ι) {x : E}
    (hx : x ∈ affineSpan ℝ (range p)) :
    x ∈ affineSpan ℝ (p '' (A : Set ι)) ↔ ∀ i ∉ A, c.coord i x = 0 := by
  classical
  constructor
  · exact fun h i hi => c.coord_zero_of_mem_face_span A h hi
  · intro hz
    have hsum := c.sum_face_coord A hx hz
    have hcomb : A.affineCombination ℝ p (fun i => c.coord i x) = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      exact c.sum_face_coord_smul A hx hz
    rw [← hcomb]
    exact affineCombination_mem_affineSpan_image hsum (fun i hi hnot => (hnot hi).elim) p

theorem mem_face_hull_iff (A : Finset ι) {x : E}
    (hx : x ∈ affineSpan ℝ (range p)) :
    x ∈ convexHull ℝ (p '' (A : Set ι)) ↔
      (∀ i, 0 ≤ c.coord i x) ∧ ∀ i ∉ A, c.coord i x = 0 := by
  classical
  constructor
  · intro h
    refine ⟨fun i => c.coord_nonneg_of_mem_hull
      (convexHull_mono (Set.image_subset_range _ _) h) i, ?_⟩
    exact fun i hi => c.coord_zero_of_mem_face_span A (convexHull_subset_affineSpan _ h) hi
  · rintro ⟨hn, hz⟩
    have hsum := c.sum_face_coord A hx hz
    rw [← c.sum_face_coord_smul A hx hz]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hn i) hsum
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem mem_hull_iff {x : E} (hx : x ∈ affineSpan ℝ (range p)) :
    x ∈ convexHull ℝ (range p) ↔ ∀ i, 0 ≤ c.coord i x := by
  simpa only [Finset.coe_univ, Set.image_univ, Finset.mem_univ, not_true_eq_false,
    false_implies, implies_true, and_true] using c.mem_face_hull_iff Finset.univ hx

theorem mem_erased_face_hull_iff {x : E} (hx : x ∈ convexHull ℝ (range p)) (i : ι) :
    x ∈ convexHull ℝ (p '' (↑(Finset.univ.erase i) : Set ι)) ↔ c.coord i x = 0 := by
  classical
  rw [c.mem_face_hull_iff _ (convexHull_subset_affineSpan _ hx)]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not]
  exact ⟨fun h => h.2 i rfl, fun hi => ⟨fun j => c.coord_nonneg_of_mem_hull hx j,
    fun j hji => hji ▸ hi⟩⟩

theorem mem_erased_face_span_iff {x : E} (hx : x ∈ affineSpan ℝ (range p)) (i : ι) :
    x ∈ affineSpan ℝ (p '' (↑(Finset.univ.erase i) : Set ι)) ↔ c.coord i x = 0 := by
  rw [c.mem_face_span_iff _ hx]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not]
  exact ⟨fun h => h i rfl, fun hi j hji => hji ▸ hi⟩

theorem mem_double_erased_face_hull {x : E} (hx : x ∈ convexHull ℝ (range p))
    {i j : ι} (hi : c.coord i x = 0) (hj : c.coord j x = 0) :
    x ∈ convexHull ℝ (p '' (↑((Finset.univ.erase i).erase j) : Set ι)) := by
  apply (c.mem_face_hull_iff _ (convexHull_subset_affineSpan _ hx)).mpr
  refine ⟨fun k => c.coord_nonneg_of_mem_hull hx k, fun k hk => ?_⟩
  by_cases hki : k = i
  · exact hki ▸ hi
  by_cases hkj : k = j
  · exact hkj ▸ hj
  exact (hk (by simp [hki, hkj])).elim

end Coordinates

end SharpTopologicalOverlap.Geometry.SimplexParity
