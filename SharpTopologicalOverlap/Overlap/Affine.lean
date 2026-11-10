module

public import SharpTopologicalOverlap.BMN.Basic
public import SharpTopologicalOverlap.Geometry.PlacementAvoidance
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology

/-! # Affine maps from the source skeleton and their exact face images -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Set Convexity
open scoped BigOperators

attribute [local instance] ConvexSpace.ofModule

variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Affine interpolation of a placement on the coordinate source skeleton. -/
def affineSkeletonMap (d : ℕ) (p : V → E) : C(Skeleton V d, E) where
  toFun μ := StdSimplex.affineMapMk (R := ℝ) p μ.1
  continuous_toFun := (StdSimplex.continuous_of_affineMap _).comp continuous_subtype_val

@[simp] theorem affineSkeletonMap_apply (d : ℕ) (p : V → E) (μ : Skeleton V d) :
    affineSkeletonMap d p μ = ∑ i, μ.1.weights i • p i :=
  StdSimplex.affineMapMk_apply_eq_sum_of_fintype p μ.1

omit [Fintype V] in
theorem range_simplex_map_subtype (σ : Finset V) :
    Set.range (StdSimplex.map (R := ℝ) (fun i : σ => (i : V))) = closedFace σ := by
  classical
  ext μ
  rw [StdSimplex.mem_range_map_iff, mem_closedFace_iff_coordinate_eq_zero]
  simp

omit [Fintype V] in
theorem affineMapMk_map_subtype (p : V → E) (σ : Finset V) (μ : Simplex σ) :
    StdSimplex.affineMapMk (R := ℝ) p (μ.map (fun i : σ => (i : V))) =
      StdSimplex.affineMapMk (R := ℝ) (fun i : σ => p i) μ := by
  have h : (StdSimplex.affineMapMk (R := ℝ) p).comp
      (StdSimplex.affineMap (R := ℝ) (fun i : σ => (i : V))) =
        StdSimplex.affineMapMk (R := ℝ) (fun i : σ => p i) := by
    apply StdSimplex.affineMap_ext
    intro i
    simp
  exact congrArg (fun f => f μ) h

omit [Fintype V] in
theorem image_affineMapMk_closedFace (p : V → E) (σ : Finset V) :
    StdSimplex.affineMapMk (R := ℝ) p '' closedFace σ =
      convexHull ℝ (p '' (σ : Set V)) := by
  classical
  rw [← range_simplex_map_subtype, ← Set.range_comp]
  have h : (StdSimplex.affineMapMk (R := ℝ) p) ∘
      StdSimplex.map (R := ℝ) (fun i : σ => (i : V)) =
        StdSimplex.affineMapMk (R := ℝ) (fun i : σ => p i) := by
    funext μ
    exact affineMapMk_map_subtype p σ μ
  rw [h, ← Geometry.convexHull_range_eq_range_affineMapMk]
  congr 1
  ext x
  simp

omit [Fintype V] in
/-- Closed source faces map onto the convex hull of their placed vertices. -/
theorem image_affineSkeletonMap_face {d : ℕ} (p : V → E) (σ : Finset V)
    (hσ : σ.card ≤ d + 1) :
    affineSkeletonMap d p '' skeletonFace d σ =
      convexHull ℝ (p '' (σ : Set V)) := by
  rw [← range_faceToSkeleton hσ, ← Set.range_comp]
  have h : affineSkeletonMap d p ∘ faceToSkeleton hσ =
      (StdSimplex.affineMapMk (R := ℝ) p) ∘ (Subtype.val : closedFace σ → Simplex V) := rfl
  rw [h, Set.range_comp, Subtype.range_val, image_affineMapMk_closedFace]

@[simp] theorem facesAt_affineSkeletonMap (d : ℕ) (p : V → E) (r : E) :
    facesAt (affineSkeletonMap d p) r = BMN.hullFacesAt d p r := by
  classical
  ext σ
  rw [mem_facesAt, BMN.mem_hullFacesAt]
  by_cases hσ : σ.card = d + 1
  · simp only [hσ, true_and]
    rw [image_affineSkeletonMap_face p σ (by omega)]
  · simp [hσ]

@[simp] theorem overlapCount_affineSkeletonMap (d : ℕ) (p : V → E) (r : E) :
    overlapCount (affineSkeletonMap d p) r = BMN.hullCount d p r := by
  simp [overlapCount, BMN.hullCount]

/-- A uniform real bound on hull counts bounds the overlap of the affine map. -/
theorem overlap_affineSkeletonMap_le {d : ℕ} (p : V → E) {B : ℝ}
    (hB : ∀ r : E, (BMN.hullCount d p r : ℝ) ≤ B) :
    (overlap (affineSkeletonMap d p) : ℝ) ≤ B := by
  obtain ⟨r, hr⟩ := overlap_attained (affineSkeletonMap d p)
  rw [← hr, overlapCount_affineSkeletonMap]
  exact hB r

end SharpTopologicalOverlap
