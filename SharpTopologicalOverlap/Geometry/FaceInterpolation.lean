module

public import SharpTopologicalOverlap.Geometry.Placements
public import SharpTopologicalOverlap.Skeleton
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-! # Exact images of interpolated faces

These identities keep the source indices fixed while passing from a local
convex-hull intersection to an image of an original closed source face.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open AbstractSimplicialComplex Set

variable {Q E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem interpolate_faceInclusion (K : AbstractSimplicialComplex Q) (y : Q → E)
    (σ : TauCeti.SetLike.Face K) (x : StandardSimplex σ.1) :
    interpolate K y (faceInclusion K σ x) = ∑ q : σ.1, x.1 q • y q := by
  classical
  rw [interpolate, faceInclusion_val]
  change (∑ q ∈ x.1.support, x.1 q • y q) = ∑ q : σ.1, x.1 q • y q
  rw [Finset.sum_coe_sort σ.1 (fun q => x.1 q • y q)]
  apply Finset.sum_subset (StandardSimplex.support_subset x)
  intro q _ hq
  simp [Finsupp.notMem_support_iff.mp hq]

/-- An interpolated closed face has exactly the convex hull of its placed
vertices as image, including repeated image vertices. -/
theorem image_interpolate_faceInclusion (K : AbstractSimplicialComplex Q) (y : Q → E)
    (σ : TauCeti.SetLike.Face K) :
    interpolate K y '' Set.range (faceInclusion K σ) =
      convexHull ℝ (y '' (σ.1 : Set Q)) := by
  rw [← Set.range_comp]
  have heq : interpolate K y ∘ faceInclusion K σ =
      fun x : StandardSimplex σ.1 =>
        Fintype.linearCombination ℝ (fun q : σ.1 => y q) (fun q => x.1 q) := by
    funext x
    simpa only [Function.comp_apply, Fintype.linearCombination_apply] using
      interpolate_faceInclusion K y σ x
  rw [heq, Finset.range_linearCombination_standardSimplex]
  congr 1
  ext z
  simp

/-- A local hull witness comes from the original closed source face whenever
the source subdivision homeomorphism carries that whole child into the face. -/
theorem hull_subset_original_face_image {V : Type*} {d : ℕ}
    (K : AbstractSimplicialComplex Q) (y : Q → E)
    (e : K.Realization ≃ₜ Skeleton V d) (σ : Finset V)
    (u : TauCeti.SetLike.Face K)
    (hcarrier : ∀ x ∈ Set.range (faceInclusion K u), e x ∈ skeletonFace d σ) :
    convexHull ℝ (y '' (u.1 : Set Q)) ⊆
      (interpolate K y ∘ e.symm) '' skeletonFace d σ := by
  rw [← image_interpolate_faceInclusion K y u]
  rintro z ⟨x, hx, rfl⟩
  refine ⟨e x, hcarrier x hx, ?_⟩
  simp

end SharpTopologicalOverlap.Geometry
