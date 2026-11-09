module

public import SharpTopologicalOverlap.Geometry.TargetGeometry

/-! # Arbitrarily fine mesh of the actual physical target carriers -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.TargetGeometry

open AbstractSimplicialComplex Set

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sphere_face_card_le (d : ℕ) (σ : Finset (Fin (d + 2))) (hσ : σ ∈ sphere d) :
    σ.card ≤ d + 1 := by
  have hproper := (AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mp hσ).2
  have hcard := Finset.card_lt_card hproper
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Choose one genuine target subdivision whose physical carriers all have
small diameter, including the filtered carriers of outer cone cells. -/
theorem exists_targetCells_mesh_lt (D : Affine.Simplex ℝ E d) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ σ ∈ (barycentricModel (sphere d) j).complex,
      ∀ x ∈ targetCells D (barycentricModel (sphere d) j) σ,
      ∀ y ∈ targetCells D (barycentricModel (sphere d) j) σ, dist x y < ε := by
  obtain ⟨j, hj⟩ := exists_barycentric_hull_image_mesh_lt (sphere d) d
    (sphere_face_card_le d) (fun μ => affineMap D μ.1) (continuous_targetMap D) hε
  refine ⟨j, fun σ hσ x hx y hy => ?_⟩
  exact hj σ hσ x (targetCells_subset_full_hull D _ σ hx) y
    (targetCells_subset_full_hull D _ σ hy)

end SharpTopologicalOverlap.Geometry.TargetGeometry
