module

public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Thickening

/-! # Enclosing a compact set in the interior of a simplex

Appendix A, Step 2 needs a full-dimensional target simplex containing a compact
neighborhood of the first approximation. Scale a reference affine basis whose
hull contains the origin in its interior.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Module Metric
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every compact set lies in the interior of the hull of a full affine basis. -/
theorem exists_enclosing_affineBasis {K : Set E} (hK : IsCompact K) :
    ∃ b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E,
      K ⊆ interior (convexHull ℝ (range b)) := by
  obtain ⟨b, hb, _⟩ := exists_mem_interior_convexHull_affineBasis
    (s := Set.univ) (x := (0 : E)) Filter.univ_mem
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : E) hb
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : E)
  let t := R / r
  have ht : 0 < t := div_pos hR hr
  have htr : t * r = R := div_mul_cancel₀ R hr.ne'
  let b' : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := Units.mk0 t ht.ne' • b
  refine ⟨b', fun x hx => ?_⟩
  have hxR : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hKR hx
  have hxsmall : t⁻¹ • x ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    rw [← div_eq_inv_mul]
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  have hmem : x ∈ t • interior (convexHull ℝ (range b)) := by
    exact ⟨t⁻¹ • x, hball hxsmall, by simp [smul_smul, ht.ne']⟩
  simpa [b', Pi.smul_def, Set.range_smul, convexHull_smul,
    interior_smul₀ ht.ne'] using hmem

/-- The target simplex in the exact Euclidean dimension used by the paper. -/
theorem exists_enclosing_simplex {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) :
    ∃ s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d,
      K ⊆ interior (convexHull ℝ (range s.points)) := by
  have hex := exists_enclosing_affineBasis hK
  rw [finrank_euclideanSpace_fin] at hex
  obtain ⟨b, hb⟩ := hex
  exact ⟨⟨b, b.ind⟩, hb⟩

/-- A compact set's closed metric neighborhood also lies inside a target
simplex, as required before the second perturbation in Appendix A. -/
theorem exists_enclosing_simplex_cthickening {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (r : ℝ) :
    ∃ s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d,
      cthickening r K ⊆ interior (convexHull ℝ (range s.points)) :=
  exists_enclosing_simplex hK.cthickening

end SharpTopologicalOverlap.Geometry
