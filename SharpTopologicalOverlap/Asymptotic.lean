module

public import SharpTopologicalOverlap.Overlap.Minimum
public import SharpTopologicalOverlap.Overlap.Lower
public import SharpTopologicalOverlap.BMN

/-! # Theorem 1.1, strengthened to include the affine constant

Both normalized finite minima converge to the sharp threshold. In particular,
their liminfs, the topological and affine overlap constants, coincide.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Filter
open scoped Topology

/-- The affine minimum satisfies the finite BMN upper bound. -/
theorem normalizedAffineMinimumOverlap_le_bmn_bound (d n : ℕ) :
    normalizedAffineMinimumOverlap d n ≤
      (((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
        (2 * d : ℝ) * ((n - 1).choose d : ℝ)) / (n.choose (d + 1) : ℝ) := by
  obtain ⟨p, hp⟩ := BMN.exists_affineSkeletonMap_overlap_bound d n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (show (affineMinimumOverlap d n : ℝ) ≤
    (overlap (affineSkeletonMap d p) : ℝ) by
      exact_mod_cast affineMinimumOverlap_le p).trans hp

/-- The finite lower theorem applies to the attained continuous minimum. -/
theorem normalized_finite_bound_le_minimum {d n : ℕ} (hd : 0 < d)
    (hn : deletionBound d < n) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) /
      (n.choose (d + 1) : ℝ) ≤ normalizedMinimumOverlap d n := by
  obtain ⟨f, hf⟩ := minimumOverlap_attained d n
  simpa only [normalizedMinimumOverlap, hf] using normalized_finite_overlap_bound hd hn f

/-- The normalized continuous minima have a limit, rather than only a liminf. -/
theorem tendsto_normalizedMinimumOverlap {d : ℕ} (hd : 0 < d) :
    Tendsto (normalizedMinimumOverlap d) atTop (𝓝 (overlapThreshold d)) := by
  apply (tendsto_normalized_finite_bound d).squeeze'
    (BMN.tendsto_normalized_bmn_bound d)
  · filter_upwards [eventually_gt_atTop (deletionBound d)] with n hn
    exact normalized_finite_bound_le_minimum hd hn
  · exact Eventually.of_forall fun n =>
      (normalizedMinimumOverlap_le_affine d n).trans
        (normalizedAffineMinimumOverlap_le_bmn_bound d n)

/-- The affine minima converge to the same sharp threshold. -/
theorem tendsto_normalizedAffineMinimumOverlap {d : ℕ} (hd : 0 < d) :
    Tendsto (normalizedAffineMinimumOverlap d) atTop (𝓝 (overlapThreshold d)) := by
  exact (tendsto_normalizedMinimumOverlap hd).squeeze'
    (BMN.tendsto_normalized_bmn_bound d)
    (Eventually.of_forall (normalizedMinimumOverlap_le_affine d))
    (Eventually.of_forall (normalizedAffineMinimumOverlap_le_bmn_bound d))

/-- Theorem 1.1 of the reference manuscript. -/
theorem topologicalOverlapConstant_eq_threshold {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = overlapThreshold d :=
  (tendsto_normalizedMinimumOverlap hd).liminf_eq

/-- The affine analogue of Theorem 1.1, with the same normalization. -/
theorem affineOverlapConstant_eq_threshold {d : ℕ} (hd : 0 < d) :
    affineOverlapConstant d = overlapThreshold d :=
  (tendsto_normalizedAffineMinimumOverlap hd).liminf_eq

/-- The strengthened Theorem 1.1, with the factorial normalization expanded. -/
theorem sharp_overlap_constants {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = affineOverlapConstant d ∧
      affineOverlapConstant d = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) := by
  constructor
  · rw [topologicalOverlapConstant_eq_threshold hd, affineOverlapConstant_eq_threshold hd]
  · exact affineOverlapConstant_eq_threshold hd

end SharpTopologicalOverlap
