import SharpTopologicalOverlap

/-! Root-import-only statement and axiom audits for the strengthened Theorem 1.1.

Both constants use the manuscript's binomial normalization. The affine minimum
ranges over vertex placements and therefore includes all affine interpolations.
-/

noncomputable section

open SharpTopologicalOverlap

namespace Theorem11Verification

/-- The original manuscript statement, with the finite minimum expanded. -/
theorem manuscript_bound {d : ℕ} (hd : 0 < d) :
    Filter.liminf
      (fun n : ℕ =>
        ((sInf (Set.range
          (fun f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)) => overlap f)) : ℕ) : ℝ) /
          (n.choose (d + 1) : ℝ))
      Filter.atTop = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) := by
  change topologicalOverlapConstant d = overlapThreshold d
  exact topologicalOverlapConstant_eq_threshold hd

/-- The affine analogue, with its independent finite minimum expanded. -/
theorem affine_bound {d : ℕ} (hd : 0 < d) :
    Filter.liminf
      (fun n : ℕ =>
        ((sInf (Set.range
          (fun p : Fin n → EuclideanSpace ℝ (Fin d) =>
            overlap (affineSkeletonMap d p))) : ℕ) : ℝ) /
          (n.choose (d + 1) : ℝ))
      Filter.atTop = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) := by
  change affineOverlapConstant d = overlapThreshold d
  exact affineOverlapConstant_eq_threshold hd

/-- The strengthened Theorem 1.1 requested for the two independently defined constants. -/
theorem strengthened_bound {d : ℕ} (hd : 0 < d) :
    topologicalOverlapConstant d = affineOverlapConstant d ∧
      affineOverlapConstant d = ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) :=
  sharp_overlap_constants hd

/-- All initial terms without source top faces are harmless zero normalizations. -/
theorem normalized_empty_prefix (d n : ℕ) (hn : n < d + 1) :
    normalizedMinimumOverlap d n = 0 ∧ normalizedAffineMinimumOverlap d n = 0 := by
  simp [normalizedMinimumOverlap, normalizedAffineMinimumOverlap, Nat.choose_eq_zero_of_lt hn]

example : topologicalOverlapConstant 1 = (1 : ℝ) / 2 ∧
    affineOverlapConstant 1 = (1 : ℝ) / 2 := by
  have ht := topologicalOverlapConstant_eq_threshold (d := 1) (by decide)
  have ha := affineOverlapConstant_eq_threshold (d := 1) (by decide)
  norm_num [overlapThreshold] at ht ha
  exact ⟨ht, ha⟩

example : topologicalOverlapConstant 2 = (2 : ℝ) / 9 := by
  rw [topologicalOverlapConstant_eq_threshold (by decide)]
  norm_num [overlapThreshold]

example : affineOverlapConstant 2 = (2 : ℝ) / 9 := by
  rw [affineOverlapConstant_eq_threshold (by decide)]
  norm_num [overlapThreshold]

example : topologicalOverlapConstant 3 = (3 : ℝ) / 32 := by
  rw [topologicalOverlapConstant_eq_threshold (by decide)]
  norm_num [overlapThreshold]

example : affineOverlapConstant 3 = (3 : ℝ) / 32 := by
  rw [affineOverlapConstant_eq_threshold (by decide)]
  norm_num [overlapThreshold]

#print axioms minimumOverlap_attained
#print axioms affineMinimumOverlap_attained
#print axioms minimumOverlap_le_affineMinimumOverlap
#print axioms tendsto_normalizedMinimumOverlap
#print axioms tendsto_normalizedAffineMinimumOverlap
#print axioms topologicalOverlapConstant_eq_threshold
#print axioms affineOverlapConstant_eq_threshold
#print axioms sharp_overlap_constants
#print axioms manuscript_bound
#print axioms affine_bound
#print axioms strengthened_bound
#print axioms normalized_empty_prefix

end Theorem11Verification
