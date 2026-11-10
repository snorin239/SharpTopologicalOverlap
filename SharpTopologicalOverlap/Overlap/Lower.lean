module

public import SharpTopologicalOverlap.Finite
public import SharpTopologicalOverlap.BMN.Normalization

/-! # Normalization and limit of the finite lower bound -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Filter
open scoped Topology

/-- The finite theorem, with the same binomial normalization as the constants. -/
theorem normalized_finite_overlap_bound {n d : ℕ} (hd : 2 ≤ d)
    (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) /
        (n.choose (d + 1) : ℝ) ≤
      (overlap f : ℝ) / (n.choose (d + 1) : ℝ) :=
  div_le_div_of_nonneg_right (finite_overlap_bound hd hn f) (Nat.cast_nonneg _)

/-- Normalizing the finite lower bound recovers the factorial threshold. -/
theorem tendsto_normalized_finite_bound (d : ℕ) :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) /
        (n.choose (d + 1) : ℝ)) atTop (𝓝 (overlapThreshold d)) := by
  have hratio : Tendsto (fun n : ℕ => 1 - (deletionBound d : ℝ) / (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (deletionBound d : ℝ))
  have hlim := (hratio.pow (d + 1)).mul (BMN.tendsto_normalized_leadingTerm d)
  simp only [one_pow, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hid : (1 - (deletionBound d : ℝ) / (n : ℝ)) *
      ((n : ℝ) / (d + 1 : ℝ)) =
      ((n : ℝ) - deletionBound d) / (d + 1 : ℝ) := by
    field_simp
  rw [← mul_div_assoc, ← mul_pow, hid]

end SharpTopologicalOverlap
