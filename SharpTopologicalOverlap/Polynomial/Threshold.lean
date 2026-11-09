module

public import SharpTopologicalOverlap.Polynomial

/-! # The overlap threshold -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

/-- The sharp threshold `θ` in Lemma 4.1 and Theorem 5.1. -/
def overlapThreshold (d : ℕ) : ℝ :=
  ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1)

theorem overlapThreshold_pos (d : ℕ) : 0 < overlapThreshold d := by
  exact div_pos (Nat.cast_pos.mpr (d + 1).factorial_pos) (pow_pos (by positivity) _)

theorem overlapThreshold_ne_zero (d : ℕ) : overlapThreshold d ≠ 0 :=
  ne_of_gt (overlapThreshold_pos d)

end SharpTopologicalOverlap
