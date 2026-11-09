import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! # The vertex deletion bound in Theorem 1.2 -/

namespace SharpTopologicalOverlap

/-- The constant `C_d` in Theorem 1.2. The quotient `d / p` is natural-number division. -/
def deletionBound (d : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 1 d, (d + 1).choose (p + 1) * (d + 1 - p) * (d / p)

end SharpTopologicalOverlap
