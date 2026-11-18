module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # The vertex deletion bound in Theorem 1.2 -/

@[expose] public section

namespace SharpTopologicalOverlap

/-- The constant `C_d` in Theorem 1.2. The quotient `d / p` is natural-number division. -/
def deletionBound (d : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 1 d, (d + 1).choose (p + 1) * (d + 1 - p) * (d / p)

/-- The size assumption in Theorem 1.2 implies the simplex has enough vertices. -/
theorem add_one_le_deletionBound {d : ℕ} (hd : 2 ≤ d) : d + 1 ≤ deletionBound d := by
  have hc : d ≤ (d + 1).choose (1 + 1) := by
    simpa only [Nat.choose_succ_succ', Nat.choose_one_right] using
      (Nat.le_add_right d (d.choose 2))
  have hm : 1 ∈ Finset.Icc 1 d := by simp; omega
  have hs := Finset.single_le_sum
    (f := fun p => (d + 1).choose (p + 1) * (d + 1 - p) * (d / p))
    (fun p _ => Nat.zero_le _) hm
  have hcube : d * d * d ≤ deletionBound d := by
    calc
      d * d * d ≤ (d + 1).choose (1 + 1) * d * d :=
        Nat.mul_le_mul_right d (Nat.mul_le_mul_right d hc)
      _ ≤ deletionBound d := by simpa [deletionBound] using hs
  have hsq : d + 1 ≤ d * d := by nlinarith
  have hprod : d * d ≤ d * d * d := by nlinarith
  exact hsq.trans (hprod.trans hcube)

theorem add_one_lt_of_deletionBound_lt {d n : ℕ} (hd : 2 ≤ d)
    (hn : deletionBound d < n) : d + 1 < n :=
  (add_one_le_deletionBound hd).trans_lt hn

/-- In dimension one the deletion sum has a single term of value one. -/
theorem deletionBound_one : deletionBound 1 = 1 := by decide

/-- Above the deletion bound there are enough vertices for a top-dimensional face. -/
theorem add_one_le_of_deletionBound_lt {d n : ℕ} (hd : 0 < d)
    (hn : deletionBound d < n) : d + 1 ≤ n := by
  by_cases hd₂ : 2 ≤ d
  · exact Nat.le_of_lt (add_one_lt_of_deletionBound_lt hd₂ hn)
  · have h : d = 1 := by omega
    subst d
    rw [deletionBound_one] at hn
    omega

end SharpTopologicalOverlap
