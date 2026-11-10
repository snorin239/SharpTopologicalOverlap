module

public import SharpTopologicalOverlap.Polynomial.Threshold
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic

/-! # The factorial conversion from BMN counts to normalized overlap -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open Filter
open scoped Topology BigOperators

/-- The discarded-face error has an exact binomial normalization. -/
theorem normalized_error_eq {d n : ℕ} (hn : d + 1 ≤ n) :
    ((2 * d : ℝ) * ((n - 1).choose d : ℝ)) / (n.choose (d + 1) : ℝ) =
      (2 * d * (d + 1) : ℝ) / (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hpred : n - 1 + 1 = n := by omega
  have hnat := Nat.add_one_mul_choose_eq (n - 1) d
  rw [hpred] at hnat
  have hid : (n : ℝ) * ((n - 1).choose d : ℝ) =
      (n.choose (d + 1) : ℝ) * (d + 1 : ℝ) := by exact_mod_cast hnat
  have hc0 : (n.choose (d + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  apply (div_eq_div_iff hc0 hn0).mpr
  calc
    (2 * d : ℝ) * ((n - 1).choose d : ℝ) * (n : ℝ) =
        (2 * d : ℝ) * ((n : ℝ) * ((n - 1).choose d : ℝ)) := by ring
    _ = (2 * d : ℝ) * ((n.choose (d + 1) : ℝ) * (d + 1 : ℝ)) := by rw [hid]
    _ = (2 * d * (d + 1) : ℝ) * (n.choose (d + 1) : ℝ) := by ring

private theorem choose_div_pow_eq_prod {k n : ℕ} (hkn : k ≤ n) (hn : n ≠ 0) :
    (n.choose k : ℝ) / (n : ℝ) ^ k =
      (∏ i ∈ Finset.range k, (1 - (i : ℝ) / (n : ℝ))) / (k.factorial : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hdesc : (k.factorial : ℝ) * (n.choose k : ℝ) =
      ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) := by
    calc
      (k.factorial : ℝ) * (n.choose k : ℝ) = (n.descFactorial k : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose n k).symm
      _ = ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℝ) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      _ = ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)
  have hprod : (∏ i ∈ Finset.range k, (1 - (i : ℝ) / (n : ℝ))) =
      (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) / (n : ℝ) ^ k := by
    calc
      (∏ i ∈ Finset.range k, (1 - (i : ℝ) / (n : ℝ))) =
          ∏ i ∈ Finset.range k, (((n : ℝ) - (i : ℝ)) / (n : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        field_simp
      _ = (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) /
          (∏ _i ∈ Finset.range k, (n : ℝ)) := Finset.prod_div_distrib _ _
      _ = (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) / (n : ℝ) ^ k := by simp
  rw [hprod, ← hdesc]
  field_simp

/-- Fixed-degree binomial coefficients differ from powers by the factorial. -/
theorem tendsto_choose_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 ((k.factorial : ℝ)⁻¹)) := by
  have hfactor (i : ℕ) :
      Tendsto (fun n : ℕ => 1 - (i : ℝ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
  have hprod : Tendsto
      (fun n : ℕ => ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (n : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_finsetProd (Finset.range k) (fun i _ => hfactor i)
  have hlim := hprod.div_const (k.factorial : ℝ)
  simp only [one_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1] with n hkn hn
  exact (choose_div_pow_eq_prod hkn (by omega)).symm

theorem tendsto_normalized_leadingTerm (d : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) /
      (n.choose (d + 1) : ℝ)) atTop (𝓝 (overlapThreshold d)) := by
  have hc : ((d + 1).factorial : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hlim := (tendsto_const_nhds (x := (1 : ℝ) / (d + 1 : ℝ) ^ (d + 1))).div
    (tendsto_choose_div_pow (d + 1)) hc
  convert hlim using 1
  · funext n
    change ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) / (n.choose (d + 1) : ℝ) =
      ((1 : ℝ) / (d + 1 : ℝ) ^ (d + 1)) /
        ((n.choose (d + 1) : ℝ) / (n : ℝ) ^ (d + 1))
    rw [div_pow, div_div_eq_mul_div]
    ring
  · simp [overlapThreshold, div_eq_mul_inv, mul_comm]

/-- The finite BMN numerical bound tends to the manuscript's normalization. -/
theorem tendsto_normalized_bmn_bound (d : ℕ) :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
        (2 * d : ℝ) * ((n - 1).choose d : ℝ)) / (n.choose (d + 1) : ℝ))
      atTop (𝓝 (overlapThreshold d)) := by
  have hlim := (tendsto_normalized_leadingTerm d).add
    (tendsto_const_div_atTop_nhds_zero_nat (2 * d * (d + 1) : ℝ))
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (d + 1)] with n hn
  rw [add_div, normalized_error_eq hn]

end SharpTopologicalOverlap.BMN
