module

public import SharpTopologicalOverlap.BMN.Basic

/-! # An explicit coordinate-separated configuration -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

theorem growth_nonneg (d : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ growth d x := by
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

theorem growth_self_le (d : ℕ) {x : ℝ} (hx : 1 ≤ x) : x ≤ growth d x := by
  have hpow : x ≤ x ^ (d + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hx (show 1 ≤ d + 1 by omega)
  have hfac : (1 : ℝ) ≤ ((d + 1).factorial : ℝ) := by
    exact_mod_cast (d + 1).factorial_pos
  exact hpow.trans (le_mul_of_one_le_left (pow_nonneg (by linarith : 0 ≤ x) _) hfac)

theorem growth_monotone (d : ℕ) : MonotoneOn (growth d) (Set.Ici 0) := by
  intro x hx y _ hxy
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (Nat.cast_nonneg _)

theorem growth_four_sq_lt {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx : 1 < x) :
    4 * x ^ 2 < growth d x := by
  have hfac : (6 : ℝ) ≤ ((d + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_le (show 3 ≤ d + 1 by omega))
  have hpow : x ^ 2 ≤ x ^ (d + 1) :=
    pow_le_pow_right₀ hx.le (by omega)
  have hx2 : 0 < x ^ 2 := pow_pos (by linarith) _
  unfold growth
  nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 6)]

theorem growth_two_mul_lt {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx : 1 < x) :
    2 * x < growth d x := by
  have h := growth_four_sq_lt hd hx
  nlinarith

/-- A concrete sequence with each term separated from every earlier term. -/
def rapidSequence (d : ℕ) : ℕ → ℝ
  | 0 => 2
  | k + 1 => growth d (rapidSequence d k) + 1

@[simp] theorem rapidSequence_zero (d : ℕ) : rapidSequence d 0 = 2 := rfl

@[simp] theorem rapidSequence_succ (d k : ℕ) :
    rapidSequence d (k + 1) = growth d (rapidSequence d k) + 1 := rfl

theorem one_lt_rapidSequence (d k : ℕ) : 1 < rapidSequence d k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [rapidSequence_succ]
    have h := growth_self_le d ih.le
    linarith

theorem strictMono_rapidSequence (d : ℕ) : StrictMono (rapidSequence d) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [rapidSequence_succ]
  have h := growth_self_le d (one_lt_rapidSequence d k).le
  linarith

theorem growth_rapidSequence_lt {d k l : ℕ} (hkl : k < l) :
    growth d (rapidSequence d k) < rapidSequence d l := by
  have h := (strictMono_rapidSequence d).monotone (Nat.succ_le_of_lt hkl)
  rw [rapidSequence_succ] at h
  linarith

/-- Coordinates are flattened with the coordinate index first. -/
def configuration (d n : ℕ) (i : Fin n) (j : Fin d) : ℝ :=
  rapidSequence d (j.val * n + i.val)

theorem configuration_separated (d n : ℕ) : Separated (configuration d n) where
  one_lt i j := one_lt_rapidSequence _ _
  gap i i' j j' h := by
    apply growth_rapidSequence_lt
    rcases h with hj | ⟨rfl, hi⟩
    · have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
      have hi := i.isLt
      dsimp at hmul hi ⊢
      rw [Nat.succ_mul] at hmul
      omega
    · exact Nat.add_lt_add_left hi _

theorem exists_separated (d n : ℕ) :
    ∃ p : Fin n → Fin d → ℝ, Separated p :=
  ⟨configuration d n, configuration_separated d n⟩

theorem Separated.lt_of_lex {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) {i i' : Fin n} {j j' : Fin d}
    (h : j < j' ∨ (j = j' ∧ i < i')) : p i j < p i' j' :=
  (growth_self_le d (hp.one_lt i j).le).trans_lt (hp.gap i i' j j' h)

theorem Separated.coordinate_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) {i i' : Fin n} (h : i < i') (j : Fin d) :
    p i j < p i' j := hp.lt_of_lex (Or.inr ⟨rfl, h⟩)

theorem Separated.coordinate_mono {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) {i i' : Fin n} (h : i ≤ i') (j : Fin d) :
    p i j ≤ p i' j := by
  rcases h.eq_or_lt with rfl | hlt
  · rfl
  · exact (hp.coordinate_lt hlt j).le

theorem Separated.cross_coordinate_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) (i i' : Fin n) {j j' : Fin d} (h : j < j') :
    p i j < p i' j' := hp.lt_of_lex (Or.inl h)

end SharpTopologicalOverlap.BMN
