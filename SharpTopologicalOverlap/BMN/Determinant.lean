module

public import SharpTopologicalOverlap.BMN.Basic

/-! # Determinants with one quantitatively dominant permutation -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open scoped BigOperators
open Finset Equiv

/-- The positive product occurring in a determinant term. -/
def permutationProduct {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (g : Equiv.Perm (Fin m)) : ℝ := ∏ j, A (g j) j

private theorem exists_last_difference {m : ℕ} (g t : Equiv.Perm (Fin (m + 1)))
    (hne : t ≠ g) :
    ∃ j : Fin (m + 1), 0 < j ∧ t j ≠ g j ∧ ∀ k, j < k → t k = g k := by
  classical
  have hex : ∃ j, t j ≠ g j := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  let s := Finset.univ.filter (fun j => t j ≠ g j)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, by simp [s, hj]⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun j => j) hs
  have hjne : t j ≠ g j := (Finset.mem_filter.mp hj).2
  have hlast : ∀ k, j < k → t k = g k := by
    intro k hk
    by_contra h
    exact (not_le_of_gt hk) (hmax k (by simp [s, h]))
  have hjpos : 0 < j := by
    by_contra h
    have hjzero : j = 0 := le_antisymm (le_of_not_gt h) (Fin.zero_le _)
    let k := g.symm (t j)
    have hkne : k ≠ j := by
      intro hkj
      exact hjne (by simpa [k] using congrArg g hkj)
    have hkpos : j < k := by
      rw [hjzero]
      exact Fin.pos_iff_ne_zero.mpr (by simpa [hjzero] using hkne)
    have heq : t k = t j := (hlast k hkpos).trans (g.apply_symm_apply (t j))
    exact hkne (t.injective heq)
  exact ⟨j, hjpos, hjne, hlast⟩

/-- A candidate permutation selects a strongly larger entry than every
available alternative, processing the columns from right to left. -/
def DominantPermutation {d : ℕ} (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (g : Equiv.Perm (Fin (d + 1))) : Prop :=
  ∀ j, 0 < j → ∀ i, i ≠ g j →
    (∀ k, j < k → i ≠ g k) → growth d (A i j) < A (g j) j

/-- It suffices to compare the chosen row with rows chosen in earlier columns. -/
theorem dominantPermutation_of_lower_gap {d : ℕ}
    {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {g : Equiv.Perm (Fin (d + 1))}
    (h : ∀ j, 0 < j → ∀ l, l < j → growth d (A (g l) j) < A (g j) j) :
    DominantPermutation A g := by
  intro j hj i hij hi
  have hle : g.symm i ≤ j := by
    by_contra hn
    exact hi (g.symm i) (lt_of_not_ge hn) (g.apply_symm_apply i).symm
  have hne : g.symm i ≠ j := by
    intro heq
    exact hij (by simpa using congrArg g heq)
  simpa using h j hj (g.symm i) (lt_of_le_of_ne hle hne)

/-- Quantitative separation makes a supplied permutation product dominate
every competing product. -/
theorem permutationProduct_dominates {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (g : Equiv.Perm (Fin (d + 1)))
    (hone : ∀ i j, 1 ≤ A i j)
    (hcol : ∀ i i' j j', j < j' → A i j < A i' j')
    (hg : DominantPermutation A g) (t : Equiv.Perm (Fin (d + 1))) (ht : t ≠ g) :
    ((d + 1).factorial : ℝ) * permutationProduct A t < permutationProduct A g := by
  classical
  obtain ⟨j, hjpos, hjne, hlast⟩ := exists_last_difference g t ht
  let L := Finset.univ.filter (fun k : Fin (d + 1) => k ≤ j)
  let H := Finset.univ.filter (fun k : Fin (d + 1) => ¬ k ≤ j)
  let a := A (t j) j
  have ha : 1 ≤ a := hone _ _
  have hgap : ((d + 1).factorial : ℝ) * a ^ (d + 1) < A (g j) j := by
    apply hg j hjpos (t j) hjne
    intro k hk heq
    exact (ne_of_lt hk) (t.injective ((hlast k hk).trans heq.symm)).symm
  have hlow : (∏ k ∈ L, A (t k) k) ≤ a ^ (d + 1) := by
    calc
      (∏ k ∈ L, A (t k) k) ≤ ∏ k ∈ L, a :=
        Finset.prod_le_prod₀ (fun k _ => (hone _ _).trans' zero_le_one) (by
          intro k hk
          have hkj : k ≤ j := (Finset.mem_filter.mp hk).2
          rcases lt_or_eq_of_le hkj with h | rfl
          · exact (hcol _ _ _ _ h).le
          · exact le_rfl)
      _ = a ^ L.card := by simp
      _ ≤ a ^ (d + 1) := by
        apply pow_le_pow_right₀ ha
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hselected : A (g j) j ≤ ∏ k ∈ L, A (g k) k := by
    have hjL : j ∈ L := by simp [L]
    calc
      A (g j) j = ∏ k ∈ ({j} : Finset (Fin (d + 1))), A (g k) k := by simp
      _ ≤ ∏ k ∈ L, A (g k) k :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (by simpa using hjL)
          (by intro k hk; exact (hone _ _).trans' zero_le_one)
          (by intro k hk _; exact hone _ _)
  have hsmall : ((d + 1).factorial : ℝ) * (∏ k ∈ L, A (t k) k) <
      ∏ k ∈ L, A (g k) k :=
    (mul_le_mul_of_nonneg_left hlow (by positivity)).trans_lt (hgap.trans_le hselected)
  have hhigh : (∏ k ∈ H, A (t k) k) = ∏ k ∈ H, A (g k) k := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hlast k (lt_of_not_ge (Finset.mem_filter.mp hk).2)]
  have hhighpos : 0 < ∏ k ∈ H, A (g k) k :=
    Finset.prod_pos (fun k _ => zero_lt_one.trans_le (hone _ _))
  have hsplit (v : Equiv.Perm (Fin (d + 1))) :
      permutationProduct A v = (∏ k ∈ L, A (v k) k) * ∏ k ∈ H, A (v k) k := by
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  rw [hsplit t, hsplit g, hhigh, ← mul_assoc]
  exact mul_lt_mul_of_pos_right hsmall hhighpos

private theorem abs_real_sign {m : ℕ} (g : Equiv.Perm (Fin m)) :
    |((Equiv.Perm.sign g : ℤ) : ℝ)| = 1 := by
  exact_mod_cast Equiv.Perm.sign_abs g

private theorem real_sign_mul_self {m : ℕ} (g : Equiv.Perm (Fin m)) :
    ((Equiv.Perm.sign g : ℤ) : ℝ) * ((Equiv.Perm.sign g : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [h]

/-- The determinant has the sign of its quantitatively dominant permutation. -/
theorem det_sign_of_dominantPermutation {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (g : Equiv.Perm (Fin (d + 1)))
    (hone : ∀ i j, 1 ≤ A i j)
    (hcol : ∀ i i' j j', j < j' → A i j < A i' j')
    (hg : DominantPermutation A g) :
    0 < ((Equiv.Perm.sign g : ℤ) : ℝ) * A.det := by
  classical
  let P := permutationProduct A
  let K : ℝ := (d + 1).factorial
  let s := (Finset.univ : Finset (Equiv.Perm (Fin (d + 1)))).erase g
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P g := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hone _ _))
  have hcomp : ∀ t ∈ s, P t ≤ P g / K := by
    intro t ht
    apply (le_div_iff₀ hK).mpr
    have h := permutationProduct_dominates A g hone hcol hg t (Finset.mem_erase.mp ht).1
    exact (by simpa [P, K, mul_comm] using h.le)
  have hcard : (s.card : ℝ) < K := by
    have hc : s.card < Fintype.card (Equiv.Perm (Fin (d + 1))) :=
      Finset.card_erase_lt_of_mem (Finset.mem_univ g)
    simpa [K, Fintype.card_perm] using (Nat.cast_lt (α := ℝ)).mpr hc
  have hsum : (∑ t ∈ s, P t) < P g := by
    calc
      (∑ t ∈ s, P t) ≤ ∑ _t ∈ s, P g / K := Finset.sum_le_sum hcomp
      _ = (s.card : ℝ) * (P g / K) := by simp
      _ < K * (P g / K) := mul_lt_mul_of_pos_right hcard (div_pos hP hK)
      _ = P g := by field_simp
  let R : ℝ := ∑ t ∈ s,
    ((Equiv.Perm.sign g : ℤ) : ℝ) * ((Equiv.Perm.sign t : ℤ) : ℝ) * P t
  have hR : |R| < P g := by
    calc
      |R| ≤ ∑ t ∈ s, |((Equiv.Perm.sign g : ℤ) : ℝ) *
          ((Equiv.Perm.sign t : ℤ) : ℝ) * P t| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t ∈ s, P t := by
        apply Finset.sum_congr rfl
        intro t _
        rw [abs_mul, abs_mul, abs_real_sign, abs_real_sign, one_mul, one_mul]
        exact abs_of_pos (Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hone _ _)))
      _ < P g := hsum
  have hdet : ((Equiv.Perm.sign g : ℤ) : ℝ) * A.det = P g + R := by
    rw [Matrix.det_apply', Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ g)]
    simp only [← mul_assoc, real_sign_mul_self, one_mul]
    rfl
  rw [hdet]
  have := (abs_lt.mp hR).1
  linarith

theorem det_pos_of_dominant_identity {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hone : ∀ i j, 1 ≤ A i j)
    (hcol : ∀ i i' j j', j < j' → A i j < A i' j')
    (hg : DominantPermutation A (Equiv.refl _)) : 0 < A.det := by
  simpa using det_sign_of_dominantPermutation A (Equiv.refl _) hone hcol hg

theorem det_neg_of_dominant_swap {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (hone : ∀ i j, 1 ≤ A i j)
    (hcol : ∀ i i' j j', j < j' → A i j < A i' j')
    (hg : DominantPermutation A (Equiv.swap a b)) : A.det < 0 := by
  have h := det_sign_of_dominantPermutation A (Equiv.swap a b) hone hcol hg
  simpa [Equiv.Perm.sign_swap hab] using h

end SharpTopologicalOverlap.BMN
