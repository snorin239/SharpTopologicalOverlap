module

public import SharpTopologicalOverlap.BMN.MatrixQuery

/-! # The upper interleaving inequalities -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN.MatrixQuery

open Finset Equiv

private theorem succ_value {d : ℕ} (j : Fin d) : (j.succ : ℕ) = j.val + 1 := rfl
private theorem castSucc_value {d : ℕ} (j : Fin d) : (j.castSucc : ℕ) = j.val := rfl
private theorem zero_value (d : ℕ) : ((0 : Fin (d + 1)) : ℕ) = 0 := rfl
attribute [local fin_omega] succ_value castSucc_value zero_value

theorem upper_bounds {d : ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {v : Fin (d + 1) → ℝ} (h : MatrixQuery M v) :
    ∀ j : Fin d, v j.succ < M j.succ j.succ := by
  classical
  by_contra hn
  push Not at hn
  let bad := Finset.univ.filter (fun j : Fin d => M j.succ j.succ ≤ v j.succ)
  have hbad : bad.Nonempty := by
    obtain ⟨j, hj⟩ := hn
    exact ⟨j, by simp [bad, hj]⟩
  obtain ⟨j, hj, hmax⟩ := bad.exists_max_image (fun j => j) hbad
  have hfail : M j.succ j.succ ≤ v j.succ := (Finset.mem_filter.mp hj).2
  have hlater : ∀ k : Fin d, j < k → v k.succ < M k.succ k.succ := by
    intro k hk
    by_contra hnk
    have hkbad : k ∈ bad := by simp [bad, le_of_not_gt hnk]
    exact (not_le_of_gt hk) (hmax k hkbad)
  let a := j.castSucc
  let b := j.succ
  let g := Equiv.swap a b
  let A := M.updateRow a v
  have hab : a ≠ b := ne_of_lt j.castSucc_lt_succ
  have hA (i c : Fin (d + 1)) (hi : i ≠ a) : A i c = M i c := by
    simp [A, Matrix.updateRow, Function.update, hi]
  have hAa (c : Fin (d + 1)) : A a c = v c := by simp [A]
  have hgap : growth d (M b b) < v b :=
    h.growth_source_lt_query (Fin.succ_pos j) hfail
  have hg : DominantPermutation A g := by
    apply dominantPermutation_of_lower_gap
    intro c
    refine Fin.cases (by simp) (fun k hc l hl => ?_) c
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · have hca : k.succ ≠ a := by
        intro heq
        have hv := congrArg Fin.val heq
        change k.val + 1 = j.val at hv
        change j.val < k.val at hjk
        omega
      have hcb : k.succ ≠ b := by
        intro heq
        have hv := congrArg Fin.val heq
        change k.val + 1 = j.val + 1 at hv
        exact (ne_of_lt hjk) (Fin.ext (by omega))
      have hgc : g k.succ = k.succ := Equiv.swap_apply_of_ne_of_ne hca hcb
      rw [hgc, hA _ _ hca]
      by_cases hga : g l = a
      · rw [hga, hAa]
        exact h.growth_query_lt_source hc (hlater k hjk).le
      · rw [hA _ _ hga]
        apply h.source_gap _ _ _ ?_ hc
        by_cases hla : l = a
        · rw [hla, show g a = b by simp [g]]
          dsimp [b]
          fin_omega
        by_cases hlb : l = b
        · rw [hlb, show g b = a by simp [g]]
          dsimp [a]
          fin_omega
        · rw [show g l = l from Equiv.swap_apply_of_ne_of_ne hla hlb]
          exact hl
    · have hgb : g j.succ = a := by simp [g, b]
      rw [hgb, hAa]
      have hlb : l ≠ b := ne_of_lt hl
      have hga : g l ≠ a := by
        intro heq
        have hsame : g l = g b := by simpa [g] using heq
        exact hlb (g.injective hsame)
      rw [hA _ _ hga]
      have hle : g l ≤ b := by
        by_cases hla : l = a
        · subst l
          simp [g]
        · rw [show g l = l from Equiv.swap_apply_of_ne_of_ne hla hlb]
          exact hl.le
      exact (h.source_growth_mono hle hc).trans_lt hgap
    · have hca : k.succ ≤ a := by
        change k.val + 1 ≤ j.val
        exact Nat.succ_le_of_lt hkj
      have hla : l ≠ a := by fin_omega
      have hlb : l ≠ b := ne_of_lt (hl.trans_le (hca.trans j.castSucc_lt_succ.le))
      have hgl : g l = l := Equiv.swap_apply_of_ne_of_ne hla hlb
      rw [hgl, hA _ _ hla]
      by_cases hceq : k.succ = a
      · rw [hceq, show g a = b by simp [g], hA _ _ hab.symm]
        apply h.source_gap _ _ _ ?_ (hceq ▸ hc)
        dsimp [a, b] at *
        fin_omega
      · have hcb : k.succ ≠ b := by
          intro heq
          have hv := congrArg Fin.val heq
          change k.val + 1 = j.val + 1 at hv
          exact (ne_of_lt hkj) (Fin.ext (by omega))
        have hgc : g k.succ = k.succ := Equiv.swap_apply_of_ne_of_ne hceq hcb
        rw [hgc, hA _ _ hceq]
        exact h.source_gap _ _ _ hl hc
  have hneg : A.det < 0 := det_neg_of_dominant_swap A hab
    (h.replacement_one_le a) (h.replacement_columns a) hg
  exact (not_lt_of_ge (h.det_nonneg a)) hneg

end SharpTopologicalOverlap.BMN.MatrixQuery
