module

public import SharpTopologicalOverlap.BMN.MatrixQuery

/-! # The lower interleaving inequalities in the BMN type lemma -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN.MatrixQuery

open Equiv

variable {d : ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
  {v : Fin (d + 1) → ℝ} (h : MatrixQuery M v)

include h

private theorem lower_failure_dominant
    (hupper : ∀ j : Fin d, v j.succ < M j.succ j.succ)
    (j : Fin d) (hbad : v j.succ ≤ M j.castSucc j.succ)
    (hprev : ∀ k : Fin d, k < j → M k.castSucc k.succ < v k.succ) :
    DominantPermutation (M.updateRow j.succ v) (swap j.castSucc j.succ) := by
  classical
  let a := j.castSucc
  let b := j.succ
  have hab : a ≠ b := ne_of_lt j.castSucc_lt_succ
  apply dominantPermutation_of_lower_gap
  intro c hc l hlc
  by_cases hca : c = a
  · subst c
    have hla : l ≠ a := ne_of_lt hlc
    have hlb : l ≠ b := ne_of_lt (hlc.trans j.castSucc_lt_succ)
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero (ne_of_gt hc)
    have hkval : k.val + 1 = j.val := congrArg Fin.val hk
    have hkj : k < j := by
      change k.val < j.val
      omega
    have hlk : l ≤ k.castSucc := by
      change l.val ≤ k.val
      have hlval : l.val < j.val := hlc
      omega
    have hlow : M l a ≤ v a :=
      (h.source_mono hlk hc).trans (by simpa [hk] using (hprev k hkj).le)
    have hg := h.growth_source_lt_query hc hlow
    simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hla, hlb, hab, hab.symm] using hg
  · by_cases hcb : c = b
    · subst c
      have hlb : l ≠ b := ne_of_lt hlc
      by_cases hla : l = a
      · subst l
        have hg := h.growth_query_lt_source hc hbad
        simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hab, hab.symm] using hg
      · have hla' : l < a := by
          have hlval : l.val < j.val + 1 := hlc
          have hlne : l.val ≠ j.val := fun heq => hla (Fin.ext heq)
          change l.val < j.val
          omega
        have hg := h.source_gap l a b hla' hc
        simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hla, hlb, hab, hab.symm] using hg
    · by_cases hla : l = a
      · subst l
        obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero (ne_of_gt hc)
        have hvc : v c ≤ M c c := by simpa [hk] using (hupper k).le
        have hg := h.growth_query_lt_source hc hvc
        simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hca, hcb, hab, hab.symm] using hg
      · by_cases hlb : l = b
        · subst l
          have hac : a < c := j.castSucc_lt_succ.trans hlc
          have hg := h.source_gap a c c hac hc
          simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hca, hcb, hab, hab.symm] using hg
        · have hg := h.source_gap l c c hlc hc
          simpa [a, b, swap_apply_def, Matrix.updateRow_apply, hca, hcb, hla, hlb] using hg

/-- Once all upper bounds hold, a minimal failing lower bound would give a
negative determinant for a closed-hull replacement matrix. -/
theorem lower_bounds
    (hupper : ∀ j : Fin d, v j.succ < M j.succ j.succ) :
    ∀ j : Fin d, M j.castSucc j.succ < v j.succ := by
  classical
  by_contra hnot
  push Not at hnot
  let s := Finset.univ.filter (fun j : Fin d => v j.succ ≤ M j.castSucc j.succ)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hnot
    exact ⟨j, by simpa [s] using hj⟩
  let j := s.min' hs
  have hjmem : j ∈ s := Finset.min'_mem _ _
  have hbad : v j.succ ≤ M j.castSucc j.succ := (Finset.mem_filter.mp hjmem).2
  have hprev : ∀ k : Fin d, k < j → M k.castSucc k.succ < v k.succ := by
    intro k hkj
    by_contra hk
    have hkmem : k ∈ s := by simp [s, le_of_not_gt hk]
    have := Finset.min'_le s k hkmem
    exact (not_le_of_gt hkj) this
  have hdom := lower_failure_dominant h hupper j hbad hprev
  have hneg := det_neg_of_dominant_swap (M.updateRow j.succ v)
    (ne_of_lt j.castSucc_lt_succ) (h.replacement_one_le j.succ)
    (h.replacement_columns j.succ) hdom
  exact (not_lt_of_ge (h.det_nonneg j.succ)) hneg

end SharpTopologicalOverlap.BMN.MatrixQuery
