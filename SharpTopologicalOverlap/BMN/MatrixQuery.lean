module

public import SharpTopologicalOverlap.BMN.Configuration
public import SharpTopologicalOverlap.BMN.Determinant

/-! # Matrix hypotheses for the BMN interleaving argument -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

/-- The concrete geometry supplies these matrix properties for a separated
source simplex and a query in its closed convex hull. -/
structure MatrixQuery {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (v : Fin (d + 1) → ℝ) : Prop where
  one_le : ∀ i j, 1 ≤ M i j
  query_one_le : ∀ j, 1 ≤ v j
  source_gap : ∀ a b j, a < b → 0 < j → growth d (M a j) < M b j
  replacement_columns : ∀ k i i' j j', j < j' →
    (M.updateRow k v) i j < (M.updateRow k v) i' j'
  query_gap : ∀ i j, 0 < j → growth d (M i j) < v j ∨ growth d (v j) < M i j
  det_nonneg : ∀ k, 0 ≤ (M.updateRow k v).det

namespace MatrixQuery

variable {d : ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
  {v : Fin (d + 1) → ℝ} (h : MatrixQuery M v)

include h

theorem replacement_one_le (k i j : Fin (d + 1)) :
    1 ≤ (M.updateRow k v) i j := by
  by_cases hi : i = k
  · subst i
    simpa using h.query_one_le j
  · simpa [Matrix.updateRow, Function.update, hi] using h.one_le i j

theorem source_lt {a b j : Fin (d + 1)} (hab : a < b) (hj : 0 < j) :
    M a j < M b j :=
  (growth_self_le d (h.one_le a j)).trans_lt (h.source_gap a b j hab hj)

theorem source_mono {a b j : Fin (d + 1)} (hab : a ≤ b) (hj : 0 < j) :
    M a j ≤ M b j := by
  rcases hab.eq_or_lt with rfl | hlt
  · rfl
  · exact (h.source_lt hlt hj).le

theorem source_growth_mono {a b j : Fin (d + 1)} (hab : a ≤ b) (hj : 0 < j) :
    growth d (M a j) ≤ growth d (M b j) :=
  growth_monotone d (show 0 ≤ M a j from zero_le_one.trans (h.one_le a j))
    (show 0 ≤ M b j from zero_le_one.trans (h.one_le b j)) (h.source_mono hab hj)

theorem growth_source_lt_query {i j : Fin (d + 1)} (hj : 0 < j)
    (hij : M i j ≤ v j) : growth d (M i j) < v j := by
  rcases h.query_gap i j hj with hg | hg
  · exact hg
  · have hs := growth_self_le d (h.query_one_le j)
    linarith

theorem growth_query_lt_source {i j : Fin (d + 1)} (hj : 0 < j)
    (hij : v j ≤ M i j) : growth d (v j) < M i j := by
  rcases h.query_gap i j hj with hg | hg
  · have hs := growth_self_le d (h.one_le i j)
    linarith
  · exact hg

end MatrixQuery

end SharpTopologicalOverlap.BMN
