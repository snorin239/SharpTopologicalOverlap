module

public import SharpTopologicalOverlap.Overlap

/-! # Constant maps and degenerate dimensions

A constant map counts every source face separately. These formulas also cover
an empty vertex type and degrees above the available number of vertices.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

variable {V Y : Type*} [Fintype V] [TopologicalSpace Y] {d : ℕ}

/-- At the value of a constant map, all source faces are counted. -/
theorem facesAt_const (y : Y) :
    facesAt (ContinuousMap.const (Skeleton V d) y) y =
      Finset.univ.powersetCard (d + 1) := by
  classical
  ext σ
  rw [mem_facesAt]
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · exact And.left
  · intro hσ
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < σ.card by omega)
    refine ⟨hσ, ⟨⟨vertex i, by simp⟩, ?_, rfl⟩⟩
    simpa using hi

theorem overlapCount_const (y : Y) :
    overlapCount (ContinuousMap.const (Skeleton V d) y) y =
      (Fintype.card V).choose (d + 1) := by
  classical
  simp [overlapCount, facesAt_const]

/-- Coincident images do not collapse the number of source faces. -/
theorem overlap_const (y : Y) :
    overlap (ContinuousMap.const (Skeleton V d) y) =
      (Fintype.card V).choose (d + 1) := by
  let : Nonempty Y := ⟨y⟩
  apply le_antisymm (overlap_le_choose _)
  simpa only [overlapCount_const] using
    (overlapCount_le_overlap (ContinuousMap.const (Skeleton V d) y) y)

/-- There are no source `d`-faces when fewer than `d + 1` vertices are available. -/
theorem overlap_eq_zero_of_card_lt [Nonempty Y] (f : C(Skeleton V d, Y))
    (h : Fintype.card V < d + 1) : overlap f = 0 := by
  have hb := overlap_le_choose f
  rw [Nat.choose_eq_zero_of_lt h] at hb
  exact Nat.eq_zero_of_le_zero hb

end SharpTopologicalOverlap
