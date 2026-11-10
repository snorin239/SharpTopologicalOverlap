module

public import SharpTopologicalOverlap.BMN.Configuration

/-! # Query bounds and deletion of coordinate neighbors -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open scoped BigOperators

/-- The query belongs to the coordinate box spanned by the source points. -/
def WithinBounds {d n : ℕ} (p : Fin n → Fin d → ℝ) (r : Fin d → ℝ) : Prop :=
  ∀ j, (∃ i, p i j ≤ r j) ∧ (∃ i, r j ≤ p i j)

theorem withinBounds_of_mem_convexHull {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ} {s : Set (Fin n)}
    (hr : r ∈ convexHull ℝ (p '' s)) : WithinBounds p r := by
  classical
  intro j
  constructor
  · by_contra h
    push Not at h
    have hs : convexHull ℝ (p '' s) ⊆ {z | r j < z j} := by
      apply convexHull_min
      · rintro _ ⟨i, _, rfl⟩
        exact h i
      · exact convex_halfSpace_gt (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (r j)
    exact (lt_irrefl (r j)) (hs hr)
  · by_contra h
    push Not at h
    have hs : convexHull ℝ (p '' s) ⊆ {z | z j < r j} := by
      apply convexHull_min
      · rintro _ ⟨i, _, rfl⟩
        exact h i
      · exact convex_halfSpace_lt (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (r j)
    exact (lt_irrefl (r j)) (hs hr)

theorem withinBounds_of_mem_hullFacesAt {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ} {σ : Finset (Fin n)}
    (hσ : σ ∈ hullFacesAt d p r) : WithinBounds p r :=
  withinBounds_of_mem_convexHull (mem_hullFacesAt.mp hσ).2

theorem hullCount_eq_zero_of_not_withinBounds {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ} (h : ¬ WithinBounds p r) :
    hullCount d p r = 0 := by
  classical
  unfold hullCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  exact h (withinBounds_of_mem_hullFacesAt hσ)

theorem WithinBounds.one_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    {r : Fin d → ℝ} (hbox : WithinBounds p r) (hp : Separated p) (j : Fin d) :
    1 < r j := by
  obtain ⟨i, hi⟩ := (hbox j).1
  exact (hp.one_lt i j).trans_le hi

theorem WithinBounds.source_query_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    {r : Fin d → ℝ} (hbox : WithinBounds p r) (hp : Separated p)
    (i : Fin n) {j j' : Fin d} (hjj' : j < j') : p i j < r j' := by
  obtain ⟨i', hi'⟩ := (hbox j').1
  exact (hp.cross_coordinate_lt i i' hjj').trans_le hi'

theorem WithinBounds.query_source_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    {r : Fin d → ℝ} (hbox : WithinBounds p r) (hp : Separated p)
    (i : Fin n) {j j' : Fin d} (hjj' : j < j') : r j < p i j' := by
  obtain ⟨i', hi'⟩ := (hbox j).2
  exact hi'.trans_lt (hp.cross_coordinate_lt i' i hjj')

theorem WithinBounds.query_query_lt {d n : ℕ} {p : Fin n → Fin d → ℝ}
    {r : Fin d → ℝ} (hbox : WithinBounds p r) (hp : Separated p)
    {j j' : Fin d} (hjj' : j < j') : r j < r j' := by
  obtain ⟨i, hi⟩ := (hbox j).2
  exact hi.trans_lt (hbox.source_query_lt hp i hjj')

/-- Deleting the source neighbors bracketing each coordinate leaves strong
separation between every remaining source coordinate and the query. -/
theorem exists_query_deletion {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) {r : Fin d → ℝ} (hbox : WithinBounds p r) :
    ∃ D : Finset (Fin n), D.card ≤ 2 * d ∧
      ∀ i, i ∉ D → ∀ j, growth d (p i j) < r j ∨ growth d (r j) < p i j := by
  classical
  let below (j : Fin d) : Finset (Fin n) := Finset.univ.filter (fun i => p i j ≤ r j)
  let above (j : Fin d) : Finset (Fin n) := Finset.univ.filter (fun i => r j ≤ p i j)
  have hbelow (j : Fin d) : (below j).Nonempty := by
    obtain ⟨i, hi⟩ := (hbox j).1
    exact ⟨i, by simp [below, hi]⟩
  have habove (j : Fin d) : (above j).Nonempty := by
    obtain ⟨i, hi⟩ := (hbox j).2
    exact ⟨i, by simp [above, hi]⟩
  let last (j : Fin d) := (below j).max' (hbelow j)
  let first (j : Fin d) := (above j).min' (habove j)
  let D := Finset.univ.image last ∪ Finset.univ.image first
  have hcard : D.card ≤ 2 * d := by
    calc
      D.card ≤ (Finset.univ.image last).card + (Finset.univ.image first).card :=
        Finset.card_union_le _ _
      _ ≤ Finset.univ.card + Finset.univ.card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = 2 * d := by simp; omega
  refine ⟨D, hcard, ?_⟩
  intro i hi j
  have hilast : i ≠ last j := by
    intro heq
    apply hi
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  have hifirst : i ≠ first j := by
    intro heq
    apply hi
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  rcases le_or_gt (p i j) (r j) with hle | hgt
  · left
    have himem : i ∈ below j := by simp [below, hle]
    have hilastle : i ≤ last j := Finset.le_max' _ _ himem
    have hilastlt : i < last j := lt_of_le_of_ne hilastle hilast
    have hlastmem : last j ∈ below j := Finset.max'_mem _ _
    have hlastle : p (last j) j ≤ r j := (Finset.mem_filter.mp hlastmem).2
    exact (hp.gap i (last j) j j (Or.inr ⟨rfl, hilastlt⟩)).trans_le hlastle
  · right
    have himem : i ∈ above j := by simp [above, hgt.le]
    have hfirstile : first j ≤ i := Finset.min'_le _ _ himem
    have hfirstilt : first j < i := lt_of_le_of_ne hfirstile hifirst.symm
    have hfirstmem : first j ∈ above j := Finset.min'_mem _ _
    have hfirstle : r j ≤ p (first j) j := (Finset.mem_filter.mp hfirstmem).2
    have hgrowth : growth d (r j) ≤ growth d (p (first j) j) :=
      growth_monotone d ((zero_lt_one.trans (hbox.one_lt hp j)).le)
        ((zero_lt_one.trans (hp.one_lt (first j) j)).le) hfirstle
    exact hgrowth.trans_lt (hp.gap (first j) i j j (Or.inr ⟨rfl, hfirstilt⟩))

end SharpTopologicalOverlap.BMN
