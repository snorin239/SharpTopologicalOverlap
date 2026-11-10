module

public import SharpTopologicalOverlap.BMN.Augmented
public import SharpTopologicalOverlap.BMN.Query
public import SharpTopologicalOverlap.BMN.Upper
public import SharpTopologicalOverlap.BMN.Lower
public import SharpTopologicalOverlap.BMN.Color
public import SharpTopologicalOverlap.BMN.Counting

/-! # The BMN type lemma and its uniform finite overlap bound -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Bounding-box control preserves column ordering after inserting a query
row into an augmented source matrix. -/
theorem replacement_columns_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ}
    (hp : Separated p) (hbox : WithinBounds p r) (s : Fin (d + 1) → Fin n)
    (k i i' j j' : Fin (d + 1)) (hjj' : j < j') :
    ((augmentedMatrix (p ∘ s)).updateRow k (Fin.cons 1 r)) i j <
      ((augmentedMatrix (p ∘ s)).updateRow k (Fin.cons 1 r)) i' j' := by
  cases j using Fin.cases with
  | zero =>
    cases j' using Fin.cases with
    | zero => exact (lt_irrefl _ hjj').elim
    | succ j' =>
      by_cases hi : i = k <;> by_cases hi' : i' = k
      · simp only [Matrix.updateRow_apply, hi, hi', ↓reduceIte,
          Fin.cons_zero, Fin.cons_succ]
        exact hbox.one_lt hp j'
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hp.one_lt (s i') j'
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hbox.one_lt hp j'
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hp.one_lt (s i') j'
  | succ j =>
    cases j' using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hjj').elim
    | succ j' =>
      have hjj : j < j' := by simpa using hjj'
      by_cases hi : i = k <;> by_cases hi' : i' = k
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hbox.query_query_lt hp hjj
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hbox.query_source_lt hp (s i') hjj
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hbox.source_query_lt hp (s i) hjj
      · simpa [Matrix.updateRow_apply, hi, hi', augmentedMatrix, Function.comp_apply]
          using hp.cross_coordinate_lt (s i) (s i') hjj

/-- All matrix hypotheses in the determinant proof follow from a separated
source simplex, a query in its closed hull, and the surviving query gaps. -/
theorem matrixQuery_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ}
    (hp : Separated p) (hbox : WithinBounds p r)
    {s : Fin (d + 1) → Fin n} (hs : StrictMono s)
    (hgap : ∀ i j, growth d (p (s i) j) < r j ∨ growth d (r j) < p (s i) j)
    (hr : r ∈ convexHull ℝ (Set.range (p ∘ s))) :
    MatrixQuery (augmentedMatrix (p ∘ s)) (Fin.cons 1 r) where
  one_le := augmentedMatrix_one_le_of_separated hp s
  query_one_le j := by
    cases j using Fin.cases with
    | zero => simp
    | succ j => exact (hbox.one_lt hp j).le
  source_gap a b j hab hj := by
    cases j using Fin.cases with
    | zero => exact (lt_irrefl _ hj).elim
    | succ j => exact hp.gap (s a) (s b) j j (Or.inr ⟨rfl, hs hab⟩)
  replacement_columns := replacement_columns_of_separated hp hbox s
  query_gap i j hj := by
    cases j using Fin.cases with
    | zero => exact (lt_irrefl _ hj).elim
    | succ j => exact hgap i j
  det_nonneg k := det_updateRow_nonneg_of_mem_convexHull
    (det_augmentedMatrix_pos_of_separated hp hs).le hr k

/-- A surviving containing simplex interleaves the query coordinate by
coordinate. Both inequalities are strict, even for closed-hull membership. -/
theorem interleaves_of_mem_convexHull {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ}
    (hp : Separated p) (hbox : WithinBounds p r)
    {s : Fin (d + 1) → Fin n} (hs : StrictMono s)
    (hgap : ∀ i j, growth d (p (s i) j) < r j ∨ growth d (r j) < p (s i) j)
    (hr : r ∈ convexHull ℝ (Set.range (p ∘ s))) :
    ∀ j : Fin d, p (s j.castSucc) j < r j ∧ r j < p (s j.succ) j := by
  have h := matrixQuery_of_separated hp hbox hs hgap hr
  have hu := h.upper_bounds
  have hl := h.lower_bounds hu
  intro j
  exact ⟨hl j, hu j⟩

/-- BMN Lemma 2.2: the sorted vertices of a surviving containing simplex
have consecutive types. -/
theorem type_of_mem_convexHull {d n : ℕ}
    {p : Fin n → Fin d → ℝ} {r : Fin d → ℝ}
    (hp : Separated p) (hbox : WithinBounds p r)
    {s : Fin (d + 1) → Fin n} (hs : StrictMono s)
    (hgap : ∀ i j, growth d (p (s i) j) < r j ∨ growth d (r j) < p (s i) j)
    (hr : r ∈ convexHull ℝ (Set.range (p ∘ s))) :
    ∀ k, pointType (p (s k)) r = k := by
  apply pointType_eq_of_interleaves (p ∘ s) r
  · intro j a b hab
    exact hp.coordinate_mono (hs.monotone hab) j
  · exact interleaves_of_mem_convexHull hp hbox hs hgap hr

/-- Every separated configuration satisfies the uniform finite BMN count.
The estimate includes empty configurations and all boundary queries. -/
theorem hullCount_le_of_separated {d n : ℕ} {p : Fin n → Fin d → ℝ}
    (hp : Separated p) (r : Fin d → ℝ) :
    (hullCount d p r : ℝ) ≤ ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
      (2 * d : ℝ) * ((n - 1).choose d : ℝ) := by
  by_cases hbox : WithinBounds p r
  · obtain ⟨D, hD, hgap⟩ := exists_query_deletion hp hbox
    have hcolor : ∀ σ ∈ hullFacesAt d p r,
        Disjoint σ D → Set.InjOn (fun i => pointType (p i) r) (σ : Set (Fin n)) := by
      intro σ hσ hdis
      obtain ⟨hcard, hr⟩ := mem_hullFacesAt.mp hσ
      let s := σ.orderEmbOfFin hcard
      have hs : StrictMono s := s.strictMono
      have hsgap : ∀ i j,
          growth d (p (s i) j) < r j ∨ growth d (r j) < p (s i) j := by
        intro i j
        apply hgap (s i) ?_ j
        intro hiD
        exact Finset.disjoint_left.mp hdis (σ.orderEmbOfFin_mem hcard i) hiD
      have hr' : r ∈ convexHull ℝ (Set.range (p ∘ s)) := by
        simpa only [Set.range_comp, s, Finset.range_orderEmbOfFin] using hr
      apply injOn_pointType_of_interleaves p r σ hcard
      · intro j a b hab
        exact hp.coordinate_mono hab j
      · exact interleaves_of_mem_convexHull hp hbox hs hsgap hr'
    simpa only [Fintype.card_fin] using
      hullCount_le_of_color d p r D (fun i => pointType (p i) r) hD hcolor
  · simp only [hullCount_eq_zero_of_not_withinBounds hbox, Nat.cast_zero]
    positivity

end SharpTopologicalOverlap.BMN
