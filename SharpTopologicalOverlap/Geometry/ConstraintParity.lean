module

public import SharpTopologicalOverlap.Geometry.Segments
public import Mathlib.Data.ZMod.Basic

/-! # Endpoint parity for finite affine constraints on a line

The inequalities model source and target barycentric coordinates restricted to
their common affine line. Uniqueness of an active inequality and its nonzero
slope are explicit hypotheses. The geometric verification of those hypotheses
for the intersection construction is separate.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace SharpTopologicalOverlap.Geometry

variable {ι : Type*} [Fintype ι]

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- The feasible parameters of finitely many affine nonnegativity constraints. -/
def feasibleParameters (a b : ι → ℝ) : Set ℝ := {t | ∀ i, 0 ≤ a i + t * b i}

/-- A constraint is active if it vanishes at some feasible parameter. -/
def activeConstraints (a b : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∃ t ∈ feasibleParameters a b, a i + t * b i = 0)

@[simp] theorem mem_activeConstraints (a b : ι → ℝ) (i : ι) :
    i ∈ activeConstraints a b ↔ ∃ t ∈ feasibleParameters a b, a i + t * b i = 0 := by
  classical
  simp [activeConstraints]

/-- All strict constraints remain feasible on both sides of a parameter. -/
theorem feasibleParameters_both_sides (a b : ι → ℝ) (t : ℝ)
    (ht : ∀ i, 0 < a i + t * b i) :
    ∃ δ > 0, t - δ ∈ feasibleParameters a b ∧ t + δ ∈ feasibleParameters a b := by
  have hnear : ∀ᶠ u : ℝ in 𝓝 t, ∀ i, 0 < a i + u * b i := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun u : ℝ => a i + u * b i) t := by fun_prop
    exact continuousAt_const.eventually_lt hcont (ht i)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · have hdist : dist (t - δ / 2) t < δ := by
      rw [Real.dist_eq]
      have hsub : t - δ / 2 - t = -(δ / 2) := by ring
      rw [hsub, abs_neg, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    exact fun i => (hball hdist i).le
  · have hdist : dist (t + δ / 2) t < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    exact fun i => (hball hdist i).le

/-- At most one active constraint with nonzero slope prevents isolated feasible points. -/
theorem exists_distinct_feasibleParameter (a b : ι → ℝ) (t : ℝ)
    (ht : t ∈ feasibleParameters a b)
    (hunique : ∀ i j, a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    ∃ u ∈ feasibleParameters a b, u ≠ t := by
  obtain ⟨s, hs, hstrict⟩ := exists_nonzero_strict_finite_affine_constraints
    (fun i => a i + t * b i) b ht hunique hslope
  refine ⟨t + s, ?_, ?_⟩
  · intro i
    have hi := hstrict i
    nlinarith
  · intro heq
    exact hs (by linarith)

/-- A least feasible parameter must have an active constraint. -/
theorem exists_active_of_isLeast (a b : ι → ℝ) {l : ℝ}
    (hl : IsLeast (feasibleParameters a b) l) :
    ∃ i, a i + l * b i = 0 := by
  by_contra hnone
  have hstrict : ∀ i, 0 < a i + l * b i := by
    intro i
    apply (hl.1 i).lt_of_ne'
    exact fun hi => hnone ⟨i, hi⟩
  obtain ⟨δ, hδ, hleft, _⟩ := feasibleParameters_both_sides a b l hstrict
  have := hl.2 hleft
  linarith

/-- A greatest feasible parameter must have an active constraint. -/
theorem exists_active_of_isGreatest (a b : ι → ℝ) {r : ℝ}
    (hr : IsGreatest (feasibleParameters a b) r) :
    ∃ i, a i + r * b i = 0 := by
  by_contra hnone
  have hstrict : ∀ i, 0 < a i + r * b i := by
    intro i
    apply (hr.1 i).lt_of_ne'
    exact fun hi => hnone ⟨i, hi⟩
  obtain ⟨δ, hδ, _, hright⟩ := feasibleParameters_both_sides a b r hstrict
  have := hr.2 hright
  linarith

omit [Fintype ι] in
/-- If extrema exist then the feasible set is exactly the interval between them. -/
theorem feasibleParameters_eq_Icc (a b : ι → ℝ) {l r : ℝ}
    (hl : IsLeast (feasibleParameters a b) l)
    (hr : IsGreatest (feasibleParameters a b) r) :
    feasibleParameters a b = Set.Icc l r := by
  apply Set.Subset.antisymm
  · exact fun t ht => ⟨hl.2 ht, hr.2 ht⟩
  · intro t ht i
    by_cases hb : 0 ≤ b i
    · have hi := hl.1 i
      have hmul := mul_nonneg (sub_nonneg.mpr ht.1) hb
      nlinarith
    · have hi := hr.1 i
      have hmul := mul_nonneg (sub_nonneg.mpr ht.2) (neg_nonneg.mpr (le_of_not_ge hb))
      nlinarith

omit [Fintype ι] in
/-- A nonzero affine constraint can be active only at an endpoint. -/
theorem activeParameter_eq_endpoint (a b : ι → ℝ) {l r t : ℝ}
    (hl : IsLeast (feasibleParameters a b) l)
    (hr : IsGreatest (feasibleParameters a b) r)
    (ht : t ∈ feasibleParameters a b) (i : ι)
    (hzero : a i + t * b i = 0) (hb : b i ≠ 0) : t = l ∨ t = r := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · right
    apply le_antisymm (hr.2 ht)
    by_contra hrt
    have hlt : t < r := lt_of_not_ge hrt
    have hmul := mul_neg_of_pos_of_neg (sub_pos.mpr hlt) hneg
    have hi := hr.1 i
    nlinarith
  · left
    apply le_antisymm
    · by_contra htl
      have hlt : l < t := lt_of_not_ge htl
      have hmul := mul_pos (sub_pos.mpr hlt) hpos
      have hi := hl.1 i
      nlinarith
    · exact hl.2 ht

/-- Nonempty compact feasible constraints under the genericity hypotheses
form a nondegenerate interval with exactly two distinct active indices. -/
theorem finite_affine_constraints_endpoints (a b : ι → ℝ)
    (hcompact : IsCompact (feasibleParameters a b))
    (hne : (feasibleParameters a b).Nonempty)
    (hunique : ∀ t ∈ feasibleParameters a b, ∀ i j,
      a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ t ∈ feasibleParameters a b, ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    ∃ l r : ℝ, ∃ i j : ι,
      l < r ∧ feasibleParameters a b = Set.Icc l r ∧ i ≠ j ∧
      a i + l * b i = 0 ∧ a j + r * b j = 0 ∧
      activeConstraints a b = {i, j} := by
  classical
  obtain ⟨l, hl⟩ := hcompact.exists_isLeast hne
  obtain ⟨r, hr⟩ := hcompact.exists_isGreatest hne
  have hlt : l < r := by
    have hle := hl.2 hr.1
    apply lt_of_le_of_ne hle
    intro hlr
    obtain ⟨u, hu, hul⟩ := exists_distinct_feasibleParameter a b l hl.1
      (hunique l hl.1) (hslope l hl.1)
    have hulu := hl.2 hu
    have huur := hr.2 hu
    exact hul (by linarith)
  obtain ⟨i, hi⟩ := exists_active_of_isLeast a b hl
  obtain ⟨j, hj⟩ := exists_active_of_isGreatest a b hr
  have hij : i ≠ j := by
    intro heq
    subst j
    have hb := hslope l hl.1 i hi
    have hmul : (l - r) * b i = 0 := by nlinarith
    have hlr : l = r := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hb)
    exact (ne_of_lt hlt) hlr
  refine ⟨l, r, i, j, hlt, feasibleParameters_eq_Icc a b hl hr, hij, hi, hj, ?_⟩
  ext k
  rw [mem_activeConstraints]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨t, ht, hk⟩
    rcases activeParameter_eq_endpoint a b hl hr ht k hk (hslope t ht k hk) with htl | htr
    · rw [htl] at hk
      exact Or.inl (hunique l hl.1 k i hk hi)
    · rw [htr] at hk
      exact Or.inr (hunique r hr.1 k j hk hj)
  · rintro (rfl | rfl)
    · exact ⟨l, hl.1, hi⟩
    · exact ⟨r, hr.1, hj⟩

theorem card_activeConstraints_eq_two (a b : ι → ℝ)
    (hcompact : IsCompact (feasibleParameters a b))
    (hne : (feasibleParameters a b).Nonempty)
    (hunique : ∀ t ∈ feasibleParameters a b, ∀ i j,
      a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ t ∈ feasibleParameters a b, ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    (activeConstraints a b).card = 2 := by
  obtain ⟨l, r, i, j, _, _, hij, _, _, hactive⟩ :=
    finite_affine_constraints_endpoints a b hcompact hne hunique hslope
  rw [hactive]
  simp [hij]

/-- The active-facet count is zero modulo two. -/
theorem activeConstraints_card_mod_two (a b : ι → ℝ)
    (hcompact : IsCompact (feasibleParameters a b))
    (hne : (feasibleParameters a b).Nonempty)
    (hunique : ∀ t ∈ feasibleParameters a b, ∀ i j,
      a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ t ∈ feasibleParameters a b, ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    ((activeConstraints a b).card : ZMod 2) = 0 := by
  rw [card_activeConstraints_eq_two a b hcompact hne hunique hslope]
  decide

theorem activeConstraints_eq_empty_of_empty (a b : ι → ℝ)
    (hempty : feasibleParameters a b = ∅) : activeConstraints a b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨t, ht, _⟩ := (mem_activeConstraints a b i).mp hi
  simp [hempty] at ht

/-- The empty-intersection case contributes zero and every nonempty case contributes two. -/
theorem card_activeConstraints_eq_zero_or_two (a b : ι → ℝ)
    (hcompact : IsCompact (feasibleParameters a b))
    (hunique : ∀ t ∈ feasibleParameters a b, ∀ i j,
      a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ t ∈ feasibleParameters a b, ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    (activeConstraints a b).card = 0 ∨ (activeConstraints a b).card = 2 := by
  rcases (feasibleParameters a b).eq_empty_or_nonempty with hempty | hne
  · exact Or.inl (by rw [activeConstraints_eq_empty_of_empty a b hempty]; rfl)
  · exact Or.inr (card_activeConstraints_eq_two a b hcompact hne hunique hslope)

/-- The endpoint indicator sum vanishes modulo two, including empty intersections. -/
theorem sum_activeConstraint_indicators_eq_zero (a b : ι → ℝ)
    (hcompact : IsCompact (feasibleParameters a b))
    (hunique : ∀ t ∈ feasibleParameters a b, ∀ i j,
      a i + t * b i = 0 → a j + t * b j = 0 → i = j)
    (hslope : ∀ t ∈ feasibleParameters a b, ∀ i, a i + t * b i = 0 → b i ≠ 0) :
    (∑ i, if (∃ t ∈ feasibleParameters a b, a i + t * b i = 0)
      then (1 : ZMod 2) else 0) = 0 := by
  classical
  have hsum : (∑ i, if (∃ t ∈ feasibleParameters a b, a i + t * b i = 0)
      then (1 : ZMod 2) else 0) = ((activeConstraints a b).card : ZMod 2) := by
    simp only [activeConstraints, ← Finset.sum_filter]
    simp
  rw [hsum]
  rcases card_activeConstraints_eq_zero_or_two a b hcompact hunique hslope with h | h
  · rw [h]
    rfl
  · rw [h]
    decide

end SharpTopologicalOverlap.Geometry
