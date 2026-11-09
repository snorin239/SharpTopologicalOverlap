module

public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! # The affine line and closed segment underlying intersection parity

Spanning affine directions with dimensions summing to one more than the ambient
dimension meet in an affine line. A nonempty compact convex subset of a line is
a closed segment. These are the geometric foundations for Appendix A's endpoint
count; nondegeneracy and the incident-facet count are separate assertions.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Module
open scoped Convex Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two nonempty affine subspaces with spanning directions and excess dimension
one intersect in an affine line. -/
theorem finrank_direction_inf_eq_one [FiniteDimensional ℝ E]
    (S T : AffineSubspace ℝ E) (hS : (S : Set E).Nonempty)
    (hT : (T : Set E).Nonempty) (hspan : S.direction ⊔ T.direction = ⊤)
    (hdim : finrank ℝ S.direction + finrank ℝ T.direction = finrank ℝ E + 1) :
    finrank ℝ (S ⊓ T).direction = 1 := by
  obtain ⟨x, hxS, hxT⟩ :=
    AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top hS hT hspan
  rw [AffineSubspace.direction_inf_of_mem hxS hxT]
  have h := S.direction.finrank_sup_add_finrank_inf_eq T.direction
  rw [hspan, finrank_top, hdim] at h
  omega

/-- A nonempty compact convex collinear set is a closed segment, possibly with
equal endpoints. The proof selects a pair attaining the largest distance. -/
theorem exists_eq_segment_of_isCompact_convex_collinear {C : Set E}
    (hcompact : IsCompact C) (hconvex : Convex ℝ C) (hne : C.Nonempty)
    (hcollinear : Collinear ℝ C) :
    ∃ a ∈ C, ∃ b ∈ C, C = segment ℝ a b := by
  have hdist : Continuous (fun p : E × E => dist p.1 p.2) := by fun_prop
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmax⟩ :=
    (hcompact.prod hcompact).exists_isMaxOn (hne.prod hne) hdist.continuousOn
  refine ⟨a, ha, b, hb, Subset.antisymm ?_ (hconvex.segment_subset ha hb)⟩
  intro x hx
  have htriple : Collinear ℝ ({a, x, b} : Set E) :=
    hcollinear.subset (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, hx, hb⟩)
  rcases htriple.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact mem_segment_iff_wbtw.mpr h
  · have heq := h.dist_add_dist
    have hle := hmax (show (x, a) ∈ C ×ˢ C from ⟨hx, ha⟩)
    change dist x a ≤ dist a b at hle
    have hzero : dist x b = 0 := by
      rw [dist_comm b a] at heq
      linarith [dist_nonneg (x := x) (y := b)]
    exact (dist_eq_zero.mp hzero).symm ▸ right_mem_segment ℝ a b
  · have heq := h.dist_add_dist
    have hle := hmax (show (b, x) ∈ C ×ˢ C from ⟨hb, hx⟩)
    change dist b x ≤ dist a b at hle
    have hzero : dist a x = 0 := by
      rw [dist_comm b a] at heq
      linarith [dist_nonneg (x := a) (y := x)]
    exact dist_eq_zero.mp hzero ▸ left_mem_segment ℝ a b

/-- The segment classification applied to an arbitrary compact convex subset of
an affine subspace with direction of dimension at most one. -/
theorem exists_eq_segment_of_isCompact_convex_subset_affineLine
    [FiniteDimensional ℝ E] {C : Set E} (L : AffineSubspace ℝ E)
    (hline : finrank ℝ L.direction ≤ 1) (hsub : C ⊆ L)
    (hcompact : IsCompact C) (hconvex : Convex ℝ C) (hne : C.Nonempty) :
    ∃ a ∈ C, ∃ b ∈ C, C = segment ℝ a b := by
  apply exists_eq_segment_of_isCompact_convex_collinear hcompact hconvex hne
  apply collinear_iff_finrank_le_one.mpr
  rw [← direction_affineSpan]
  exact (Submodule.finrank_mono
    (AffineSubspace.direction_le (affineSpan_le.mpr hsub))).trans hline

/-- Simplex affine spans in the dimension range of the endpoint-parity argument
have a common affine line. -/
theorem simplex_finrank_direction_inf_eq_one [FiniteDimensional ℝ E]
    {p q : ℕ} (s : Affine.Simplex ℝ E p) (t : Affine.Simplex ℝ E q)
    (hdim : p + q = finrank ℝ E + 1)
    (hspan : (affineSpan ℝ (range s.points)).direction ⊔
      (affineSpan ℝ (range t.points)).direction = ⊤) :
    finrank ℝ ((affineSpan ℝ (range s.points)) ⊓
      (affineSpan ℝ (range t.points))).direction = 1 := by
  apply finrank_direction_inf_eq_one _ _
    ⟨s.points 0, s.mem_affineSpan_range 0⟩
    ⟨t.points 0, t.mem_affineSpan_range 0⟩ hspan
  have hs : finrank ℝ (affineSpan ℝ (range s.points)).direction = p := by
    rw [direction_affineSpan]
    exact s.independent.finrank_vectorSpan (Fintype.card_fin _)
  have ht : finrank ℝ (affineSpan ℝ (range t.points)).direction = q := by
    rw [direction_affineSpan]
    exact t.independent.finrank_vectorSpan (Fintype.card_fin _)
  rw [hs, ht]
  exact hdim

/-- A nonempty hull intersection of transverse simplices in the excess-one
dimension range is a closed segment. -/
theorem simplex_convexHull_inter_eq_segment [FiniteDimensional ℝ E]
    {p q : ℕ} (s : Affine.Simplex ℝ E p) (t : Affine.Simplex ℝ E q)
    (hdim : p + q = finrank ℝ E + 1)
    (hspan : (affineSpan ℝ (range s.points)).direction ⊔
      (affineSpan ℝ (range t.points)).direction = ⊤)
    (hne : (convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points)).Nonempty) :
    ∃ a ∈ convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points),
      ∃ b ∈ convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points),
        convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points) =
          segment ℝ a b := by
  apply exists_eq_segment_of_isCompact_convex_subset_affineLine
    ((affineSpan ℝ (range s.points)) ⊓ (affineSpan ℝ (range t.points)))
    (simplex_finrank_direction_inf_eq_one s t hdim hspan).le
    (Set.inter_subset_inter (convexHull_subset_affineSpan _) (convexHull_subset_affineSpan _))
  · exact ((Set.finite_range s.points).isCompact_convexHull ℝ).inter
      ((Set.finite_range t.points).isCompact_convexHull ℝ)
  · exact (convex_convexHull ℝ _).inter (convex_convexHull ℝ _)
  · exact hne

/-- Along a line, finitely many nonnegative affine constraints can be made
strict when at most one constraint is active and its slope is nonzero.

For the parity construction, these constraints are the source and target
barycentric coordinates. Lower-dimensional face exclusion controls the number
of active constraints, and facet transversality controls their slopes. -/
theorem exists_nonzero_strict_finite_affine_constraints {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hnonneg : ∀ i, 0 ≤ a i)
    (hunique : ∀ i j, a i = 0 → a j = 0 → i = j)
    (hslope : ∀ i, a i = 0 → b i ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ i, 0 < a i + t * b i := by
  classical
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i ≠ 0 → 0 < a i + t * b i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : a i = 0
    · simp [hi]
    have hpos : 0 < a i := (hnonneg i).lt_of_ne' hi
    have hcont : ContinuousAt (fun t : ℝ => a i + t * b i) 0 := by fun_prop
    exact ((continuousAt_const.eventually_lt hcont (by simpa using hpos))).mono
      (fun _ ht _ => ht)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hhalf : dist (δ / 2) (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)] using half_lt_self hδ
  have hneg_half : dist (-(δ / 2)) (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
      using half_lt_self hδ
  by_cases hactive : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hactive
    by_cases hb : 0 < b i
    · refine ⟨δ / 2, ne_of_gt (half_pos hδ), fun j => ?_⟩
      by_cases hj : a j = 0
      · have hji := hunique j i hj hi
        subst j
        simpa only [hi, zero_add] using mul_pos (half_pos hδ) hb
      · exact hball hhalf j hj
    · have hbneg : b i < 0 := lt_of_le_of_ne (le_of_not_gt hb) (hslope i hi)
      refine ⟨-(δ / 2), neg_ne_zero.mpr (ne_of_gt (half_pos hδ)), fun j => ?_⟩
      by_cases hj : a j = 0
      · have hji := hunique j i hj hi
        subst j
        simpa only [hi, zero_add] using mul_pos_of_neg_of_neg (neg_neg_of_pos (half_pos hδ)) hbneg
      · exact hball hneg_half j hj
  · refine ⟨δ / 2, ne_of_gt (half_pos hδ), fun i => hball hhalf i ?_⟩
    intro hi
    exact hactive ⟨i, hi⟩

end SharpTopologicalOverlap.Geometry
