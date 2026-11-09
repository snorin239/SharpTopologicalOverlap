module

public import SharpTopologicalOverlap.Simplex
public import SharpTopologicalOverlap.Geometry.GeneralPosition
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Maps.Proper.Basic

/-! # Open loci for finite hull avoidance

The openness argument for G1 and G3 in Lemma A.2 uses compact barycentric
coefficients. Here G3 is proved for any fixed closed target set, without an
affine-independence assumption on the moving source vertices.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Convexity

attribute [local instance] ConvexSpace.ofModule

variable {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convex combinations of an indexed family fill its hull, even when
different indices have equal images. -/
theorem convexHull_range_eq_range_affineMapMk (y : Q → E) :
    convexHull ℝ (range y) = range (StdSimplex.affineMapMk (R := ℝ) y) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨q, rfl⟩
      exact ⟨StdSimplex.single q, by simp⟩
    · exact ConvexSpace.AffineMap.convex_range _
  · rintro x ⟨w, rfl⟩
    rw [StdSimplex.affineMapMk_apply, iConvexComb_eq_sum, Finsupp.sum]
    apply (convex_convexHull ℝ _).sum_mem
    · exact fun q _ => w.nonneg q
    · simpa only [Finsupp.sum] using w.total
    · exact fun q _ => subset_convexHull ℝ _ (mem_range_self q)

/-- The moving hull of finitely many source vertices avoids a fixed closed
set on an open set of placements. -/
theorem isOpen_hull_avoidance (A : Finset Q) {C : Set E} (hC : IsClosed C) :
    IsOpen {y : Q → E | Disjoint (convexHull ℝ (y '' (A : Set Q))) C} := by
  classical
  let F : (Q → E) × Simplex A → E :=
    fun z => ∑ i : A, z.2.weights i • z.1 i
  have hF : Continuous F :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_coordinate i).comp continuous_snd).smul
        ((continuous_apply (i : Q)).comp continuous_fst))
  have hclosed : IsClosed (Prod.fst '' (F ⁻¹' C)) :=
    isClosedMap_fst_of_compactSpace _ (hC.preimage hF)
  have heq : {y : Q → E | Disjoint (convexHull ℝ (y '' (A : Set Q))) C} =
      (Prod.fst '' (F ⁻¹' C))ᶜ := by
    ext y
    have hrange : y '' (A : Set Q) = range (fun i : A => y i) := by
      ext x
      simp
    rw [Set.mem_ofPred_eq, hrange, convexHull_range_eq_range_affineMapMk]
    constructor
    · intro hd hbad
      obtain ⟨⟨z, w⟩, hw, hzy⟩ := hbad
      change z = y at hzy
      subst z
      apply Set.disjoint_left.mp hd
      · exact ⟨w, rfl⟩
      · change (∑ i : A, w.weights i • y i) ∈ C at hw
        simpa only [StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using hw
    · intro havoid
      apply Set.disjoint_left.mpr
      rintro x ⟨w, rfl⟩ hx
      apply havoid
      exact ⟨(y, w), by
        change (∑ i : A, w.weights i • y i) ∈ C
        simpa only [StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using hx, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

/-- The density argument for one G3 condition: translating all source vertices
by one arbitrarily small vector separates their hull from a target affine
space when their dimensions add up to less than `d`. -/
theorem exists_near_hull_avoidance {d : ℕ} (A : Finset Q) (hA : A.Nonempty)
    (y : Q → EuclideanSpace ℝ (Fin d))
    (T : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hT : (T : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : A.card - 1 + Module.finrank ℝ T.direction < d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d), (∀ q, ‖z q - y q‖ < ε) ∧
      Disjoint (convexHull ℝ (z '' (A : Set Q))) T := by
  classical
  let S := affineSpan ℝ (y '' (A : Set Q))
  have hS : (S : Set (EuclideanSpace ℝ (Fin d))).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨y a, subset_affineSpan ℝ _ ⟨a, ha, rfl⟩⟩
  have hcard : A.card = (A.card - 1) + 1 := by
    have := hA.card_pos
    omega
  have hbound : Module.finrank ℝ S.direction ≤ A.card - 1 := by
    dsimp [S]
    rw [direction_affineSpan, ← Finset.coe_image]
    exact finrank_vectorSpan_image_finset_le ℝ y A hcard
  have hsmall := dense_disjoint_affineSubspace_translations S T hS hT
    (lt_of_le_of_lt (Nat.add_le_add_right hbound _) hdim)
  obtain ⟨c, hc, hdisj⟩ := hsmall.inter_open_nonempty
    (Metric.ball 0 ε) Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  refine ⟨fun q => c + y q, fun q => ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right, add_sub_cancel_right] using hc
  · have heq : convexHull ℝ ((fun q => c + y q) '' (A : Set Q)) =
        (fun x => c + x) '' convexHull ℝ (y '' (A : Set Q)) := by
      simpa only [AffineEquiv.constVAdd_apply, AffineEquiv.coe_toAffineMap,
        vadd_eq_add, Set.image_image, Function.comp_def] using
        ((AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) c).toAffineMap.image_convexHull
          (y '' (A : Set Q))).symm
    rw [heq]
    exact hdisj.mono (Set.image_mono (convexHull_subset_affineSpan _)) Set.Subset.rfl

/-- The G3 locus for a finite source face and a fixed closed target set is
open and dense under the below-complementary dimension condition. -/
theorem open_dense_hull_avoidance [Fintype Q] {d : ℕ} (A : Finset Q) (hA : A.Nonempty)
    (T : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hT : (T : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : A.card - 1 + Module.finrank ℝ T.direction < d)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsClosed C) (hCT : C ⊆ T) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) |
      Disjoint (convexHull ℝ (y '' (A : Set Q))) C} ∧
    Dense {y : Q → EuclideanSpace ℝ (Fin d) |
      Disjoint (convexHull ℝ (y '' (A : Set Q))) C} := by
  refine ⟨isOpen_hull_avoidance A hC, Metric.dense_iff.mpr ?_⟩
  intro y ε hε
  obtain ⟨z, hz, hdisj⟩ := exists_near_hull_avoidance A hA y T hT hdim hε
  refine ⟨z, ?_, hdisj.mono Set.Subset.rfl hCT⟩
  exact (dist_pi_lt_iff hε).mpr (fun q => by simpa only [dist_eq_norm] using hz q)

end SharpTopologicalOverlap.Geometry
