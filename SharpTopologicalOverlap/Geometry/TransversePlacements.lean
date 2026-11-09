module

public import SharpTopologicalOverlap.Geometry.GeneralPosition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Perturbing source directions to span modulo a fixed target direction

This is the density part of condition G4 in Appendix A. The construction keeps
the first source point fixed and successively perturbs difference vectors
outside the proper subspace already spanned together with the target direction.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Module Metric
open scoped Topology BigOperators

variable {d : ℕ}

/-- Vectors can be perturbed arbitrarily little to span modulo a fixed
subspace as soon as their number is at least its codimension. -/
theorem exists_near_spanning_modulo (k : ℕ)
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : d ≤ k + finrank ℝ T)
    (v : Fin k → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Fin k → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖w i - v i‖ < ε) ∧ Submodule.span ℝ (range w) ⊔ T = ⊤ := by
  classical
  induction k generalizing T with
  | zero =>
    have hle : finrank ℝ T ≤ d := by simpa using T.finrank_le
    have htop : T = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa using (show finrank ℝ T = d by omega))
    exact ⟨v, fun i => Fin.elim0 i, by simp [htop]⟩
  | succ k ih =>
    by_cases htop : T = ⊤
    · exact ⟨v, fun i => by simpa using hε, by simp [htop]⟩
    have hproper : T.toAffineSubspace ≠ ⊤ := by
      intro h
      have hdir := congrArg AffineSubspace.direction h
      exact htop (by simpa only [Submodule.toAffineSubspace_direction,
        AffineSubspace.direction_top] using hdir)
    obtain ⟨w₀, hw₀near, hw₀not⟩ :=
      (dense_compl_affineSubspace T.toAffineSubspace hproper).inter_open_nonempty
        (ball (v 0) ε) isOpen_ball ⟨v 0, mem_ball_self hε⟩
    have hw₀ : w₀ ∉ T := hw₀not
    let U := T ⊔ Submodule.span ℝ ({w₀} : Set (EuclideanSpace ℝ (Fin d)))
    have hrank : finrank ℝ U = finrank ℝ T + 1 := Submodule.finrank_sup_span_singleton hw₀
    obtain ⟨w, hwnear, hwspan⟩ := ih U (by rw [hrank]; omega) (fun i => v i.succ)
    refine ⟨Fin.cons w₀ w, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using mem_ball_iff_norm.mp hw₀near
      · simpa only [Fin.cons_succ] using hwnear j
    · rw [Fin.range_cons, Submodule.span_insert]
      simpa only [U, sup_assoc, sup_comm, sup_left_comm] using hwspan

/-- G4 with one target direction fixed. -/
def SpanningDirections {k : ℕ}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (y : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) : Prop :=
  Submodule.span ℝ (range (fun i : Fin k => y i.succ - y 0)) ⊔ T = ⊤

/-- An arbitrary source simplex placement can be approximated by one whose
directions span modulo the fixed target direction. The base point is fixed. -/
theorem exists_near_spanningDirections {k : ℕ}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : d ≤ k + finrank ℝ T)
    (y : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Fin (k + 1) → EuclideanSpace ℝ (Fin d), z 0 = y 0 ∧
      (∀ i, ‖z i - y i‖ < ε) ∧ SpanningDirections T z := by
  obtain ⟨w, hwnear, hwspan⟩ :=
    exists_near_spanning_modulo k T hdim (fun i : Fin k => y i.succ - y 0) hε
  refine ⟨Fin.cons (y 0) (fun i => y 0 + w i), rfl, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero, sub_self, norm_zero] using hε
    · simpa only [Fin.cons_succ, show y 0 + w j - y j.succ =
        w j - (y j.succ - y 0) by abel] using hwnear j
  · simpa only [SpanningDirections, Fin.cons_succ, Fin.cons_zero, add_sub_cancel_left]
      using hwspan

/-- The source placements satisfying the fixed-target spanning condition are
dense whenever the dimension inequality of G4 holds. -/
theorem dense_spanningDirections {k : ℕ}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdim : d ≤ k + finrank ℝ T) :
    Dense {y : Fin (k + 1) → EuclideanSpace ℝ (Fin d) | SpanningDirections T y} := by
  apply Metric.dense_iff.mpr
  intro y ε hε
  obtain ⟨z, _, hz, hspan⟩ := exists_near_spanningDirections T hdim y hε
  exact ⟨z, (dist_pi_lt_iff hε).mpr (fun i => by simpa only [dist_eq_norm] using hz i), hspan⟩

/-- A continuously varying finite generating family continues to span under
sufficiently small changes. Fixed linear combinations of the original family
give a nearby basis. -/
theorem isOpen_finite_family_span_top {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (u : X → ι → EuclideanSpace ℝ (Fin d)) (hu : Continuous u) :
    IsOpen {x : X | Submodule.span ℝ (range (u x)) = ⊤} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let B := Module.finBasis ℝ (EuclideanSpace ℝ (Fin d))
  have hcoeff (j : Fin (finrank ℝ (EuclideanSpace ℝ (Fin d)))) :
      ∃ c : ι → ℝ, ∑ i, c i • u x i = B j := by
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    rw [hx]
    exact Submodule.mem_top
  choose c hc using hcoeff
  let b (y : X) : Fin (finrank ℝ (EuclideanSpace ℝ (Fin d))) →
      EuclideanSpace ℝ (Fin d) := fun j => ∑ i, c j i • u y i
  have hb : b x = B := funext hc
  have hbcont : Continuous b := by
    apply continuous_pi
    intro j
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp hu).const_smul (c j i))
  have hbind : LinearIndependent ℝ (b x) := by rw [hb]; exact B.linearIndependent
  have hevent : ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (b y) :=
    hbcont.continuousAt.eventually hbind.eventually
  filter_upwards [hevent] with y hy
  apply top_unique
  rw [← hy.span_eq_top_of_card_eq_finrank' (by simp)]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- Spanning modulo a fixed subspace is an open condition on any continuously
varying finite family of vectors. -/
theorem isOpen_finite_family_span_sup {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (v : X → ι → EuclideanSpace ℝ (Fin d)) (hv : Continuous v) :
    IsOpen {x : X | Submodule.span ℝ (range (v x)) ⊔ T = ⊤} := by
  classical
  let B := Module.finBasis ℝ T
  have hT : Submodule.span ℝ (range (fun j => (B j : EuclideanSpace ℝ (Fin d)))) = T := by
    have h := congrArg (Submodule.map T.subtype) B.span_eq
    rw [Submodule.map_span, ← Set.range_comp] at h
    simpa only [Function.comp_def, Submodule.map_top, Submodule.range_subtype,
      Submodule.subtype_apply] using h
  let u (x : X) : ι ⊕ Fin (finrank ℝ T) → EuclideanSpace ℝ (Fin d) :=
    Sum.elim (v x) (fun j => B j)
  have hspan (x : X) :
      Submodule.span ℝ (range (u x)) = Submodule.span ℝ (range (v x)) ⊔ T := by
    dsimp only [u]
    rw [Sum.elim_range, Submodule.span_union, hT]
  have hu : Continuous u := by
    apply continuous_pi
    intro i
    cases i with
    | inl j => exact (continuous_apply j).comp hv
    | inr j => exact continuous_const
  simpa only [hspan] using isOpen_finite_family_span_top u hu

/-- The fixed-target G4 locus is open. -/
theorem isOpen_spanningDirections {k : ℕ}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    IsOpen {y : Fin (k + 1) → EuclideanSpace ℝ (Fin d) | SpanningDirections T y} := by
  change IsOpen {y : Fin (k + 1) → EuclideanSpace ℝ (Fin d) |
    Submodule.span ℝ (range (fun i : Fin k => y i.succ - y 0)) ⊔ T = ⊤}
  exact isOpen_finite_family_span_sup (ι := Fin k)
    (X := Fin (k + 1) → EuclideanSpace ℝ (Fin d)) T
    (fun y (i : Fin k) => y i.succ - y 0)
    (continuous_pi fun i => (continuous_apply i.succ).sub (continuous_apply 0))

/-- Difference vectors from the first point generate the direction of an
ordered finite placement. -/
theorem vectorSpan_range_fin_succ {k : ℕ}
    (y : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) :
    vectorSpan ℝ (range y) =
      Submodule.span ℝ (range (fun i : Fin k => y i.succ - y 0)) := by
  rw [vectorSpan_range_eq_span_range_vsub_right ℝ y 0]
  change Submodule.span ℝ (range (fun i => y i - y 0)) = _
  have heq : (fun i => y i - y 0) = Fin.cons 0 (fun i : Fin k => y i.succ - y 0) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  rw [heq, Fin.range_cons, Submodule.span_insert_zero]

/-- The G4 direction condition for a specified finite subset of an ambient
source vertex type. -/
def SpanningDirectionsOn {Q : Type*}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (A : Finset Q)
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  vectorSpan ℝ (y '' (A : Set Q)) ⊔ T = ⊤

/-- G4 can be obtained by perturbing only the vertices of the specified
nonempty source set. -/
theorem exists_near_spanningDirectionsOn {Q : Type*}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (A : Finset Q) (hA : A.Nonempty)
    (hdim : d ≤ A.card - 1 + finrank ℝ T)
    (y : Q → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d), (∀ q, ‖z q - y q‖ < ε) ∧
      (∀ q ∉ A, z q = y q) ∧ SpanningDirectionsOn T A z := by
  classical
  let k := A.card - 1
  have hcard : Fintype.card A = k + 1 := by
    simp only [Fintype.card_coe]
    have := hA.card_pos
    dsimp [k]
    omega
  let e : Fin (k + 1) ≃ A := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨w, _, hwnear, hwspan⟩ :=
    exists_near_spanningDirections T hdim (fun i => y (e i)) hε
  let z : Q → EuclideanSpace ℝ (Fin d) :=
    fun q => if hq : q ∈ A then w (e.symm ⟨q, hq⟩) else y q
  have hz (i : Fin (k + 1)) : z (e i) = w i := by
    simp only [z, dite_eq_left (e i).prop]
    change w (e.symm (e i)) = w i
    rw [Equiv.symm_apply_apply]
  refine ⟨z, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ A
    · simpa only [z, dite_eq_left hq, Equiv.apply_symm_apply] using hwnear (e.symm ⟨q, hq⟩)
    · simpa only [z, dite_eq_right hq, sub_self, norm_zero] using hε
  · intro q hq
    exact dite_eq_right hq
  · have hrange : z '' (A : Set Q) = range w := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨e.symm ⟨q, hq⟩, ?_⟩
        exact (show z q = w (e.symm ⟨q, hq⟩) from dite_eq_left hq).symm
      · rintro ⟨i, rfl⟩
        exact ⟨e i, (e i).prop, hz i⟩
    change vectorSpan ℝ (z '' (A : Set Q)) ⊔ T = ⊤
    rw [hrange, vectorSpan_range_fin_succ]
    exact hwspan

/-- The finite-source G4 locus is open. -/
theorem isOpen_spanningDirectionsOn {Q : Type*}
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (A : Finset Q) (hA : A.Nonempty) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | SpanningDirectionsOn T A y} := by
  classical
  obtain ⟨a, ha⟩ := hA
  have hspan (y : Q → EuclideanSpace ℝ (Fin d)) :
      vectorSpan ℝ (y '' (A : Set Q)) =
        Submodule.span ℝ (range (fun i : A => y i - y a)) := by
    have hrange : y '' (A : Set Q) = range (fun i : A => y i) := by ext x; simp
    rw [hrange, vectorSpan_range_eq_span_range_vsub_right ℝ _ (⟨a, ha⟩ : A)]
    rfl
  have hopen := isOpen_finite_family_span_sup (ι := A)
    (X := Q → EuclideanSpace ℝ (Fin d)) T (fun y (i : A) => y i - y a)
    (continuous_pi fun i => (continuous_apply (i : Q)).sub (continuous_apply a))
  change IsOpen {y : Q → EuclideanSpace ℝ (Fin d) |
    vectorSpan ℝ (y '' (A : Set Q)) ⊔ T = ⊤}
  simpa only [hspan] using hopen

/-- The finite-source G4 locus is dense under the manuscript's dimension
condition. -/
theorem dense_spanningDirectionsOn {Q : Type*} [Fintype Q]
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (A : Finset Q) (hA : A.Nonempty)
    (hdim : d ≤ A.card - 1 + finrank ℝ T) :
    Dense {y : Q → EuclideanSpace ℝ (Fin d) | SpanningDirectionsOn T A y} := by
  apply Metric.dense_iff.mpr
  intro y ε hε
  obtain ⟨z, hz, _, hspan⟩ := exists_near_spanningDirectionsOn T A hA hdim y hε
  exact ⟨z, (dist_pi_lt_iff hε).mpr (fun i => by simpa only [dist_eq_norm] using hz i), hspan⟩

end SharpTopologicalOverlap.Geometry
