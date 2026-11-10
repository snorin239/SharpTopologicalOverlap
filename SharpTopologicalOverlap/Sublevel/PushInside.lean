module

public import SharpTopologicalOverlap.Sublevel.Definitions
public import SharpTopologicalOverlap.Barrier.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Pushing the closed simplex uniformly into its interior

The homotopy is `ψ_t(μ)=(1-t)μ+tu`. Its coordinates and continuity are kept
explicit, so the same push can control chains, the polynomial and the barrier.
-/

@[expose] public noncomputable section

open scoped unitInterval Topology
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Sublevel

variable {V : Type} [Fintype V] [Nonempty V]

/-- The uniform interior push `ψ_t` of the manuscript. -/
def pushInside (t : unitInterval) (μ : Simplex V) : Simplex V := by
  let w : V → ℝ := fun i => (1 - (t : ℝ)) * μ.weights i + (t : ℝ) * (uniform : Simplex V).weights i
  have hw : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
    constructor
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg μ i))
        (mul_nonneg t.2.1 (coordinate_nonneg uniform i))
    · simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, sum_coordinates]
      ring
  exact coordinateHomeomorph.symm ⟨w, hw⟩

@[simp] theorem pushInside_coordinate (t : unitInterval) (μ : Simplex V) (i : V) :
    (pushInside t μ).weights i =
      (1 - (t : ℝ)) * μ.weights i + (t : ℝ) * (uniform : Simplex V).weights i := by
  exact congrArg (fun c : CoordinateSimplex V => c.1 i) (coordinateHomeomorph.apply_symm_apply _)

@[simp] theorem pushInside_zero (μ : Simplex V) : pushInside 0 μ = μ := by
  apply Convexity.StdSimplex.ext
  ext i
  simp

@[simp] theorem pushInside_one (μ : Simplex V) : pushInside 1 μ = uniform := by
  apply Convexity.StdSimplex.ext
  ext i
  simp

theorem continuous_pushInside :
    Continuous (fun p : unitInterval × Simplex V => pushInside p.1 p.2) := by
  apply coordinateHomeomorph.symm.continuous.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_coordinate i).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

theorem pushInside_coordinate_lower (t : unitInterval) (μ : Simplex V) (i : V) :
    (t : ℝ) / Fintype.card V ≤ (pushInside t μ).weights i := by
  rw [pushInside_coordinate, coordinate_uniform, div_eq_mul_inv]
  exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg μ i))

theorem pushInside_positive {t : unitInterval} (ht : 0 < (t : ℝ)) (μ : Simplex V) (i : V) :
    0 < (pushInside t μ).weights i :=
  (div_pos ht (Nat.cast_pos.mpr Fintype.card_pos)).trans_le (pushInside_coordinate_lower t μ i)

/-- At positive time the same homotopy lands in the actual positive simplex. -/
def pushInsidePositive (t : unitInterval) (ht : 0 < (t : ℝ)) :
    C(Simplex V, Barrier.PositiveSimplex V) :=
  ⟨fun μ => ⟨pushInside t μ, pushInside_positive ht μ⟩,
    (continuous_pushInside.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

omit [Nonempty V] in
theorem continuous_simplexPolynomial (d : ℕ) (G : Finset (Finset V)) :
    Continuous (fun μ : Simplex V => weightPolynomial (d + 1) G (μ.weights : V → ℝ)) :=
  (WeightPolynomial.contDiff (d + 1) G 0).continuous.comp
    coordinateHomeomorph.continuous.subtype_val

/-- A single positive push time controls the polynomial at every simplex point
and at every earlier time. -/
theorem exists_pushInside_polynomial_control (d : ℕ) (G : Finset (Finset V))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ t₀ : unitInterval, 0 < (t₀ : ℝ) ∧ ∀ t : unitInterval, t ≤ t₀ → ∀ μ : Simplex V,
      |weightPolynomial (d + 1) G ((pushInside t μ).weights : V → ℝ) -
        weightPolynomial (d + 1) G (μ.weights : V → ℝ)| < γ := by
  let P : Simplex V → ℝ := fun μ => weightPolynomial (d + 1) G (μ.weights : V → ℝ)
  have hP : Continuous P := continuous_simplexPolynomial d G
  have hcont : Continuous (fun q : unitInterval × Simplex V => |P (pushInside q.1 q.2) - P q.2|) :=
    ((hP.comp continuous_pushInside).sub (hP.comp continuous_snd)).abs
  have hevent : ∀ᶠ t in 𝓝 (0 : unitInterval), ∀ μ : Simplex V, |P (pushInside t μ) - P μ| < γ := by
    have h := (isCompact_univ : IsCompact (Set.univ : Set (Simplex V))).eventually_forall_of_forall_eventually
      (x₀ := (0 : unitInterval)) (P := fun t μ => |P (pushInside t μ) - P μ| < γ) (by
        intro μ _
        exact (isOpen_Iio.preimage hcont).mem_nhds (by
          change |P (pushInside 0 μ) - P μ| < γ
          simpa only [pushInside_zero, sub_self, abs_zero] using hγ))
    simpa only [Set.mem_univ, forall_true_left] using h
  obtain ⟨δ, hδ, hδset⟩ := Metric.mem_nhds_iff.mp hevent
  let r := min (δ / 2) 1
  have hr : 0 < r := lt_min (by linarith) zero_lt_one
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  let t₀ : unitInterval := ⟨r, hr.le, min_le_right _ _⟩
  refine ⟨t₀, hr, ?_⟩
  intro t ht μ
  apply hδset ?_ μ
  rw [Metric.mem_ball]
  have hdist : dist t (0 : unitInterval) = (t : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(t : ℝ) - 0| = (t : ℝ)
    simp only [sub_zero, abs_of_nonneg t.2.1]
  rw [hdist]
  exact (show (t : ℝ) ≤ r from ht).trans_lt hrδ

theorem pushInside_logBarrier_le {t : unitInterval} (ht : 0 < (t : ℝ)) (μ : Simplex V) :
    Barrier.logBarrier ((pushInside t μ).weights : V → ℝ) ≤
      (Fintype.card V : ℝ) * Real.log ((Fintype.card V : ℝ) / (t : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hlog (i : V) : -Real.log ((pushInside t μ).weights i) ≤
      Real.log ((Fintype.card V : ℝ) / (t : ℝ)) := by
    have h := Real.log_le_log (div_pos ht hN) (pushInside_coordinate_lower t μ i)
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hN)] at h
    rw [Real.log_div (ne_of_gt hN) (ne_of_gt ht)]
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlog i)
  simpa only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Barrier.logBarrier] using hsum

/-- The barrier and tilt are uniformly small after a fixed positive push. -/
theorem pushInside_barrier_error_le (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 ≤ ε) (α : V → ℝ) {t : unitInterval}
    (ht : 0 < (t : ℝ)) (μ : Simplex V) :
    |Barrier.ambientBarrier d G ε α ((pushInside t μ).weights : V → ℝ) -
      weightPolynomial (d + 1) G ((pushInside t μ).weights : V → ℝ)| ≤
      ε * (Fintype.card V : ℝ) * Real.log ((Fintype.card V : ℝ) / (t : ℝ)) + ‖α‖ := by
  have hnonneg : 0 ≤ ε * Barrier.logBarrier ((pushInside t μ).weights : V → ℝ) :=
    mul_nonneg hε (Barrier.logBarrier_nonneg _)
  have hlog := mul_le_mul_of_nonneg_left (pushInside_logBarrier_le ht μ) hε
  have htilt := Barrier.linearTilt_abs_le_norm α (pushInside t μ)
  have hid : Barrier.ambientBarrier d G ε α ((pushInside t μ).weights : V → ℝ) -
      weightPolynomial (d + 1) G ((pushInside t μ).weights : V → ℝ) =
      ε * Barrier.logBarrier ((pushInside t μ).weights : V → ℝ) +
        Barrier.linearTilt α ((pushInside t μ).weights : V → ℝ) := by
    unfold Barrier.ambientBarrier
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hnonneg]; nlinarith)

end SharpTopologicalOverlap.Sublevel
