module

public import SharpTopologicalOverlap.Barrier.Basic
public import SharpTopologicalOverlap.Spectral
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Limits of barrier critical points

Only coordinates that stay positive are used in the limiting multiplier
equations. This is essential when the limiting point is on a proper face.
-/

@[expose] public noncomputable section

open Filter Topology
open SharpTopologicalOverlap.Spectral SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Barrier

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem continuous_coordinatePartial (d : ℕ) (G : Finset (Finset V)) (i : V) :
    Continuous (coordinatePartial (d + 1) G i) := by
  have heq : coordinatePartial (d + 1) G i =
      fun x => (d + 1 : ℝ) * weightPolynomial d (link d G i) x :=
    funext (partial_eq_link d G i)
  rw [heq]
  exact continuous_const.mul (WeightPolynomial.contDiff d (link d G i) ⊤).continuous

theorem faceCritical_of_partial_eq_on_support (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V)
    (h : ∀ i ∈ support μ, ∀ j ∈ support μ,
      coordinatePartial (d + 1) G i (μ.weights : V → ℝ) =
        coordinatePartial (d + 1) G j (μ.weights : V → ℝ)) : IsFaceCritical d G μ := by
  obtain ⟨j, hj⟩ := support_nonempty μ
  intro x
  rw [differential_apply]
  have hs : ∀ i : V, x.1 i * coordinatePartial (d + 1) G i (μ.weights : V → ℝ) =
      x.1 i * coordinatePartial (d + 1) G j (μ.weights : V → ℝ) := by
    intro i
    by_cases hi : i ∈ support μ
    · rw [h i hi j hj]
    · rw [x.2.1 i hi, zero_mul, zero_mul]
  simp_rw [hs]
  rw [← Finset.sum_mul, x.2.2, zero_mul]

/-- Limits of barrier critical points are critical on their own active
face. No convergence of Hessians at disappearing coordinates is asserted. -/
theorem faceCritical_of_critical_limit (d : ℕ) (G : Finset (Finset V))
    {A : Type*} {l : Filter A} [NeBot l] {ε : A → ℝ} {α : A → V → ℝ}
    {ν : A → Simplex V} {μ : Simplex V}
    (hε : Tendsto ε l (𝓝 0)) (hα : Tendsto α l (𝓝 0)) (hν : Tendsto ν l (𝓝 μ))
    (hc : ∀ᶠ a in l, IsBarrierCritical d G (ε a) (α a) (ν a)) : IsFaceCritical d G μ := by
  apply faceCritical_of_partial_eq_on_support d G μ
  intro i hi j hj
  have hv : Tendsto (fun a => ((ν a).weights : V → ℝ)) l (𝓝 (μ.weights : V → ℝ)) :=
    ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous.tendsto μ).comp hν
  have hterm (k : V) (hk : k ∈ support μ) :
      Tendsto (fun a => coordinatePartial (d + 1) G k ((ν a).weights : V → ℝ) -
        ε a / (ν a).weights k + α a k) l
        (𝓝 (coordinatePartial (d + 1) G k (μ.weights : V → ℝ))) := by
    have hp := ((continuous_coordinatePartial d G k).tendsto _).comp hv
    have hcoord := ((continuous_coordinate k).tendsto μ).comp hν
    have hd := hε.div hcoord (mem_support.mp hk)
    have ht := ((continuous_apply k).tendsto (0 : V → ℝ)).comp hα
    simpa only [zero_div, Pi.zero_apply, sub_zero, add_zero, Function.comp_apply,
      Pi.div_apply] using (hp.sub hd).add ht
  have heq : ∀ᶠ a in l,
      coordinatePartial (d + 1) G i ((ν a).weights : V → ℝ) - ε a / (ν a).weights i + α a i =
      coordinatePartial (d + 1) G j ((ν a).weights : V → ℝ) - ε a / (ν a).weights j + α a j := by
    filter_upwards [hc] with a ha
    exact barrier_coefficient_eq_of_critical d G (ε a) (α a) (ν a) ha i j
  exact tendsto_nhds_unique_of_eventuallyEq (hterm i hi) (hterm j hj) heq

theorem continuous_barrier_bound (d : ℕ) (N : ℝ) :
    Continuous (fun ε : ℝ => N * ε * Real.log ((d + 4 : ℝ) / ε)) := by
  have heq : (fun ε : ℝ => N * ε * Real.log ((d + 4 : ℝ) / ε)) =
      fun ε : ℝ => N * (ε * Real.log (d + 4 : ℝ) - ε * Real.log ε) := by
    funext ε
    by_cases hε : ε = 0
    · simp [hε]
    · rw [Real.log_div (by positivity) hε]
      ring
  rw [heq]
  exact continuous_const.mul ((continuous_id.mul continuous_const).sub Real.continuous_mul_log)

/-- The logarithmic contribution tends to zero along small perturbed
critical points, including when their limit has zero coordinates. -/
theorem tendsto_critical_logTerm_zero (d : ℕ) (G : Finset (Finset V))
    {A : Type*} {l : Filter A} {ε : A → ℝ} {α : A → V → ℝ} {ν : A → Simplex V}
    (hε : Tendsto ε l (𝓝 0))
    (hcrit : ∀ᶠ a in l, 0 < ε a ∧ (∀ i, 0 < (ν a).weights i) ∧
      IsBarrierCritical d G (ε a) (α a) (ν a) ∧
      (Fintype.card V : ℝ) * ε a ≤ 1 ∧ ‖α a‖ ≤ 1) :
    Tendsto (fun a => ε a * logBarrier ((ν a).weights : V → ℝ)) l (𝓝 0) := by
  have hu : Tendsto (fun a => (Fintype.card V : ℝ) * ε a * Real.log ((d + 4 : ℝ) / ε a))
      l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, zero_mul] using
      ((continuous_barrier_bound d (Fintype.card V)).tendsto 0).comp hε
  apply squeeze_zero' _ _ hu
  · filter_upwards [hcrit] with a ha
    exact (critical_logBarrier_bounds d G ha.1 (α a) (ν a) ha.2.1 ha.2.2.1
      ha.2.2.2.1 ha.2.2.2.2).1
  · filter_upwards [hcrit] with a ha
    exact (critical_logBarrier_bounds d G ha.1 (α a) (ν a) ha.2.1 ha.2.2.1
      ha.2.2.2.1 ha.2.2.2.2).2

omit [DecidableEq V] in
theorem continuous_linearTilt_simplex :
    Continuous (fun p : (V → ℝ) × Simplex V => linearTilt p.1 (p.2.weights : V → ℝ)) := by
  unfold linearTilt
  fun_prop

/-- Critical barrier values converge to the value of the unperturbed
polynomial at the limiting probability vector. -/
theorem tendsto_critical_barrier_value (d : ℕ) (G : Finset (Finset V))
    {A : Type*} {l : Filter A} {ε : A → ℝ} {α : A → V → ℝ}
    {ν : A → Simplex V} {μ : Simplex V}
    (hε : Tendsto ε l (𝓝 0)) (hα : Tendsto α l (𝓝 0)) (hν : Tendsto ν l (𝓝 μ))
    (hcrit : ∀ᶠ a in l, 0 < ε a ∧ (∀ i, 0 < (ν a).weights i) ∧
      IsBarrierCritical d G (ε a) (α a) (ν a) ∧
      (Fintype.card V : ℝ) * ε a ≤ 1 ∧ ‖α a‖ ≤ 1) :
    Tendsto (fun a => ambientBarrier d G (ε a) (α a) ((ν a).weights : V → ℝ)) l
      (𝓝 (weightPolynomial (d + 1) G (μ.weights : V → ℝ))) := by
  have hv : Tendsto (fun a => ((ν a).weights : V → ℝ)) l (𝓝 (μ.weights : V → ℝ)) :=
    ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous.tendsto μ).comp hν
  have hp := ((WeightPolynomial.contDiff (d + 1) G ⊤).continuous.tendsto _).comp hv
  have hl := tendsto_critical_logTerm_zero d G hε hcrit
  have ht := (continuous_linearTilt_simplex.tendsto ((0 : V → ℝ), μ)).comp (hα.prodMk_nhds hν)
  simpa only [ambientBarrier, linearTilt, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, Function.comp_apply] using (hp.add hl).add ht

end SharpTopologicalOverlap.Barrier
