module

public import SharpTopologicalOverlap.Barrier.MorseAdapter
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # The logarithmic barrier on the open simplex

The ambient formula is total as a real function, but all calculus statements
below are made where every coordinate is positive.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold Topology
open SharpTopologicalOverlap.Spectral SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Barrier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The linear tilt in ordinary finite coordinates. -/
def linearTilt (α x : V → ℝ) : ℝ := ∑ i, α i * x i

/-- The positive logarithmic barrier, without its small coefficient. -/
def logBarrier (x : V → ℝ) : ℝ := -∑ i, Real.log (x i)

/-- The total ambient formula for the paper's logarithmic perturbation. -/
def ambientBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α x : V → ℝ) : ℝ :=
  weightPolynomial (d + 1) G x + ε * logBarrier x + linearTilt α x

/-- The continuous linear functional with a specified coordinate coefficient vector. -/
def coefficientForm (c : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj i

@[simp] theorem coefficientForm_apply (c x : V → ℝ) :
    coefficientForm c x = ∑ i, c i * x i := by
  simp [coefficientForm, ContinuousLinearMap.sum_apply, smul_eq_mul]

theorem coefficientForm_coe (c : V → ℝ) :
    (coefficientForm c : (V → ℝ) → ℝ) = linearTilt c :=
  funext fun x => coefficientForm_apply c x

/-- The first derivative specified by the coordinate formula in Lemma 5.6(a). -/
def barrierDifferential (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α x : V → ℝ) :
    (V → ℝ) →L[ℝ] ℝ :=
  differential (d + 1) G x - ε • coefficientForm (fun i => (x i)⁻¹) + coefficientForm α

theorem barrierDifferential_apply (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α x y : V → ℝ) :
    barrierDifferential d G ε α x y =
      ∑ i, (coordinatePartial (d + 1) G i x - ε / x i + α i) * y i := by
  simp only [barrierDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, coefficientForm_apply, differential_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv]
  ring

theorem hasFDerivAt_linearTilt (α x : V → ℝ) :
    HasFDerivAt (linearTilt α) (coefficientForm α) x := by
  simpa only [coefficientForm_coe] using (coefficientForm α).hasFDerivAt (x := x)

theorem hasFDerivAt_logBarrier {x : V → ℝ} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt logBarrier (-coefficientForm (fun i => (x i)⁻¹)) x := by
  have h := (HasFDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset V)) =>
    (hasFDerivAt_apply i x).log (hx i))).neg
  have hf : (-∑ i, fun y : V → ℝ => Real.log (y i)) = logBarrier := by
    ext y
    simp [logBarrier]
  simpa only [hf, coefficientForm] using h

theorem hasFDerivAt_ambientBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) {x : V → ℝ} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (ambientBarrier d G ε α) (barrierDifferential d G ε α x) x := by
  have h := ((WeightPolynomial.hasFDerivAt (d + 1) G x).add
    ((hasFDerivAt_logBarrier hx).const_mul ε)).add (hasFDerivAt_linearTilt α x)
  simpa only [ambientBarrier, barrierDifferential, smul_neg, ← sub_eq_add_neg] using! h

theorem contDiffAt_ambientBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) {x : V → ℝ} (hx : ∀ i, x i ≠ 0) (n : ℕ∞ω) :
    ContDiffAt ℝ n (ambientBarrier d G ε α) x := by
  apply ((WeightPolynomial.contDiff (d + 1) G n).contDiffAt.add ?_).add ?_
  · exact contDiffAt_const.mul ((ContDiffAt.sum fun i _ =>
      (contDiff_apply ℝ (fun _ : V => ℝ) i).contDiffAt.log (hx i)).neg)
  · simpa only [coefficientForm_coe] using (coefficientForm α).contDiff.contDiffAt

/-- The derivative of the reciprocal-coordinate coefficient functional. -/
def inverseCoefficientDerivative (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ((V → ℝ) →L[ℝ] ℝ) :=
  ∑ i, (-((x i) ^ 2)⁻¹ • ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

theorem hasFDerivAt_inverseCoefficient {x : V → ℝ} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (fun y : V → ℝ => coefficientForm (fun i => (y i)⁻¹))
      (inverseCoefficientDerivative x) x := by
  have hi (i : V) : HasFDerivAt (fun y : V → ℝ => (y i)⁻¹)
      (-((x i) ^ 2)⁻¹ • (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ)) x := by
    simpa only [Function.comp_def] using!
      (hasDerivAt_inv (𝕜 := ℝ) (hx i)).comp_hasFDerivAt x (hasFDerivAt_apply i x)
  have h := HasFDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset V)) =>
    (hi i).smul_const (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ))
  have hf : (∑ i, fun y : V → ℝ => (y i)⁻¹ • (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ)) =
      (fun y => coefficientForm (fun i => (y i)⁻¹)) := by
    ext y z
    simp [coefficientForm]
  simpa only [hf, inverseCoefficientDerivative] using h

/-- The second derivative in ambient finite coordinates. -/
def barrierHessian (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ((V → ℝ) →L[ℝ] ℝ) :=
  hessian (d + 1) G x - ε • inverseCoefficientDerivative x

theorem hasFDerivAt_barrierDifferential (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) {x : V → ℝ} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (barrierDifferential d G ε α) (barrierHessian d G ε x) x := by
  have h := ((hasFDerivAt_differential (d + 1) G x).sub
    ((hasFDerivAt_inverseCoefficient hx).fun_const_smul ε)).add
      (hasFDerivAt_const (coefficientForm α) x)
  simpa only [barrierDifferential, barrierHessian, add_zero] using! h

theorem fderiv_fderiv_ambientBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) {x : V → ℝ} (hx : ∀ i, x i ≠ 0) :
    fderiv ℝ (fderiv ℝ (ambientBarrier d G ε α)) x = barrierHessian d G ε x := by
  have hevent : ∀ᶠ y in 𝓝 x, ∀ i, y i ≠ 0 := Filter.eventually_all.mpr
    (fun i => (continuous_apply i).continuousAt.eventually_ne (hx i))
  have hgerm : fderiv ℝ (ambientBarrier d G ε α) =ᶠ[𝓝 x] barrierDifferential d G ε α := by
    filter_upwards [hevent] with y hy
    exact (hasFDerivAt_ambientBarrier d G ε α hy).fderiv
  rw [hgerm.fderiv_eq]
  exact (hasFDerivAt_barrierDifferential d G ε α hx).fderiv

theorem barrierHessian_apply (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (x y z : V → ℝ) :
    barrierHessian d G ε x y z = hessian (d + 1) G x y z +
      ε * ∑ i, y i * z i / (x i) ^ 2 := by
  simp only [barrierHessian, sub_apply, smul_apply, inverseCoefficientDerivative,
    sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring

theorem linearTilt_abs_le_norm (α : V → ℝ) (μ : Simplex V) :
    |linearTilt α (μ.weights : V → ℝ)| ≤ ‖α‖ := by
  calc
    |linearTilt α (μ.weights : V → ℝ)| ≤ ∑ i, |α i * μ.weights i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |α i| * μ.weights i := by
      simp only [abs_mul, abs_of_nonneg (coordinate_nonneg μ _)]
    _ ≤ ∑ i, ‖α‖ * μ.weights i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm α i) (coordinate_nonneg μ i)
    _ = ‖α‖ := by rw [← Finset.mul_sum, sum_coordinates, mul_one]

theorem logBarrier_nonneg (μ : Simplex V) : 0 ≤ logBarrier (μ.weights : V → ℝ) := by
  apply neg_nonneg.mpr
  exact Finset.sum_nonpos fun i _ => Real.log_nonpos (coordinate_nonneg μ i) (coordinate_le_one μ i)

theorem neg_log_coordinate_le_logBarrier (μ : Simplex V) (i : V) :
    -Real.log (μ.weights i) ≤ logBarrier (μ.weights : V → ℝ) := by
  unfold logBarrier
  rw [← Finset.sum_neg_distrib]
  exact Finset.single_le_sum (fun j _ => neg_nonneg.mpr
    (Real.log_nonpos (coordinate_nonneg μ j) (coordinate_le_one μ j))) (Finset.mem_univ i)

/-- Every point in a barrier sublevel stays a uniform positive distance from
each coordinate face, the compactness estimate in Lemma 5.6(a). -/
theorem coordinate_ge_exp_of_sublevel (d : ℕ) (G : Finset (Finset V))
    {ε c : ℝ} (hε : 0 < ε) (α : V → ℝ) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hc : ambientBarrier d G ε α (μ.weights : V → ℝ) ≤ c) (i : V) :
    Real.exp (-(c + ‖α‖) / ε) ≤ μ.weights i := by
  apply (Real.le_log_iff_exp_le (hμ i)).mp
  apply (div_le_iff₀ hε).mpr
  have hcoord := mul_le_mul_of_nonneg_left (neg_log_coordinate_le_logBarrier μ i) hε.le
  have hp := WeightPolynomial.nonneg (d + 1) G (coordinate_nonneg μ)
  have htilt := (abs_le.mp (linearTilt_abs_le_norm α μ)).1
  unfold ambientBarrier at hc
  nlinarith

/-- Vanishing of the barrier differential on the affine simplex tangent space. -/
def IsBarrierCritical (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α : V → ℝ)
    (μ : Simplex V) : Prop :=
  ∀ y : V → ℝ, (∑ i, y i) = 0 → barrierDifferential d G ε α (μ.weights : V → ℝ) y = 0

theorem barrier_coefficient_eq_of_critical (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (μ : Simplex V) (hc : IsBarrierCritical d G ε α μ) (i j : V) :
    coordinatePartial (d + 1) G i (μ.weights : V → ℝ) - ε / μ.weights i + α i =
      coordinatePartial (d + 1) G j (μ.weights : V → ℝ) - ε / μ.weights j + α j := by
  have hsum : (∑ a : V, (Pi.single i 1 - Pi.single j 1 : V → ℝ) a) = 0 := by
    simp [Finset.sum_sub_distrib]
  have h := hc _ hsum
  rw [barrierDifferential_apply] at h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_eq_zero] at h
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem critical_multiplier_eq (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hc : IsBarrierCritical d G ε α μ) (i : V) :
    coordinatePartial (d + 1) G i (μ.weights : V → ℝ) - ε / μ.weights i + α i =
      (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) -
        (Fintype.card V : ℝ) * ε + linearTilt α (μ.weights : V → ℝ) := by
  have hsame : (∑ j, μ.weights j *
      (coordinatePartial (d + 1) G j (μ.weights : V → ℝ) - ε / μ.weights j + α j)) =
      coordinatePartial (d + 1) G i (μ.weights : V → ℝ) - ε / μ.weights i + α i := by
    simp_rw [barrier_coefficient_eq_of_critical d G ε α μ hc _ i]
    rw [← Finset.sum_mul, sum_coordinates, one_mul]
  rw [← hsame]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have heuler : (∑ j, μ.weights j * coordinatePartial (d + 1) G j (μ.weights : V → ℝ)) =
      (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) := by
    simpa only [differential_apply, Nat.cast_add, Nat.cast_one] using
      euler (d + 1) G (μ.weights : V → ℝ)
  have hdiv : (∑ j, μ.weights j * (ε / μ.weights j)) = (Fintype.card V : ℝ) * ε := by
    calc
      _ = ∑ _j : V, ε := by
        apply Finset.sum_congr rfl
        intro j _
        field_simp [ne_of_gt (hμ j)]
      _ = _ := by simp
  rw [heuler, hdiv]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The coordinate estimate at critical points from Lemma 5.6(b). -/
theorem coordinate_ge_of_critical (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i) (hc : IsBarrierCritical d G ε α μ)
    (hNε : (Fintype.card V : ℝ) * ε ≤ 1) (hα : ‖α‖ ≤ 1) (i : V) :
    ε / (d + 4 : ℝ) ≤ μ.weights i := by
  have hmult := critical_multiplier_eq d G ε α μ hμ hc i
  have hp := WeightPolynomial.nonneg (d + 1) G (coordinate_nonneg μ)
  have htilt := (abs_le.mp (linearTilt_abs_le_norm α μ)).1
  have hαi : α i ≤ 1 := (le_abs_self (α i)).trans
    ((norm_le_pi_norm α i).trans hα)
  have hpartial := simplex_partial_le d G i μ
  have hdiv : ε / μ.weights i ≤ (d + 4 : ℝ) := by
    have hprod : 0 ≤ (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) :=
      mul_nonneg (by positivity) hp
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < d + 4)).mpr
  have := (div_le_iff₀ (hμ i)).mp hdiv
  nlinarith

theorem critical_logBarrier_bounds (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i) (hc : IsBarrierCritical d G ε α μ)
    (hNε : (Fintype.card V : ℝ) * ε ≤ 1) (hα : ‖α‖ ≤ 1) :
    0 ≤ ε * logBarrier (μ.weights : V → ℝ) ∧
      ε * logBarrier (μ.weights : V → ℝ) ≤
        (Fintype.card V : ℝ) * ε * Real.log ((d + 4 : ℝ) / ε) := by
  refine ⟨mul_nonneg hε.le (logBarrier_nonneg μ), ?_⟩
  have hlog (i : V) : -Real.log (μ.weights i) ≤ Real.log ((d + 4 : ℝ) / ε) := by
    have hcoord := coordinate_ge_of_critical d G hε α μ hμ hc hNε hα i
    have h := Real.log_le_log (div_pos hε (by positivity)) hcoord
    rw [Real.log_div (ne_of_gt hε) (by positivity)] at h
    rw [Real.log_div (by positivity) (ne_of_gt hε)]
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlog i)
  simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum hε.le
  simpa only [logBarrier, ← mul_assoc, mul_comm ε (Fintype.card V : ℝ)] using hmul

variable [Nonempty V]

/-- The total Euclidean-coordinate expression, restricted to the positive
domain in every subsequent manifold statement. -/
def coordinateBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α : V → ℝ) :
    euclideanZeroSumSpace (V := V) → ℝ := ambientBarrier d G ε α ∘ affineCoordinates

/-- The actual barrier function on the open simplex manifold. -/
def barrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α : V → ℝ) :
    openSimplexDomain (V := V) → ℝ := coordinateBarrier d G ε α ∘ Subtype.val

@[simp] theorem barrier_eq_ambient (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V)) :
    barrier d G ε α z = ambientBarrier d G ε α ((toPositiveSimplex z).1.weights : V → ℝ) := by
  change ambientBarrier d G ε α (affineCoordinates z.1) = _
  rw [affineCoordinates_eq_weights]

theorem contDiffOn_coordinateBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (n : ℕ∞ω) :
    ContDiffOn ℝ n (coordinateBarrier d G ε α) (openSimplexDomain (V := V)) := by
  intro z hz
  exact ((contDiffAt_ambientBarrier d G ε α (fun i => ne_of_gt (hz i)) n).comp z
    (contDiff_affineCoordinates n).contDiffAt).contDiffWithinAt

theorem hasFDerivAt_coordinateBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V)) :
    HasFDerivAt (coordinateBarrier d G ε α)
      ((barrierDifferential d G ε α (affineCoordinates z.1)).comp tangentCoordinates) z.1 :=
  (hasFDerivAt_ambientBarrier d G ε α (fun i => ne_of_gt (z.2 i))).comp z.1
    (hasFDerivAt_affineCoordinates z.1)

theorem contMDiff_barrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) n (barrier d G ε α) :=
  (contDiffOn_coordinateBarrier d G ε α n).contMDiffOn.comp_contMDiff
    contMDiff_subtype_val Subtype.prop

theorem continuous_barrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α : V → ℝ) :
    Continuous (barrier d G ε α) := (contMDiff_barrier d G ε α ∞).continuous

theorem second_fderiv_coordinateBarrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V))
    (x y : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (fderiv ℝ (coordinateBarrier d G ε α)) z.1 x y =
      barrierHessian d G ε (affineCoordinates z.1) (tangentCoordinates x) (tangentCoordinates y) := by
  rw [coordinateBarrier, second_derivative_comp_affine _ z.1
    (contDiffAt_ambientBarrier d G ε α (fun i => ne_of_gt (z.2 i)) 2),
    fderiv_fderiv_ambientBarrier d G ε α (fun i => ne_of_gt (z.2 i))]

theorem coordinateBarrier_critical_iff (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V)) :
    fderiv ℝ (coordinateBarrier d G ε α) z.1 = 0 ↔
      IsBarrierCritical d G ε α (toPositiveSimplex z).1 := by
  rw [(hasFDerivAt_coordinateBarrier d G ε α z).fderiv, affineCoordinates_eq_weights]
  constructor
  · intro h y hy
    let x := zeroSumCoordinates.symm (⟨y, hy⟩ : zeroSumSpace (V := V))
    have hx : tangentCoordinates x = y :=
      congrArg Subtype.val (zeroSumCoordinates.apply_symm_apply ⟨y, hy⟩)
    have hval := congrArg (fun L => L x) h
    change barrierDifferential d G ε α ((toPositiveSimplex z).1.weights : V → ℝ)
      (tangentCoordinates x) = 0 at hval
    rwa [hx] at hval
  · intro hc
    ext x
    exact hc (tangentCoordinates x) (sum_tangentCoordinates x)

theorem barrier_critical_iff (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V)) :
    fderiv ℝ ((barrier d G ε α) ∘
      (extChartAt 𝓘(ℝ, euclideanZeroSumSpace (V := V)) z).symm)
      (extChartAt 𝓘(ℝ, euclideanZeroSumSpace (V := V)) z z) = 0 ↔
      IsBarrierCritical d G ε α (toPositiveSimplex z).1 := by
  rw [barrier, openSubtype_fderiv_coordinate, coordinateBarrier_critical_iff]

/-- The actual barrier Hessian on the affine zero-sum tangent space. -/
def barrierTangentForm (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (μ : Simplex V) :
    QuadraticForm ℝ (zeroSumSpace (V := V)) :=
  (barrierHessian d G ε (μ.weights : V → ℝ)).toBilinForm.toQuadraticMap.restrict zeroSumSpace

theorem barrierTangentForm_apply (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (μ : Simplex V)
    (x : zeroSumSpace (V := V)) :
    barrierTangentForm d G ε μ x = hessian (d + 1) G (μ.weights : V → ℝ) x.1 x.1 +
      ε * ∑ i, x.1 i ^ 2 / μ.weights i ^ 2 := by
  change barrierHessian d G ε (μ.weights : V → ℝ) x.1 x.1 = _
  simpa only [pow_two] using barrierHessian_apply d G ε (μ.weights : V → ℝ) x.1 x.1

theorem manifoldMorseIndex_barrier (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) (z : openSimplexDomain (V := V)) :
    TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α) z =
      sigNeg (barrierTangentForm d G ε (toPositiveSimplex z).1) := by
  rw [barrier, openSubtype_manifoldMorseIndex]
  have hform : (fderiv ℝ (fderiv ℝ (coordinateBarrier d G ε α)) z.1).toBilinForm.toQuadraticMap =
      (barrierTangentForm d G ε (toPositiveSimplex z).1).comp
        zeroSumCoordinates.toLinearEquiv.toLinearMap := by
    ext x
    change fderiv ℝ (fderiv ℝ (coordinateBarrier d G ε α)) z.1 x x =
      barrierHessian d G ε ((toPositiveSimplex z).1.weights : V → ℝ)
        (zeroSumCoordinates x).1 (zeroSumCoordinates x).1
    rw [second_fderiv_coordinateBarrier, affineCoordinates_eq_weights]
    rfl
  rw [hform, sigNeg_comp_linearEquiv]

/-- A positive coordinate slab is a compact subset of the closed simplex. -/
theorem isCompact_coordinate_slab (b : ℝ) :
    IsCompact {μ : Simplex V | ∀ i, b ≤ μ.weights i} := by
  have hclosed : IsClosed {μ : Simplex V | ∀ i, b ≤ μ.weights i} := by
    simpa only [Set.iInter_ofPred] using isClosed_iInter
      (fun i : V => isClosed_le continuous_const (continuous_coordinate i))
  simpa only [Set.univ_inter] using isCompact_univ.inter_right hclosed

/-- Compactness of all sublevels of the actual open-simplex barrier. -/
theorem isCompact_barrier_sublevel (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ) (c : ℝ) :
    IsCompact {z : openSimplexDomain (V := V) | barrier d G ε α z ≤ c} := by
  let b := Real.exp (-(c + ‖α‖) / ε)
  have hb : 0 < b := Real.exp_pos _
  let K := {μ : Simplex V | ∀ i, b ≤ μ.weights i}
  have hK : IsCompact K := isCompact_coordinate_slab b
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → openSimplexDomain (V := V) := fun μ =>
    fromPositiveSimplex ⟨μ.1, fun i => hb.trans_le (μ.2 i)⟩
  have hf : Continuous f := by
    exact openSimplexHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hcompact : IsCompact (Set.range f) := isCompact_range hf
  have hclosed : IsClosed {z : openSimplexDomain (V := V) | barrier d G ε α z ≤ c} :=
    isClosed_le (continuous_barrier d G ε α) continuous_const
  apply hcompact.of_isClosed_subset hclosed
  intro z hz
  change barrier d G ε α z ≤ c at hz
  let μ := (toPositiveSimplex z).1
  have hμ : μ ∈ K := by
    intro i
    apply coordinate_ge_exp_of_sublevel d G hε α μ (toPositiveSimplex z).2
    simpa only [barrier_eq_ambient, μ] using! hz
  refine ⟨⟨μ, hμ⟩, ?_⟩
  exact openSimplexHomeomorph.left_inv z

/-- Properness of the barrier function, as required by the Morse band theorem. -/
theorem isProperMap_barrier (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ) :
    IsProperMap (barrier d G ε α) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_barrier d G ε α, ?_⟩
  intro K hK
  obtain ⟨c, hc⟩ := hK.bddAbove
  apply (isCompact_barrier_sublevel d G hε α c).of_isClosed_subset
    (hK.isClosed.preimage (continuous_barrier d G ε α))
  intro z hz
  exact hc hz

end SharpTopologicalOverlap.Barrier
