module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
import Mathlib.Tactic.Linarith

/-! # Counting negative eigenvalues from a trace bound

This is the finite scalar argument in Lemma 4.1. It applies to any finite
list of real eigenvalues, and isolates the equality case before the matrix
and quadratic-form identifications are used.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Spectral

variable {ι : Type*} [Fintype ι]

/-- The number of strictly negative entries in a finite real spectrum. -/
def negativeCount (ev : ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ev i < 0).card

private theorem sum_negative_floor (ev : ι → ℝ) (κ : ℝ) :
    (∑ i, if ev i < 0 then -κ else 0) = -(negativeCount ev : ℝ) * κ := by
  classical
  rw [← Finset.sum_filter]
  simp [negativeCount]

/-- A common lower bound on the negative entries bounds their total trace. -/
theorem neg_mul_negativeCount_le_sum (ev : ι → ℝ) (κ : ℝ)
    (hlower : ∀ i, -κ ≤ ev i) :
    -(negativeCount ev : ℝ) * κ ≤ ∑ i, ev i := by
  classical
  rw [← sum_negative_floor]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact hlower i
  · exact le_of_not_gt hi

/-- Trace `-dκ` with all eigenvalues at least `-κ` forces at least `d`
strictly negative eigenvalues. -/
theorem le_negativeCount_of_sum (ev : ι → ℝ) (κ : ℝ) (d : ℕ)
    (hκ : 0 < κ) (hlower : ∀ i, -κ ≤ ev i)
    (htrace : ∑ i, ev i = -(d : ℝ) * κ) :
    d ≤ negativeCount ev := by
  have hbound := neg_mul_negativeCount_le_sum ev κ hlower
  rw [htrace] at hbound
  have hreal : (d : ℝ) ≤ (negativeCount ev : ℝ) := by nlinarith
  exact_mod_cast hreal

/-- In the equality case every negative eigenvalue attains its lower bound,
and every other eigenvalue is zero. -/
theorem spectrum_eq_of_negativeCount_eq (ev : ι → ℝ) (κ : ℝ) (d : ℕ)
    (hlower : ∀ i, -κ ≤ ev i)
    (htrace : ∑ i, ev i = -(d : ℝ) * κ)
    (hcount : negativeCount ev = d) :
    ∀ i, ev i = if ev i < 0 then -κ else 0 := by
  classical
  have hnonneg : ∀ i, 0 ≤ ev i - (if ev i < 0 then -κ else 0) := by
    intro i
    split_ifs with hi
    · linarith [hlower i]
    · linarith [le_of_not_gt hi]
  have hsum : ∑ i, (ev i - (if ev i < 0 then -κ else 0)) = 0 := by
    rw [Finset.sum_sub_distrib, htrace, sum_negative_floor, hcount]
    exact sub_self _
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnonneg j).mp hsum i
    (Finset.mem_univ i)
  exact sub_eq_zero.mp hi

/-- A convenient two-conclusion form of spectral rigidity at the minimal count. -/
theorem negative_spectrum_rigidity (ev : ι → ℝ) (κ : ℝ) (d : ℕ)
    (hκ : 0 < κ) (hlower : ∀ i, -κ ≤ ev i)
    (htrace : ∑ i, ev i = -(d : ℝ) * κ) :
    d ≤ negativeCount ev ∧
      (negativeCount ev = d → ∀ i, ev i = -κ ∨ ev i = 0) := by
  refine ⟨le_negativeCount_of_sum ev κ d hκ hlower htrace, ?_⟩
  intro hcount i
  have hi := spectrum_eq_of_negativeCount_eq ev κ d hlower htrace hcount i
  by_cases hneg : ev i < 0
  · exact Or.inl (by simpa only [ite_eq_left hneg] using hi)
  · exact Or.inr (by simpa only [ite_eq_right hneg] using hi)

section SymmetricOperator

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} {Q : QuadraticForm ℝ E}

/-- The scalar negative count agrees with the library's quadratic-form index. -/
theorem negativeCount_eigenvalues_eq_sigNeg (hA : A.IsSymmetric) {N : ℕ}
    (hN : Module.finrank ℝ E = N) (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ) :
    negativeCount (hA.eigenvalues hN) = sigNeg Q := by
  classical
  rw [hA.sigNeg_eq_ncard_eigenvalues_neg hN hQ]
  unfold negativeCount
  have hset : {i | hA.eigenvalues hN i < 0} =
      ((Finset.univ.filter fun i => hA.eigenvalues hN i < 0) : Set (Fin N)) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset]

/-- A lower bound for the quadratic form supplies the corresponding eigenvalue
bound, by evaluating on the unit eigenvectors. -/
theorem eigenvalues_lower_of_form_lower (hA : A.IsSymmetric) {N : ℕ}
    (hN : Module.finrank ℝ E = N) (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ)
    {κ : ℝ} (hlower : ∀ x, -κ * ‖x‖ ^ 2 ≤ Q x) :
    ∀ i, -κ ≤ hA.eigenvalues hN i := by
  intro i
  let b := hA.eigenvectorBasis hN
  have hi := hlower (b i)
  rw [hQ, hA.apply_eigenvectorBasis hN i, real_inner_smul_left,
    real_inner_self_eq_norm_sq, b.orthonormal.1 i] at hi
  simpa only [one_pow, mul_one, RCLike.ofReal_real_eq_id, id_eq] using hi

/-- The trace/count bound in terms of the actual quadratic-form negative index. -/
theorem le_sigNeg_of_trace (hA : A.IsSymmetric) {N d : ℕ}
    (hN : Module.finrank ℝ E = N) (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ)
    {κ : ℝ} (hκ : 0 < κ) (hlower : ∀ i, -κ ≤ hA.eigenvalues hN i)
    (htrace : LinearMap.trace ℝ E A = -(d : ℝ) * κ) :
    d ≤ sigNeg Q := by
  rw [← negativeCount_eigenvalues_eq_sigNeg hA hN hQ]
  apply le_negativeCount_of_sum _ κ d hκ hlower
  rw [← show LinearMap.trace ℝ E A = ∑ i, hA.eigenvalues hN i by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hA.trace_eq_sum_eigenvalues hN]
  exact htrace

/-- A quadratic lower bound and a trace identity imply the required index bound. -/
theorem le_sigNeg_of_form_lower_trace (hA : A.IsSymmetric) {N d : ℕ}
    (hN : Module.finrank ℝ E = N) (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ)
    {κ : ℝ} (hκ : 0 < κ) (hlower : ∀ x, -κ * ‖x‖ ^ 2 ≤ Q x)
    (htrace : LinearMap.trace ℝ E A = -(d : ℝ) * κ) :
    d ≤ sigNeg Q :=
  le_sigNeg_of_trace hA hN hQ hκ (eigenvalues_lower_of_form_lower hA hN hQ hlower) htrace

/-- Equality in the index bound forces the exact two-value spectrum. -/
theorem eigenvalues_eq_of_sigNeg_eq (hA : A.IsSymmetric) {N d : ℕ}
    (hN : Module.finrank ℝ E = N) (hQ : ∀ x, Q x = ⟪A x, x⟫_ℝ)
    {κ : ℝ} (hlower : ∀ i, -κ ≤ hA.eigenvalues hN i)
    (htrace : LinearMap.trace ℝ E A = -(d : ℝ) * κ)
    (hcount : sigNeg Q = d) :
    ∀ i, hA.eigenvalues hN i = if hA.eigenvalues hN i < 0 then -κ else 0 := by
  apply spectrum_eq_of_negativeCount_eq _ κ d hlower
  · rw [← show LinearMap.trace ℝ E A = ∑ i, hA.eigenvalues hN i by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hA.trace_eq_sum_eigenvalues hN]
    exact htrace
  · rw [negativeCount_eigenvalues_eq_sigNeg hA hN hQ, hcount]

end SymmetricOperator

end SharpTopologicalOverlap.Spectral
