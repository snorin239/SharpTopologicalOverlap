module

public import SharpTopologicalOverlap.Spectral.Normalization
public import Mathlib.Algebra.Order.Star.Real

/-! # The covariance of a randomly sampled edge

The distribution is a finite weighted sum. Positivity is obtained from the
library's positive semidefinite rank-one matrices, without probability spaces.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix
open SharpTopologicalOverlap.WeightPolynomial Matrix

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized weight of an edge; normalization is proved below. -/
def edgeWeight (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) (e : Finset V) : ℝ :=
  (k.factorial : ℝ) * monomial e (μ.weights : V → ℝ) /
    weightPolynomial k G (μ.weights : V → ℝ)

theorem edgeWeight_nonneg (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) (e : Finset V) :
    0 ≤ edgeWeight k G μ e :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (monomial_nonneg (coordinate_nonneg μ)))
    (WeightPolynomial.nonneg k G (coordinate_nonneg μ))

theorem sum_edgeWeight (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0) :
    (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e) = 1 := by
  simp only [edgeWeight, ← Finset.sum_div, ← Finset.mul_sum]
  exact div_self hp

/-- The random vector used in the covariance calculation. -/
def edgeVector (μ : Simplex V) (e : Finset V) : V → ℝ :=
  fun i => if i ∈ e then (rootVector μ i)⁻¹ else 0

/-- A finite sum of centered rank-one covariance matrices. -/
def covariance (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : Matrix V V ℝ :=
  ∑ e ∈ homogeneousPart k G, edgeWeight k G μ e •
    vecMulVec (edgeVector μ e - (k : ℝ) • rootVector μ)
      (edgeVector μ e - (k : ℝ) • rootVector μ)

theorem covariance_posSemidef (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (covariance k G μ).PosSemidef := by
  apply Matrix.posSemidef_sum (homogeneousPart k G)
  intro e _
  have h : (vecMulVec (edgeVector μ e - (k : ℝ) • rootVector μ)
      (edgeVector μ e - (k : ℝ) • rootVector μ)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
      (edgeVector μ e - (k : ℝ) • rootVector μ)
  exact h.smul (edgeWeight_nonneg k G μ e)

theorem monomial_erase_factor (e : Finset V) {i : V} (hi : i ∈ e) (x : V → ℝ) :
    monomial e x = x i * monomial (e.erase i) x := by
  exact (Finset.mul_prod_erase e x hi).symm

theorem edgeWeight_mem_sum (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) (i : V) :
    (∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) =
      μ.weights i * coordinatePartial k G i (μ.weights : V → ℝ) /
        weightPolynomial k G (μ.weights : V → ℝ) := by
  simp only [edgeWeight, coordinatePartial, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [monomial_erase_factor e (Finset.mem_filter.mp he).2]
  ring

theorem edgeVector_mean (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (i : V) :
    (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e * edgeVector μ e i) =
      (k : ℝ) * rootVector μ i := by
  have h : (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e * edgeVector μ e i) =
      (∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) /
        rootVector μ i := by
    simp only [edgeVector, Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : i ∈ e <;> simp [hi]
  rw [h, edgeWeight_mem_sum, stationary_partial μ hc i]
  have hi := rootVector_ne_zero μ hμ i
  rw [← rootVector_mul_self μ i]
  field_simp

theorem edgeVector_second_diagonal (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (i : V) :
    (∑ e ∈ homogeneousPart k G,
      edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e i) = k := by
  have h : (∑ e ∈ homogeneousPart k G,
      edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e i) =
      (∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) /
        (rootVector μ i * rootVector μ i) := by
    simp only [edgeVector, Finset.sum_filter, div_eq_mul_inv, _root_.mul_inv_rev, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : i ∈ e
    · simp only [hi, ↓reduceIte]
      ring
    · simp [hi]
  rw [h, edgeWeight_mem_sum, stationary_partial μ hc i, rootVector_mul_self]
  have hi := ne_of_gt (hμ i)
  field_simp

theorem monomial_pair_factor (e : Finset V) {i j : V}
    (hi : i ∈ e) (hj : j ∈ e) (hij : i ≠ j) (x : V → ℝ) :
    monomial e x = x i * x j * monomial ((e.erase i).erase j) x := by
  rw [monomial_erase_factor e hi, monomial_erase_factor (e.erase i)
    (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)]
  ring

theorem edgeWeight_pair_sum (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    {i j : V} (hij : i ≠ j) :
    (∑ e ∈ (homogeneousPart k G).filter (fun e => i ∈ e ∧ j ∈ e), edgeWeight k G μ e) =
      μ.weights i * μ.weights j * hessianEntry k G i j (μ.weights : V → ℝ) /
        weightPolynomial k G (μ.weights : V → ℝ) := by
  rw [hessianEntry_eq]
  simp only [edgeWeight, Finset.sum_filter, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : i ∈ e <;> by_cases hj : j ∈ e
  · simp only [hi, hj, true_and, ↓reduceIte]
    rw [monomial_pair_factor e hi hj hij]
    split_ifs with h
    · ring
  · simp [hj]
  · simp [hi]
  · simp [hi]

theorem edgeVector_second_offdiagonal (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i) {i j : V} (hij : i ≠ j) :
    (∑ e ∈ homogeneousPart k G,
      edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e j) =
      normalizedHessian k G μ i j / weightPolynomial k G (μ.weights : V → ℝ) := by
  have h : (∑ e ∈ homogeneousPart k G,
      edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e j) =
      (∑ e ∈ (homogeneousPart k G).filter (fun e => i ∈ e ∧ j ∈ e), edgeWeight k G μ e) /
        (rootVector μ i * rootVector μ j) := by
    simp only [edgeVector, Finset.sum_filter, div_eq_mul_inv, _root_.mul_inv_rev, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : i ∈ e <;> by_cases hj : j ∈ e <;> simp [hi, hj] <;> ring
  rw [h, edgeWeight_pair_sum k G μ hij]
  unfold normalizedHessian
  rw [← rootVector_mul_self μ i, ← rootVector_mul_self μ j]
  have hi := rootVector_ne_zero μ hμ i
  have hj := rootVector_ne_zero μ hμ j
  field_simp

theorem edgeVector_second (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (i j : V) :
    (∑ e ∈ homogeneousPart k G,
      edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e j) =
      normalizedHessian k G μ i j / weightPolynomial k G (μ.weights : V → ℝ) +
        if i = j then (k : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp [edgeVector_second_diagonal k G μ hμ hp hc]
  · simp [edgeVector_second_offdiagonal k G μ hμ hij, hij]

theorem covariance_entry (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (i j : V) :
    covariance k G μ i j =
      normalizedHessian k G μ i j / weightPolynomial k G (μ.weights : V → ℝ) +
        (if i = j then (k : ℝ) else 0) - (k : ℝ) ^ 2 * rootVector μ i * rootVector μ j := by
  simp only [covariance, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hs : (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e *
      ((edgeVector μ e i - k * rootVector μ i) * (edgeVector μ e j - k * rootVector μ j))) =
      (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e * edgeVector μ e i * edgeVector μ e j) -
        ((k : ℝ) * rootVector μ j) *
          (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e * edgeVector μ e i) -
        ((k : ℝ) * rootVector μ i) *
          (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e * edgeVector μ e j) +
        ((k : ℝ) ^ 2 * rootVector μ i * rootVector μ j) *
          (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hs, edgeVector_second k G μ hμ hp hc, edgeVector_mean k G μ hμ hp hc,
    edgeVector_mean k G μ hμ hp hc, sum_edgeWeight k G μ hp]
  ring

theorem covariance_eq (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) :
    covariance k G μ = (weightPolynomial k G (μ.weights : V → ℝ))⁻¹ •
      normalizedHessian k G μ + (k : ℝ) • (1 : Matrix V V ℝ) -
      (k : ℝ) ^ 2 • vecMulVec (rootVector μ) (rootVector μ) := by
  ext i j
  rw [covariance_entry k G μ hμ hp hc]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, vecMulVec_apply]
  by_cases hij : i = j <;> simp only [hij, ↓reduceIte, mul_one, mul_zero]
  all_goals rw [div_eq_mul_inv]; ring

theorem normalizedHessian_lower_bound (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial k G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (z : V → ℝ)
    (hz : rootVector μ ⬝ᵥ z = 0) :
    -(k : ℝ) * weightPolynomial k G (μ.weights : V → ℝ) * (z ⬝ᵥ z) ≤
      z ⬝ᵥ (normalizedHessian k G μ *ᵥ z) := by
  have h := (covariance_posSemidef k G μ).dotProduct_mulVec_nonneg z
  rw [covariance_eq k G μ hμ (ne_of_gt hp) hc] at h
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, hz, zero_smul, dotProduct_zero, sub_zero] at h
  simp only [smul_eq_mul, MulOpposite.op_zero, zero_smul, sub_zero] at h
  have h' := mul_nonneg hp.le h
  have hpp : weightPolynomial k G (μ.weights : V → ℝ) *
      (weightPolynomial k G (μ.weights : V → ℝ))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
  simp only [mul_add, mul_sub, mul_zero, sub_zero, ← mul_assoc, hpp, one_mul] at h'
  nlinarith

theorem covariance_projected_eq (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    covariance (d + 1) G μ = (weightPolynomial (d + 1) G (μ.weights : V → ℝ))⁻¹ •
      projectedHessian d G μ + (d + 1 : ℝ) • (1 : Matrix V V ℝ) -
      (d + 1 : ℝ) • vecMulVec (rootVector μ) (rootVector μ) := by
  rw [covariance_eq (d + 1) G μ hμ hp hc]
  ext i j
  simp only [projectedHessian, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem projectedHessian_lower_bound (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) (z : V → ℝ) :
    -(d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) * (z ⬝ᵥ z) ≤
      z ⬝ᵥ (projectedHessian d G μ *ᵥ z) := by
  have h := (covariance_posSemidef (d + 1) G μ).dotProduct_mulVec_nonneg z
  rw [covariance_projected_eq d G μ hμ (ne_of_gt hp) hc] at h
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, rankOne_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, smul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  rw [dotProduct_comm z (rootVector μ)] at h
  have h' := mul_nonneg hp.le h
  have hpp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) *
      (weightPolynomial (d + 1) G (μ.weights : V → ℝ))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
  simp only [mul_add, mul_sub, ← mul_assoc, hpp, one_mul] at h'
  have hnn : 0 ≤ weightPolynomial (d + 1) G (μ.weights : V → ℝ) * (d + 1 : ℝ) *
      (rootVector μ ⬝ᵥ z) ^ 2 :=
    mul_nonneg (mul_nonneg hp.le (by positivity)) (sq_nonneg _)
  nlinarith

theorem quadratic_finset_sum {I : Type*} (s : Finset I) (A : I → Matrix V V ℝ) (z : V → ℝ) :
    z ⬝ᵥ ((∑ i ∈ s, A i) *ᵥ z) = ∑ i ∈ s, z ⬝ᵥ (A i *ᵥ z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]

theorem covariance_quadratic (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) (z : V → ℝ) :
    z ⬝ᵥ (covariance k G μ *ᵥ z) =
      ∑ e ∈ homogeneousPart k G, edgeWeight k G μ e *
        ((edgeVector μ e - (k : ℝ) • rootVector μ) ⬝ᵥ z) ^ 2 := by
  rw [covariance, quadratic_finset_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.smul_mulVec, rankOne_mulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm z (edgeVector μ e - (k : ℝ) • rootVector μ)]
  ring

theorem edgeWeight_pos (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial k G (μ.weights : V → ℝ)) (e : Finset V) :
    0 < edgeWeight k G μ e := by
  apply div_pos _ hp
  exact mul_pos (Nat.cast_pos.mpr k.factorial_pos)
    ((monomial_pos_iff (coordinate_nonneg μ)).mpr fun i _ => hμ i)

/-- A null covariance direction has a separate zero-sum identity on every edge. -/
theorem edge_sum_eq_zero_of_covariance_mulVec_eq_zero (k : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial k G (μ.weights : V → ℝ)) (z : V → ℝ)
    (hz : rootVector μ ⬝ᵥ z = 0) (hker : covariance k G μ *ᵥ z = 0)
    {e : Finset V} (he : e ∈ homogeneousPart k G) :
    ∑ i ∈ e, z i / rootVector μ i = 0 := by
  have hq : (∑ e ∈ homogeneousPart k G, edgeWeight k G μ e *
      ((edgeVector μ e - (k : ℝ) • rootVector μ) ⬝ᵥ z) ^ 2) = 0 := by
    rw [← covariance_quadratic, hker, dotProduct_zero]
  have heq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e (_ : e ∈ homogeneousPart k G) =>
      mul_nonneg (edgeWeight_nonneg k G μ e) (sq_nonneg _))).mp hq e he
  have hcenter : (edgeVector μ e - (k : ℝ) • rootVector μ) ⬝ᵥ z = 0 := by
    exact sq_eq_zero_iff.mp (mul_eq_zero.mp heq |>.resolve_left
      (ne_of_gt (edgeWeight_pos k G μ hμ hp e)))
  rw [sub_dotProduct, smul_dotProduct, hz, smul_eq_mul, mul_zero, sub_zero] at hcenter
  have hs : edgeVector μ e ⬝ᵥ z = ∑ i ∈ e, z i / rootVector μ i := by
    simp only [edgeVector, dotProduct, ite_mul, zero_mul, div_eq_mul_inv]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (· ∈ e) = e := by ext i; simp
    rw [hf]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hs] at hcenter

end SharpTopologicalOverlap.Spectral
