module

public import SharpTopologicalOverlap.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! # The normalized Hessian at a simplex-critical point

These are the stationary identities and the normalized-Hessian calculation in
the first paragraph of the proof of Lemma 4.1. Criticality is stated on the
zero-sum directions in finite coordinates, so no manifold convention is hidden.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix
open SharpTopologicalOverlap.WeightPolynomial Matrix

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Criticality in the affine hyperplane of total mass one. -/
def IsSimplexCritical (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) : Prop :=
  ∀ y : V → ℝ, (∑ i, y i) = 0 → differential k G x y = 0

theorem partial_eq_of_critical {k : ℕ} {G : Finset (Finset V)} {x : V → ℝ}
    (hc : IsSimplexCritical k G x) (i j : V) :
    coordinatePartial k G i x = coordinatePartial k G j x := by
  have hsum : (∑ a : V, (Pi.single i 1 - Pi.single j 1 : V → ℝ) a) = 0 := by
    simp [Finset.sum_sub_distrib]
  have h := hc _ hsum
  rw [map_sub, differential_single, differential_single, sub_eq_zero] at h
  exact h

theorem stationary_partial {k : ℕ} {G : Finset (Finset V)} (μ : Simplex V)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (i : V) :
    coordinatePartial k G i (μ.weights : V → ℝ) =
      (k : ℝ) * weightPolynomial k G (μ.weights : V → ℝ) := by
  have h := euler k G (μ.weights : V → ℝ)
  rw [differential_apply] at h
  have hs : (∑ j, μ.weights j * coordinatePartial k G j (μ.weights : V → ℝ)) =
      coordinatePartial k G i (μ.weights : V → ℝ) := by
    simp_rw [partial_eq_of_critical hc _ i]
    rw [← Finset.sum_mul, sum_coordinates, one_mul]
  rwa [hs] at h

/-- The unit vector with coordinates the square roots of the masses. -/
def rootVector (μ : Simplex V) : V → ℝ := fun i => Real.sqrt (μ.weights i)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem rootVector_sq (μ : Simplex V) (i : V) :
    rootVector μ i ^ 2 = μ.weights i := Real.sq_sqrt (coordinate_nonneg μ i)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem rootVector_mul_self (μ : Simplex V) (i : V) :
    rootVector μ i * rootVector μ i = μ.weights i := by
  simpa only [pow_two] using rootVector_sq μ i

omit [DecidableEq V] in
theorem rootVector_dot_self (μ : Simplex V) : rootVector μ ⬝ᵥ rootVector μ = 1 := by
  simp only [dotProduct, rootVector_mul_self, sum_coordinates]

omit [Fintype V] [DecidableEq V] in
theorem rootVector_ne_zero (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i) (i : V) :
    rootVector μ i ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hμ i))

/-- The Hessian after rescaling coordinates by square roots of the masses. -/
def normalizedHessian (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : Matrix V V ℝ :=
  fun i j => rootVector μ i * rootVector μ j * hessianEntry k G i j (μ.weights : V → ℝ)

theorem normalizedHessian_symm (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (normalizedHessian k G μ).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, normalizedHessian]
  rw [hessianEntry_symm]
  ring

theorem normalizedHessian_isHermitian (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (normalizedHessian k G μ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, normalizedHessian]
  rw [hessianEntry_symm]
  ring

@[simp] theorem normalizedHessian_diagonal (k : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (i : V) : normalizedHessian k G μ i i = 0 := by
  simp [normalizedHessian]

theorem normalizedHessian_trace (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (normalizedHessian k G μ).trace = 0 := by
  simp [Matrix.trace]

theorem hessian_mul_mass (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (k + 1) G (μ.weights : V → ℝ)) (i : V) :
    (∑ j, hessianEntry (k + 1) G i j (μ.weights : V → ℝ) * μ.weights j) =
      (k : ℝ) * (k + 1 : ℝ) * weightPolynomial (k + 1) G (μ.weights : V → ℝ) := by
  have h := partial_euler k G i (μ.weights : V → ℝ)
  rw [partialDifferential_apply, stationary_partial μ hc i] at h
  simpa only [mul_comm, Nat.cast_add, Nat.cast_one, mul_assoc] using h

theorem normalizedHessian_mulVec_root (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (k + 1) G (μ.weights : V → ℝ)) :
    normalizedHessian (k + 1) G μ *ᵥ rootVector μ =
      ((k : ℝ) * (k + 1 : ℝ) * weightPolynomial (k + 1) G (μ.weights : V → ℝ)) •
        rootVector μ := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, normalizedHessian]
  calc
    (∑ j, rootVector μ i * rootVector μ j *
        hessianEntry (k + 1) G i j (μ.weights : V → ℝ) * rootVector μ j) =
        rootVector μ i * ∑ j, hessianEntry (k + 1) G i j (μ.weights : V → ℝ) * μ.weights j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← rootVector_mul_self μ j]
      ring
    _ = _ := by rw [hessian_mul_mass k G μ hc]; ring

theorem normalizedHessian_quadratic (k : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (z : V → ℝ) :
    z ⬝ᵥ (normalizedHessian k G μ *ᵥ z) =
      hessian k G (μ.weights : V → ℝ) (fun i => rootVector μ i * z i)
        (fun i => rootVector μ i * z i) := by
  rw [hessian_apply]
  simp only [dotProduct, Matrix.mulVec, normalizedHessian, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq V] in
theorem rankOne_mulVec (v z : V → ℝ) :
    vecMulVec v v *ᵥ z = (v ⬝ᵥ z) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Remove the positive radial eigenvalue and extend the tangent Hessian by zero. -/
def projectedHessian (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : Matrix V V ℝ :=
  normalizedHessian (d + 1) G μ -
    ((d : ℝ) * (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) •
      vecMulVec (rootVector μ) (rootVector μ)

theorem projectedHessian_trace (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (projectedHessian d G μ).trace =
      -(d : ℝ) * (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) := by
  simp only [projectedHessian, Matrix.trace_sub, normalizedHessian_trace,
    Matrix.trace_smul, Matrix.trace_vecMulVec, rootVector_dot_self, smul_eq_mul, mul_one]
  ring

theorem projectedHessian_mulVec_root (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    projectedHessian d G μ *ᵥ rootVector μ = 0 := by
  rw [projectedHessian, Matrix.sub_mulVec, Matrix.smul_mulVec,
    normalizedHessian_mulVec_root d G μ hc, rankOne_mulVec, rootVector_dot_self,
    one_smul, sub_self]

theorem projectedHessian_mulVec_of_orthogonal (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (z : V → ℝ) (hz : rootVector μ ⬝ᵥ z = 0) :
    projectedHessian d G μ *ᵥ z = normalizedHessian (d + 1) G μ *ᵥ z := by
  rw [projectedHessian, Matrix.sub_mulVec, Matrix.smul_mulVec, rankOne_mulVec, hz,
    zero_smul, smul_zero, sub_zero]

theorem projectedHessian_isHermitian (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (projectedHessian d G μ).IsHermitian := by
  ext i j
  simp only [projectedHessian, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
    vecMulVec_apply, star_trivial, smul_eq_mul, normalizedHessian]
  rw [hessianEntry_symm]
  ring

/-- The square-root change of variables from the paper. -/
def sqrtRescale (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i) :
    (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun x i := x i / rootVector μ i
  invFun z i := rootVector μ i * z i
  left_inv x := by
    ext i
    dsimp
    field_simp [rootVector_ne_zero μ hμ i]
  right_inv z := by
    ext i
    dsimp
    field_simp [rootVector_ne_zero μ hμ i]
  map_add' x y := by ext i; simp [add_div]
  map_smul' a x := by ext i; simp [mul_div_assoc]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem sqrtRescale_apply (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (x : V → ℝ) (i : V) : sqrtRescale μ hμ x i = x i / rootVector μ i := rfl

omit [DecidableEq V] in
theorem sum_eq_root_dot_rescale (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i) (x : V → ℝ) :
    (∑ i, x i) = rootVector μ ⬝ᵥ sqrtRescale μ hμ x := by
  simp only [dotProduct, sqrtRescale_apply]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [rootVector_ne_zero μ hμ i]

theorem sqrtRescale_quadratic (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i) (x : V → ℝ) :
    sqrtRescale μ hμ x ⬝ᵥ (normalizedHessian k G μ *ᵥ sqrtRescale μ hμ x) =
      hessian k G (μ.weights : V → ℝ) x x := by
  rw [normalizedHessian_quadratic]
  have h : (fun i => rootVector μ i * sqrtRescale μ hμ x i) = x := by
    ext i
    simp only [sqrtRescale_apply]
    field_simp [rootVector_ne_zero μ hμ i]
  rw [h]

/-- The simplex's affine tangent space, in finite coordinates. -/
def zeroSumSpace : Submodule ℝ (V → ℝ) where
  carrier := {x | (∑ i, x i) = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro a x hx
    change (∑ i, a * x i) = 0
    rw [← Finset.mul_sum, hx, mul_zero]

/-- The coordinate orthogonal complement of the square-root mass vector. -/
def rootOrthogonal (μ : Simplex V) : Submodule ℝ (V → ℝ) where
  carrier := {z | rootVector μ ⬝ᵥ z = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all [dotProduct_add]
  smul_mem' := by intro a x hx; simp_all [dotProduct_smul]

/-- The actual linear equivalence identifying the two Hessian domains. -/
def sqrtRescaleTangent (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i) :
    zeroSumSpace (V := V) ≃ₗ[ℝ] rootOrthogonal μ where
  toFun x := ⟨sqrtRescale μ hμ x, by
    change rootVector μ ⬝ᵥ sqrtRescale μ hμ x = 0
    rw [← sum_eq_root_dot_rescale]
    exact x.2⟩
  invFun z := ⟨(sqrtRescale μ hμ).symm z, by
    change (∑ i, (sqrtRescale μ hμ).symm z i) = 0
    rw [sum_eq_root_dot_rescale μ hμ, LinearEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv x := by apply Subtype.ext; exact (sqrtRescale μ hμ).symm_apply_apply x
  right_inv z := by apply Subtype.ext; exact (sqrtRescale μ hμ).apply_symm_apply z
  map_add' x y := by
    apply Subtype.ext
    exact map_add (sqrtRescale μ hμ) (x : V → ℝ) (y : V → ℝ)
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (sqrtRescale μ hμ) a (x : V → ℝ)

end SharpTopologicalOverlap.Spectral
