module

public import SharpTopologicalOverlap.Spectral.Counting
public import SharpTopologicalOverlap.Spectral.Restriction
public import SharpTopologicalOverlap.Spectral.Covariance
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # The negative index of the actual tangent Hessian

The projected matrix is transported to Euclidean space only to invoke the
library spectral theorem. Its kernel direction is then removed by a linear
retraction, and the square-root coordinate change identifies the remaining
form with the Hessian on the simplex's zero-sum tangent space.
-/

@[expose] public noncomputable section

open scoped Matrix InnerProductSpace
open Matrix SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Spectral

theorem negativeCount_reindex {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℝ) (e : J ≃ I) : negativeCount (fun j => a (e j)) = negativeCount a := by
  classical
  unfold negativeCount
  apply Finset.card_bij (fun j _ => e j)
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro i _ j _ hij
    exact e.injective hij
  · intro i hi
    refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, e.apply_symm_apply] using hi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary finite-coordinate quadratic form of a matrix. -/
def coordinateMatrixForm (M : Matrix V V ℝ) : QuadraticForm ℝ (V → ℝ) :=
  (Matrix.toBilin' M).toQuadraticMap

@[simp] theorem coordinateMatrixForm_apply (M : Matrix V V ℝ) (z : V → ℝ) :
    coordinateMatrixForm M z = z ⬝ᵥ (M *ᵥ z) :=
  Matrix.toBilin'_apply' M z z

/-- The same form on the Euclidean presentation of finite coordinates. -/
def euclideanMatrixForm (M : Matrix V V ℝ) : QuadraticForm ℝ (EuclideanSpace ℝ V) :=
  (coordinateMatrixForm M).comp (euclideanCoordinates (V := V)).symm.toLinearEquiv.toLinearMap

@[simp] theorem euclideanMatrixForm_apply (M : Matrix V V ℝ) (z : EuclideanSpace ℝ V) :
    euclideanMatrixForm M z = (WithLp.ofLp z) ⬝ᵥ (M *ᵥ (WithLp.ofLp z)) := by
  change coordinateMatrixForm M (WithLp.ofLp z) = _
  exact coordinateMatrixForm_apply M _

theorem euclideanMatrixForm_eq_inner (M : Matrix V V ℝ) (z : EuclideanSpace ℝ V) :
    euclideanMatrixForm M z = ⟪M.toEuclideanLin z, z⟫_ℝ := by
  simp only [euclideanMatrixForm_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, star_trivial]

theorem sigNeg_euclideanMatrixForm (M : Matrix V V ℝ) :
    sigNeg (euclideanMatrixForm M) = sigNeg (coordinateMatrixForm M) :=
  sigNeg_comp_linearEquiv _ _

theorem negativeCount_matrixEigenvalues (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    negativeCount hM.eigenvalues = sigNeg (coordinateMatrixForm M) := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  calc
    negativeCount hM.eigenvalues = negativeCount hM.eigenvalues₀ :=
      negativeCount_reindex _ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    _ = sigNeg (euclideanMatrixForm M) :=
      negativeCount_eigenvalues_eq_sigNeg hsym finrank_euclideanSpace
        (euclideanMatrixForm_eq_inner M)
    _ = sigNeg (coordinateMatrixForm M) := sigNeg_euclideanMatrixForm M

/-- Orthogonal projection onto the coordinate complement of the square-root
mass vector, which has squared length one. -/
def rootProjection (μ : Simplex V) : (V → ℝ) →ₗ[ℝ] rootOrthogonal μ := by
  let l : (V → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => rootVector μ ⬝ᵥ z
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun a z => by simp [dotProduct_smul] }
  let P : (V → ℝ) →ₗ[ℝ] (V → ℝ) := LinearMap.id - l.smulRight (rootVector μ)
  exact P.codRestrict (rootOrthogonal μ) (fun z => by
    change rootVector μ ⬝ᵥ (z - (rootVector μ ⬝ᵥ z) • rootVector μ) = 0
    rw [dotProduct_sub, dotProduct_smul, rootVector_dot_self]
    simp)

@[simp] theorem rootProjection_apply (μ : Simplex V) (z : V → ℝ) :
    (rootProjection μ z).1 = z - (rootVector μ ⬝ᵥ z) • rootVector μ := rfl

theorem projectedForm_factors (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) (z : V → ℝ) :
    coordinateMatrixForm (projectedHessian d G μ) z =
      coordinateMatrixForm (projectedHessian d G μ) (rootProjection μ z).1 := by
  let M := projectedHessian d G μ
  have hkernel : M *ᵥ rootVector μ = 0 := projectedHessian_mulVec_root d G μ hc
  have htrans : Mᵀ = M := by
    exact (projectedHessian_isHermitian d G μ).isSymm
  have himage : rootVector μ ⬝ᵥ (M *ᵥ z) = 0 := by
    rw [← htrans, dotProduct_transpose_mulVec, hkernel, dotProduct_zero]
  rw [coordinateMatrixForm_apply, coordinateMatrixForm_apply, rootProjection_apply,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hkernel, smul_zero, sub_zero,
    sub_dotProduct, smul_dotProduct, himage, smul_zero, sub_zero]

theorem sigNeg_projected_eq_restrict (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    sigNeg (coordinateMatrixForm (projectedHessian d G μ)) =
      sigNeg ((coordinateMatrixForm (projectedHessian d G μ)).restrict (rootOrthogonal μ)) :=
  (sigNeg_restrict_eq_of_factor _ _ (rootProjection μ) (projectedForm_factors d G μ hc)).symm

/-- The actual second derivative, restricted to the affine simplex tangent space. -/
def tangentHessianForm (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    QuadraticForm ℝ (zeroSumSpace (V := V)) :=
  ((hessian (d + 1) G (μ.weights : V → ℝ)).toBilinForm.toQuadraticMap).restrict zeroSumSpace

@[simp] theorem tangentHessianForm_apply (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (x : zeroSumSpace (V := V)) :
    tangentHessianForm d G μ x = hessian (d + 1) G (μ.weights : V → ℝ) x.1 x.1 := rfl

theorem tangentHessianForm_eq_comp (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i) :
    tangentHessianForm d G μ =
      ((coordinateMatrixForm (projectedHessian d G μ)).restrict (rootOrthogonal μ)).comp
        (sqrtRescaleTangent μ hμ).toLinearMap := by
  ext x
  change hessian (d + 1) G (μ.weights : V → ℝ) x.1 x.1 =
    coordinateMatrixForm (projectedHessian d G μ) (sqrtRescale μ hμ x.1)
  rw [coordinateMatrixForm_apply, projectedHessian_mulVec_of_orthogonal]
  · exact (sqrtRescale_quadratic (d + 1) G μ hμ x.1).symm
  · rw [← sum_eq_root_dot_rescale]
    exact x.2

theorem sigNeg_tangent_eq_projected (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    sigNeg (tangentHessianForm d G μ) = sigNeg (coordinateMatrixForm (projectedHessian d G μ)) := by
  rw [tangentHessianForm_eq_comp d G μ hμ, sigNeg_comp_linearEquiv]
  exact (sigNeg_projected_eq_restrict d G μ hc).symm

/-- Matrix eigenvalues obey a lower quadratic-form bound. -/
theorem matrixEigenvalues_lower_of_form_lower (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (κ : ℝ) (hlower : ∀ z : V → ℝ, -κ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (M *ᵥ z)) :
    ∀ i, -κ ≤ hM.eigenvalues i := by
  intro i
  let z : V → ℝ := hM.eigenvectorBasis i
  have hunit : z ⬝ᵥ z = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ite_true, z] using
      orthonormal_iff_ite.mp hM.eigenvectorBasis.orthonormal i i
  have hi := hlower z
  rw [hM.mulVec_eigenvectorBasis i, dotProduct_smul, hunit] at hi
  simpa only [smul_eq_mul, mul_one] using hi

theorem projected_eigenvalues_lower (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    ∀ i, -((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) ≤
      (projectedHessian_isHermitian d G μ).eigenvalues i := by
  apply matrixEigenvalues_lower_of_form_lower
  intro z
  simpa only [neg_mul] using projectedHessian_lower_bound d G μ hμ hp hc z

theorem projected_eigenvalues_sum (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (∑ i, (projectedHessian_isHermitian d G μ).eigenvalues i) =
      -(d : ℝ) * ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) := by
  have htrace := (projectedHessian_isHermitian d G μ).trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at htrace
  rw [← htrace, projectedHessian_trace]
  ring

/-- The index lower bound in Lemma 4.1, on the actual restricted Hessian.
This part of the argument requires positivity and criticality; cocycle parity
is used later in the rigidity of the equality case. -/
theorem tangentNegativeIndex_ge (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    d ≤ sigNeg (tangentHessianForm d G μ) := by
  rw [sigNeg_tangent_eq_projected d G μ hμ hc,
    ← negativeCount_matrixEigenvalues _ (projectedHessian_isHermitian d G μ)]
  apply le_negativeCount_of_sum _
    ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) d
  · exact mul_pos (by positivity) hp
  · exact projected_eigenvalues_lower d G μ hμ hp hc
  · exact projected_eigenvalues_sum d G μ

/-- Equality in the tangent-index bound forces the two-value spectrum of the
full projected Hessian, including its added zero radial direction. -/
theorem projected_eigenvalues_eq_of_tangentIndex_eq (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ))
    (hindex : sigNeg (tangentHessianForm d G μ) = d) :
    ∀ i, (projectedHessian_isHermitian d G μ).eigenvalues i =
      if (projectedHessian_isHermitian d G μ).eigenvalues i < 0 then
        -((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) else 0 := by
  apply spectrum_eq_of_negativeCount_eq _
    ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) d
  · exact projected_eigenvalues_lower d G μ hμ hp hc
  · exact projected_eigenvalues_sum d G μ
  · rw [negativeCount_matrixEigenvalues,
      ← sigNeg_tangent_eq_projected d G μ hμ hc]
    exact hindex

end SharpTopologicalOverlap.Spectral
