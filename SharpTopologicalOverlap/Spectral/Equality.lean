module

public import SharpTopologicalOverlap.Spectral.Covariance
public import SharpTopologicalOverlap.Spectral.Exchange
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Equality vectors from the projected Hessian

The two-value spectrum makes a normalized negative Hessian an orthogonal
projection. Its rows provide the labels needed for the cocycle exchange proof;
no choice of a basis of a fixed-dimensional negative eigenspace is required.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix
open SharpTopologicalOverlap.WeightPolynomial Matrix

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem square_eq_neg_smul_of_two_value_spectrum {A : Matrix V V ℝ}
    (hA : A.IsHermitian) (κ : ℝ)
    (hspec : ∀ a, hA.eigenvalues a = if hA.eigenvalues a < 0 then -κ else 0) :
    A * A = (-κ) • A := by
  let D : Matrix V V ℝ := diagonal hA.eigenvalues
  let α := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
  have hdiag : D * D = (-κ) • D := by
    dsimp [D]
    rw [diagonal_mul_diagonal, ← diagonal_smul]
    congr 1
    funext i
    change hA.eigenvalues i * hA.eigenvalues i = -κ * hA.eigenvalues i
    have hi := hspec i
    split_ifs at hi <;> rw [hi] <;> ring
  have hdecomp : A = α D := by
    simpa only [D, α, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.spectral_theorem
  calc
    A * A = α D * α D := by rw [← hdecomp]
    _ = α (D * D) := (map_mul α D D).symm
    _ = α ((-κ) • D) := congrArg α hdiag
    _ = (-κ) • α D := map_smul α (-κ) D
    _ = (-κ) • A := by rw [← hdecomp]

/-- The orthogonal projection obtained by dividing the negative Hessian by its eigenvalue. -/
def negativeProjection (κ : ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ := (-κ⁻¹) • A

theorem negativeProjection_mul_self {A : Matrix V V ℝ} {κ : ℝ} (hκ : κ ≠ 0)
    (hA : A * A = (-κ) • A) :
    negativeProjection κ A * negativeProjection κ A = negativeProjection κ A := by
  simp only [negativeProjection, smul_mul_assoc, mul_smul_comm, smul_smul, hA]
  have hs : -κ⁻¹ * (-κ⁻¹ * -κ) = -κ⁻¹ := by field_simp
  rw [hs]

theorem negativeProjection_isHermitian {A : Matrix V V ℝ} (hA : A.IsHermitian) (κ : ℝ) :
    (negativeProjection κ A).IsHermitian := by
  exact hA.smul (show IsSelfAdjoint (-κ⁻¹) from rfl)

/-- The label attached to a vertex by a symmetric projection matrix. -/
def projectionLabel (P : Matrix V V ℝ) (μ : Simplex V) (i : V) : V → ℝ :=
  fun a => P i a / rootVector μ i

theorem projectionLabel_dot {P : Matrix V V ℝ} (hP : P.IsHermitian)
    (hid : P * P = P) (μ : Simplex V) (i j : V) :
    projectionLabel P μ i ⬝ᵥ projectionLabel P μ j =
      P i j / (rootVector μ i * rootVector μ j) := by
  have hs : (∑ a, P i a * P j a) = P i j := by
    have h := congrFun (congrFun hid i) j
    simp only [Matrix.mul_apply] at h
    have hsym : ∀ a, P a j = P j a := by
      intro a
      have h' := congrFun (congrFun hP a) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using h'.symm
    simpa only [hsym] using h
  simp only [projectionLabel, dotProduct, div_mul_div_comm, ← Finset.sum_div, hs]

/-- The specific projection used by the equality case of Lemma 4.1. -/
def equalityProjection (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : Matrix V V ℝ :=
  negativeProjection ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (projectedHessian d G μ)

def equalityLabel (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : V → (V → ℝ) :=
  projectionLabel (equalityProjection d G μ) μ

theorem equalityProjection_isHermitian (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (equalityProjection d G μ).IsHermitian :=
  negativeProjection_isHermitian (projectedHessian_isHermitian d G μ) _

theorem equalityProjection_mul_self (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hpoly : projectedHessian d G μ * projectedHessian d G μ =
      (-((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ))) •
        projectedHessian d G μ) :
    equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ := by
  exact negativeProjection_mul_self (mul_ne_zero (by positivity) hp) hpoly

theorem equalityLabel_pair_hessian (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hid : equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ)
    (i j : V) :
    hessianEntry (d + 1) G i j (μ.weights : V → ℝ) =
      ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) *
        ((d : ℝ) - equalityLabel d G μ i ⬝ᵥ equalityLabel d G μ j) := by
  unfold equalityLabel
  rw [projectionLabel_dot (equalityProjection_isHermitian d G μ) hid]
  simp only [equalityProjection, negativeProjection, projectedHessian,
    Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, normalizedHessian, smul_eq_mul]
  have hi := rootVector_ne_zero μ hμ i
  have hj := rootVector_ne_zero μ hμ j
  have hk : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem equalityLabel_dot_self (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hid : equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ)
    (i : V) : equalityLabel d G μ i ⬝ᵥ equalityLabel d G μ i = d := by
  have h := equalityLabel_pair_hessian d G μ hμ hp hid i i
  rw [hessianEntry_diagonal] at h
  have hk : (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0 :=
    mul_ne_zero (by positivity) hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hk) |>.symm

theorem hessianEntry_pos_of_edge {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    {e : Finset V} (he : e ∈ G) {i j : V} (hi : i ∈ e) (hj : j ∈ e) (hij : i ≠ j) :
    0 < hessianEntry k G i j (μ.weights : V → ℝ) := by
  rw [hessianEntry_eq]
  apply mul_pos (Nat.cast_pos.mpr k.factorial_pos)
  apply Finset.sum_pos'
  · intro s _
    split_ifs
    · exact monomial_nonneg (coordinate_nonneg μ)
    · exact le_rfl
  · refine ⟨e, mem_homogeneousPart.mpr ⟨he, hG e he⟩, ?_⟩
    rw [if_pos ⟨hi, hj, hij⟩]
    exact (monomial_pos_iff (coordinate_nonneg μ)).mpr fun a _ => hμ a

theorem equalityLabel_injOn_edge (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hid : equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ)
    {e : Finset V} (he : e ∈ G) : Set.InjOn (equalityLabel d G μ) (e : Set V) := by
  intro i hi j hj hlabel
  by_contra hij
  have hpos := hessianEntry_pos_of_edge hG μ hμ he hi hj hij
  have hpair := equalityLabel_pair_hessian d G μ hμ hp hid i j
  rw [hlabel, equalityLabel_dot_self d G μ hμ hp hid, sub_self, mul_zero] at hpair
  exact (ne_of_gt hpos) hpair

theorem equalityProjection_mulVec_root (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    equalityProjection d G μ *ᵥ rootVector μ = 0 := by
  simp only [equalityProjection, negativeProjection, Matrix.smul_mulVec,
    projectedHessian_mulVec_root d G μ hc, smul_zero]

theorem projectedHessian_eq_neg_smul_projection (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0) :
    projectedHessian d G μ =
      (-((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ))) •
        equalityProjection d G μ := by
  unfold equalityProjection negativeProjection
  rw [smul_smul]
  have hk : (d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0 :=
    mul_ne_zero (by positivity) hp
  rw [neg_mul_neg, mul_inv_cancel₀ hk, one_smul]

theorem equalityProjection_column_orthogonal (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) (a : V) :
    rootVector μ ⬝ᵥ (equalityProjection d G μ *ᵥ Pi.single a 1) = 0 := by
  let P := equalityProjection d G μ
  have hP := equalityProjection_isHermitian d G μ
  have hroot := congrFun (equalityProjection_mulVec_root d G μ hc) a
  simp only [Matrix.mulVec_single_one, dotProduct]
  calc
    (∑ i, rootVector μ i * P i a) = ∑ i, P a i * rootVector μ i := by
      apply Finset.sum_congr rfl
      intro i _
      have hs := congrFun (congrFun hP i) a
      simp only [Matrix.conjTranspose_apply, star_trivial] at hs
      change rootVector μ i * equalityProjection d G μ i a =
        equalityProjection d G μ a i * rootVector μ i
      rw [hs]
      ring
    _ = 0 := hroot

theorem covariance_mulVec_projection_column (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hp : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ))
    (hid : equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ)
    (a : V) : covariance (d + 1) G μ *ᵥ
      (equalityProjection d G μ *ᵥ Pi.single a 1) = 0 := by
  let z := equalityProjection d G μ *ᵥ Pi.single a 1
  have hz : rootVector μ ⬝ᵥ z = 0 := equalityProjection_column_orthogonal d G μ hc a
  have hAz : projectedHessian d G μ *ᵥ z =
      (-((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ))) • z := by
    rw [projectedHessian_eq_neg_smul_projection d G μ hp, Matrix.smul_mulVec]
    change _ • (equalityProjection d G μ *ᵥ (equalityProjection d G μ *ᵥ Pi.single a 1)) = _
    rw [Matrix.mulVec_mulVec, hid]
  change covariance (d + 1) G μ *ᵥ z = 0
  rw [covariance_projected_eq d G μ hμ hp hc, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    rankOne_mulVec, hz, zero_smul, smul_zero, sub_zero, hAz, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  field_simp
  ring

theorem equalityLabel_sum_edge (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ))
    (hid : equalityProjection d G μ * equalityProjection d G μ = equalityProjection d G μ)
    {e : Finset V} (he : e ∈ G) : ∑ i ∈ e, equalityLabel d G μ i = 0 := by
  ext a
  have h := edge_sum_eq_zero_of_covariance_mulVec_eq_zero (d + 1) G μ hμ hp
    (equalityProjection d G μ *ᵥ Pi.single a 1)
    (equalityProjection_column_orthogonal d G μ hc a)
    (covariance_mulVec_projection_column d G μ hμ (ne_of_gt hp) hc hid a)
    (mem_homogeneousPart.mpr ⟨he, hG e he⟩)
  simpa only [equalityLabel, projectionLabel, Finset.sum_apply, Pi.zero_apply,
    Matrix.mulVec_single_one, Matrix.col_apply] using h

end SharpTopologicalOverlap.Spectral
