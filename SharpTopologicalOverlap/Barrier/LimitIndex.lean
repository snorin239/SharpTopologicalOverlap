module

public import SharpTopologicalOverlap.Barrier.Basic
public import SharpTopologicalOverlap.Spectral.FaceRestriction
public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity

/-! # Persistence of the negative index on a fixed support face

Only the coordinates positive at the limit enter the varying diagonal term.
The full barrier Hessians are not claimed to converge when coordinates vanish.
-/

@[expose] public noncomputable section

open scoped Topology ContDiff
open Filter SharpTopologicalOverlap.Spectral SharpTopologicalOverlap.WeightPolynomial

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

namespace SharpTopologicalOverlap.Barrier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Include the tangent space of one support face in the full zero-sum tangent space. -/
def faceToZeroSum (S : Finset V) : faceTangentSpace S →ₗ[ℝ] zeroSumSpace (V := V) where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A coordinate functional on the fixed face tangent space. -/
def faceProjection (S : Finset V) (i : V) : faceTangentSpace S →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (faceTangentSpace S).subtypeL

@[simp] theorem faceProjection_apply (S : Finset V) (i : V) (x : faceTangentSpace S) :
    faceProjection S i x = x.1 i := rfl

/-- The restricted Hessian family, with a diagonal correction only on the
fixed support face. This family is continuous at `(0,μ)`. -/
def supportHessianFamily (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (p : ℝ × Simplex V) :
    faceTangentSpace (support μ) →L[ℝ] (faceTangentSpace (support μ) →L[ℝ] ℝ) :=
  let H : faceTangentSpace (support μ) →L[ℝ] (faceTangentSpace (support μ) →L[ℝ] ℝ) :=
    (hessian (d + 1) G (p.2.weights : V → ℝ)).bilinearComp
      (faceTangentSpace (support μ)).subtypeL (faceTangentSpace (support μ)).subtypeL
  let D : faceTangentSpace (support μ) →L[ℝ] (faceTangentSpace (support μ) →L[ℝ] ℝ) :=
    ∑ i ∈ support μ, ((p.2.weights i) ^ 2)⁻¹ •
      (faceProjection (support μ) i).smulRight (faceProjection (support μ) i)
  H + p.1 • D

theorem supportHessianFamily_apply (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V)
    (p : ℝ × Simplex V) (x y : faceTangentSpace (support μ)) :
    supportHessianFamily d G μ p x y =
      hessian (d + 1) G (p.2.weights : V → ℝ) x.1 y.1 +
        p.1 * ∑ i ∈ support μ, x.1 i * y.1 i / p.2.weights i ^ 2 := by
  simp only [supportHessianFamily, add_apply, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.smulRight_apply,
    faceProjection_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring

theorem supportHessianFamily_eq_barrier_pullback (d : ℕ) (G : Finset (Finset V))
    (μ : Simplex V) (ε : ℝ) (ν : Simplex V) :
    (supportHessianFamily d G μ (ε, ν)).toBilinForm.toQuadraticMap =
      (barrierTangentForm d G ε ν).comp (faceToZeroSum (support μ)) := by
  ext x
  change supportHessianFamily d G μ (ε, ν) x x =
    barrierHessian d G ε (ν.weights : V → ℝ) x.1 x.1
  rw [supportHessianFamily_apply, barrierHessian_apply]
  congr 2
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [x.2.1 i hi, zero_mul, zero_div]

theorem supportHessianFamily_zero (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    (supportHessianFamily d G μ (0, μ)).toBilinForm.toQuadraticMap = faceHessianForm d G μ := by
  ext x
  change supportHessianFamily d G μ (0, μ) x x =
    hessian (d + 1) G (μ.weights : V → ℝ) x.1 x.1
  rw [supportHessianFamily_apply, zero_mul, add_zero]

theorem continuous_hessian (k : ℕ) (G : Finset (Finset V)) :
    Continuous (hessian k G) := by
  have h := ((WeightPolynomial.contDiff k G 2).fderiv_right (m := 1) (by norm_num)).continuous_fderiv
    (by norm_num)
  have heq : hessian k G = fderiv ℝ (fderiv ℝ (weightPolynomial k G)) :=
    funext fun x => hessian_eq_fderiv_fderiv k G x
  rwa [heq]

theorem continuousAt_supportHessianFamily (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    ContinuousAt (supportHessianFamily d G μ) (0, μ) := by
  refine (continuousAt_clm_apply (𝕜 := ℝ) (E := faceTangentSpace (support μ))
    (F := faceTangentSpace (support μ) →L[ℝ] ℝ)
    (f := supportHessianFamily d G μ)).mpr ?_
  intro x
  refine (continuousAt_clm_apply (𝕜 := ℝ) (E := faceTangentSpace (support μ)) (F := ℝ)
    (f := fun p => supportHessianFamily d G μ p x)).mpr ?_
  intro y
  simp only [supportHessianFamily_apply]
  apply ContinuousAt.add
  · exact ((((continuous_hessian (d + 1) G).comp
      (coordinateHomeomorph.continuous.subtype_val.comp continuous_snd)).continuousAt.clm_apply
        continuousAt_const).clm_apply continuousAt_const)
  · apply continuousAt_fst.mul
    apply tendsto_finsetSum
    intro i hi
    have hpos : 0 < μ.weights i := mem_support_iff_coordinate_pos.mp hi
    exact continuousAt_const.div (((continuous_coordinate i).comp continuous_snd).continuousAt.pow 2)
      (pow_ne_zero 2 (ne_of_gt hpos))

/-- Local index persistence with the limit support held fixed. -/
theorem eventually_faceIndex_le_barrierIndex (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    ∀ᶠ p : ℝ × Simplex V in 𝓝 (0, μ),
      sigNeg (faceHessianForm d G μ) ≤ sigNeg (barrierTangentForm d G p.1 p.2) := by
  have h := ContinuousLinearMap.eventually_sigNeg_toBilinForm_le_of_continuousAt
    (E := faceTangentSpace (support μ))
    (continuousAt_supportHessianFamily d G μ)
  rw [supportHessianFamily_zero] at h
  filter_upwards [h] with p hp
  apply hp.trans
  rw [supportHessianFamily_eq_barrier_pullback]
  exact sigNeg_comp_le _ _

/-- Filter version for the compactness argument of Lemma 5.7. -/
theorem eventually_faceIndex_le_barrierIndex_of_tendsto {ι : Type*} {l : Filter ι}
    (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) {ε : ι → ℝ} {ν : ι → Simplex V}
    (hε : Tendsto ε l (𝓝 0)) (hν : Tendsto ν l (𝓝 μ)) :
    ∀ᶠ i in l, sigNeg (faceHessianForm d G μ) ≤ sigNeg (barrierTangentForm d G (ε i) (ν i)) :=
  (hε.prodMk_nhds hν).eventually (eventually_faceIndex_le_barrierIndex d G μ)

end SharpTopologicalOverlap.Barrier
