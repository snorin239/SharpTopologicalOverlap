module

public import SharpTopologicalOverlap.Spectral.FaceRestriction.Family
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # First and second derivatives after restricting to a face -/

@[expose] public noncomputable section

open scoped BigOperators
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem differential_faceFamily {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (S : Finset V) (x : S → ℝ) :
    differential k (faceFamily S G) x =
      (differential k G (extendCoordinates S x)).comp (extendCoordinatesCLM S) := by
  have heq : (fun y : S → ℝ => weightPolynomial k G (extendCoordinatesCLM S y)) =
      weightPolynomial k (faceFamily S G) := by
    funext y
    exact (weightPolynomial_faceFamily hG S y).symm
  have hc := (WeightPolynomial.hasFDerivAt k G (extendCoordinates S x)).comp x
    (extendCoordinatesCLM S).hasFDerivAt
  change HasFDerivAt (fun y : S → ℝ => weightPolynomial k G (extendCoordinatesCLM S y))
    ((differential k G (extendCoordinates S x)).comp (extendCoordinatesCLM S)) x at hc
  rw [heq] at hc
  exact (WeightPolynomial.hasFDerivAt k (faceFamily S G) x).unique hc

theorem differential_faceFamily_apply {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (S : Finset V) (x y : S → ℝ) :
    differential k (faceFamily S G) x y =
      differential k G (extendCoordinates S x) (extendCoordinates S y) := by
  exact congrArg (fun L : (S → ℝ) →L[ℝ] ℝ => L y) (differential_faceFamily hG S x)

theorem hessian_faceFamily {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (S : Finset V) (x y z : S → ℝ) :
    hessian k (faceFamily S G) x y z =
      hessian k G (extendCoordinates S x) (extendCoordinates S y) (extendCoordinates S z) := by
  have heq : (fun w : S → ℝ => differential k (faceFamily S G) w z) =
      fun w : S → ℝ => differential k G (extendCoordinatesCLM S w) (extendCoordinates S z) := by
    funext w
    exact differential_faceFamily_apply hG S w z
  have hleft := (hasFDerivAt_differential k (faceFamily S G) x).clm_apply
    (hasFDerivAt_const z x)
  have hright := ((hasFDerivAt_differential k G (extendCoordinates S x)).comp x
    (extendCoordinatesCLM S).hasFDerivAt).clm_apply
    (hasFDerivAt_const (extendCoordinates S z) x)
  change HasFDerivAt (fun w : S → ℝ =>
    differential k G (extendCoordinatesCLM S w) (extendCoordinates S z)) _ x at hright
  rw [← heq] at hright
  have h := congrArg (fun L : (S → ℝ) →L[ℝ] ℝ => L y) (hleft.unique hright)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    extendCoordinatesCLM_apply] using h

/-- The Hessian restricted to the actual open face containing `μ`. -/
def faceHessianForm (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    QuadraticForm ℝ (faceTangentSpace (support μ)) :=
  ((hessian (d + 1) G (μ.weights : V → ℝ)).toBilinForm.toQuadraticMap).restrict
    (faceTangentSpace (support μ))

/-- Face-criticality uses exactly the tangent domain of the paper. -/
def IsFaceCritical (d : ℕ) (G : Finset (Finset V)) (μ : Simplex V) : Prop :=
  ∀ x : faceTangentSpace (support μ), differential (d + 1) G (μ.weights : V → ℝ) x = 0

theorem tangentHessianForm_faceFamily_eq_comp {d : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) :
    tangentHessianForm d (faceFamily (support μ) G) (supportPoint μ) =
      (faceHessianForm d G μ).comp (faceTangentEquiv (support μ)).toLinearMap := by
  ext x
  change hessian (d + 1) (faceFamily (support μ) G)
      ((supportPoint μ).weights : support μ → ℝ) x.1 x.1 =
    hessian (d + 1) G (μ.weights : V → ℝ)
      (extendCoordinates (support μ) x.1) (extendCoordinates (support μ) x.1)
  rw [hessian_faceFamily hG, extend_supportPoint]

theorem sigNeg_faceHessianForm {d : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) :
    sigNeg (faceHessianForm d G μ) =
      sigNeg (tangentHessianForm d (faceFamily (support μ) G) (supportPoint μ)) := by
  rw [tangentHessianForm_faceFamily_eq_comp hG μ, sigNeg_comp_linearEquiv]

theorem faceCritical_supportPoint {d : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) (hc : IsFaceCritical d G μ) :
    IsSimplexCritical (d + 1) (faceFamily (support μ) G)
      ((supportPoint μ).weights : support μ → ℝ) := by
  intro y hy
  rw [differential_faceFamily_apply hG, extend_supportPoint]
  exact hc (faceTangentEquiv (support μ) ⟨y, hy⟩)

end SharpTopologicalOverlap.Spectral
