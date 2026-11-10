module

public import SharpTopologicalOverlap.Barrier.Coordinates
public import SharpTopologicalOverlap.Spectral.Index
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-! # The open-simplex Morse adapter

The canonical chart of an open subset of a normed space is locally its
inclusion. The first results expose this fact at both derivative orders,
so the Morse index convention is exactly the ordinary Hessian convention.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold Topology
open Filter TauCeti
open SharpTopologicalOverlap.Spectral SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Barrier

section OpenSubtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The preferred chart of an open subspace agrees locally with inclusion. -/
theorem openSubtype_coordinate_germ (U : TopologicalSpace.Opens E) (F : E → ℝ) (x : U) :
    (F ∘ Subtype.val) ∘ (extChartAt 𝓘(ℝ, E) x).symm =ᶠ[𝓝 x.1] F := by
  have h := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := E) U (x := x)
  have h' : (id : E → E) =ᶠ[𝓝 x.1] Subtype.val ∘ (chartAt E x).symm := by
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq] using h
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → U) = (chartAt E x).symm := by
    ext y
    simp
  rw [hext]
  filter_upwards [h'] with y hy
  change F ((Subtype.val ∘ (chartAt E x).symm) y) = F y
  change y = (Subtype.val ∘ (chartAt E x).symm) y at hy
  rw [← hy]

@[simp] theorem openSubtype_chart_point (U : TopologicalSpace.Opens E) (x : U) :
    extChartAt 𝓘(ℝ, E) x x = x.1 := by
  rfl

/-- Manifold criticality on an open subtype is ordinary criticality of its
ambient coordinate expression. -/
theorem openSubtype_fderiv_coordinate (U : TopologicalSpace.Opens E) (F : E → ℝ) (x : U) :
    fderiv ℝ ((F ∘ Subtype.val) ∘ (extChartAt 𝓘(ℝ, E) x).symm)
      (extChartAt 𝓘(ℝ, E) x x) = fderiv ℝ F x.1 := by
  rw [openSubtype_chart_point]
  exact (openSubtype_coordinate_germ U F x).fderiv_eq

/-- Both derivative orders agree with the ambient function in the canonical chart. -/
theorem openSubtype_criticalHessian (U : TopologicalSpace.Opens E) (F : E → ℝ) (x : U) :
    criticalHessian 𝓘(ℝ, E) (F ∘ Subtype.val) x = fderiv ℝ (fderiv ℝ F) x.1 := by
  rw [criticalHessian_def, openSubtype_chart_point]
  exact (openSubtype_coordinate_germ U F x).fderiv.fderiv_eq

/-- TauCeti's manifold index on the open subtype is the negative index of the
ordinary second derivative, without a scale or sign conversion. -/
theorem openSubtype_manifoldMorseIndex (U : TopologicalSpace.Opens E) (F : E → ℝ) (x : U) :
    manifoldMorseIndex 𝓘(ℝ, E) (F ∘ Subtype.val) x =
      sigNeg (fderiv ℝ (fderiv ℝ F) x.1).toBilinForm.toQuadraticMap := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, openSubtype_criticalHessian]
  rfl

end OpenSubtype

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem hasFDerivAt_affineCoordinates (z : euclideanZeroSumSpace (V := V)) :
    HasFDerivAt affineCoordinates tangentCoordinates z := by
  simpa only [affineCoordinates, zero_add] using!
    (hasFDerivAt_const ((uniform : Simplex V).weights : V → ℝ) z).add
      (tangentCoordinates (V := V)).hasFDerivAt

theorem fderiv_affineCoordinates (z : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ affineCoordinates z = tangentCoordinates :=
  (hasFDerivAt_affineCoordinates z).fderiv

theorem contDiff_affineCoordinates (n : ℕ∞ω) :
    ContDiff ℝ n (affineCoordinates (V := V)) :=
  contDiff_const.add (tangentCoordinates (V := V)).contDiff

theorem second_fderiv_affineCoordinates (z : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (fderiv ℝ affineCoordinates) z = 0 := by
  have hD : fderiv ℝ (affineCoordinates (V := V)) = fun _ => tangentCoordinates :=
    funext fderiv_affineCoordinates
  rw [hD]
  exact (hasFDerivAt_const (𝕜 := ℝ) (tangentCoordinates (V := V)) z).fderiv

/-- The ordinary second-order chain rule for the translated affine chart. -/
theorem second_derivative_comp_affine (F : (V → ℝ) → ℝ)
    (z : euclideanZeroSumSpace (V := V))
    (hF : ContDiffAt ℝ 2 F (affineCoordinates z))
    (x y : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (fderiv ℝ (F ∘ affineCoordinates)) z x y =
      fderiv ℝ (fderiv ℝ F) (affineCoordinates z)
        (tangentCoordinates x) (tangentCoordinates y) := by
  have h := TauCeti.fderiv_fderiv_comp_apply hF
    (contDiff_affineCoordinates 2).contDiffAt x y
  simpa only [fderiv_affineCoordinates, second_fderiv_affineCoordinates,
    ContinuousLinearMap.zero_apply, map_zero, add_zero] using h

/-- The weight polynomial in the Euclidean zero-sum affine chart. -/
def coordinatePolynomial (d : ℕ) (G : Finset (Finset V)) : euclideanZeroSumSpace (V := V) → ℝ :=
  weightPolynomial (d + 1) G ∘ affineCoordinates

theorem contDiff_coordinatePolynomial (d : ℕ) (G : Finset (Finset V)) (n : ℕ∞ω) :
    ContDiff ℝ n (coordinatePolynomial d G) :=
  (WeightPolynomial.contDiff (d + 1) G n).comp (contDiff_affineCoordinates n)

theorem hasFDerivAt_coordinatePolynomial (d : ℕ) (G : Finset (Finset V))
    (z : euclideanZeroSumSpace (V := V)) :
    HasFDerivAt (coordinatePolynomial d G)
      ((differential (d + 1) G (affineCoordinates z)).comp tangentCoordinates) z :=
  (WeightPolynomial.hasFDerivAt (d + 1) G (affineCoordinates z)).comp z
    (hasFDerivAt_affineCoordinates z)

theorem fderiv_coordinatePolynomial (d : ℕ) (G : Finset (Finset V))
    (z : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (coordinatePolynomial d G) z =
      (differential (d + 1) G (affineCoordinates z)).comp tangentCoordinates :=
  (hasFDerivAt_coordinatePolynomial d G z).fderiv

theorem second_fderiv_coordinatePolynomial (d : ℕ) (G : Finset (Finset V))
    (z x y : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (fderiv ℝ (coordinatePolynomial d G)) z x y =
      hessian (d + 1) G (affineCoordinates z) (tangentCoordinates x) (tangentCoordinates y) := by
  rw [coordinatePolynomial, second_derivative_comp_affine _ z
    (WeightPolynomial.contDiff (d + 1) G 2).contDiffAt, ← hessian_eq_fderiv_fderiv]

/-- Vanishing of the Euclidean differential is the paper's affine criticality. -/
theorem coordinatePolynomial_critical_iff (d : ℕ) (G : Finset (Finset V))
    (z : euclideanZeroSumSpace (V := V)) :
    fderiv ℝ (coordinatePolynomial d G) z = 0 ↔
      IsSimplexCritical (d + 1) G (affineCoordinates z) := by
  rw [fderiv_coordinatePolynomial]
  constructor
  · intro h y hy
    let x := zeroSumCoordinates.symm (⟨y, hy⟩ : zeroSumSpace (V := V))
    have hx : tangentCoordinates x = y :=
      congrArg Subtype.val (zeroSumCoordinates.apply_symm_apply ⟨y, hy⟩)
    have hval := congrArg (fun L => L x) h
    change differential (d + 1) G (affineCoordinates z) (tangentCoordinates x) = 0 at hval
    rwa [hx] at hval
  · intro hc
    ext x
    exact hc (tangentCoordinates x) (sum_tangentCoordinates x)

theorem affineCoordinates_eq_weights (z : openSimplexDomain (V := V)) :
    affineCoordinates z.1 = ((toPositiveSimplex z).1.weights : V → ℝ) := by
  ext i
  exact (toPositiveSimplex_coordinate z i).symm

/-- The actual open-simplex criticality adapter used by the Morse band theorem. -/
theorem openSimplex_polynomial_critical_iff (d : ℕ) (G : Finset (Finset V))
    (z : openSimplexDomain (V := V)) :
    fderiv ℝ (((coordinatePolynomial d G) ∘ Subtype.val) ∘
      (extChartAt 𝓘(ℝ, euclideanZeroSumSpace (V := V)) z).symm)
      (extChartAt 𝓘(ℝ, euclideanZeroSumSpace (V := V)) z z) = 0 ↔
    IsSimplexCritical (d + 1) G ((toPositiveSimplex z).1.weights : V → ℝ) := by
  rw [openSubtype_fderiv_coordinate, coordinatePolynomial_critical_iff, affineCoordinates_eq_weights]

/-- The manifold Morse index of the polynomial on the open simplex equals
the already checked negative index of its actual affine tangent Hessian. -/
theorem openSimplex_polynomial_morseIndex (d : ℕ) (G : Finset (Finset V))
    (z : openSimplexDomain (V := V)) :
    manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
      ((coordinatePolynomial d G) ∘ Subtype.val) z =
    sigNeg (tangentHessianForm d G (toPositiveSimplex z).1) := by
  rw [openSubtype_manifoldMorseIndex]
  have hform : (fderiv ℝ (fderiv ℝ (coordinatePolynomial d G)) z.1).toBilinForm.toQuadraticMap =
      (tangentHessianForm d G (toPositiveSimplex z).1).comp zeroSumCoordinates.toLinearEquiv.toLinearMap := by
    ext x
    change fderiv ℝ (fderiv ℝ (coordinatePolynomial d G)) z.1 x x =
      tangentHessianForm d G (toPositiveSimplex z).1 (zeroSumCoordinates x)
    rw [second_fderiv_coordinatePolynomial, tangentHessianForm_apply, affineCoordinates_eq_weights]
    rfl
  rw [hform, sigNeg_comp_linearEquiv]

end SharpTopologicalOverlap.Barrier
