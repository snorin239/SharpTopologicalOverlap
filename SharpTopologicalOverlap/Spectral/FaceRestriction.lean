module

public import SharpTopologicalOverlap.Spectral.FaceRestriction.Derivatives

/-! # The strict index bound on every active face -/

@[expose] public noncomputable section

open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Corollary 4.2: a face-critical point of a cocycle polynomial strictly
between zero and the overlap threshold has negative index at least `d + 1`.
The index is that of the actual Hessian on the tangent space of its support. -/
theorem faceCritical_index_ge (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (μ : Simplex V)
    (hc : IsFaceCritical d G μ)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hθ : weightPolynomial (d + 1) G (μ.weights : V → ℝ) < overlapThreshold d) :
    d + 1 ≤ sigNeg (faceHessianForm d G μ) := by
  rw [sigNeg_faceHessianForm hG μ]
  apply fullSupportCritical_index_ge d (faceFamily (support μ) G)
    (faceFamily_uniform hG _) (faceFamily_parity hpar _) (supportPoint μ)
    (supportPoint_positive μ)
  · rwa [weightPolynomial_supportPoint hG μ]
  · rwa [weightPolynomial_supportPoint hG μ]
  · exact faceCritical_supportPoint hG μ hc

end SharpTopologicalOverlap.Spectral
