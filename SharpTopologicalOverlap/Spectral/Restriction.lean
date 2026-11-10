module

public import TauCeti.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Basic.Real.Basic

/-! # Negative index under linear pullback and retraction

The normalized Hessian can be projected onto the orthogonal complement of
its distinguished eigenvector while retaining a full ambient matrix.
These lemmas justify the index comparison without choosing a basis of that
orthogonal complement.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Spectral

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Linear pullback cannot increase a quadratic form's negative index. -/
theorem sigNeg_comp_le (Q : QuadraticForm ℝ E) (f : F →ₗ[ℝ] E) :
    sigNeg (Q.comp f) ≤ sigNeg Q := by
  obtain ⟨U, hUdim, hUneg⟩ := exists_finrank_eq_sigNeg_and_negDef (Q.comp f)
  let g : U →ₗ[ℝ] E := f.comp U.subtype
  have hg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    by_contra hx0
    have hpos := hUneg x hx0
    have hgx : f x.1 = 0 := hx
    change 0 < -Q (f x.1) at hpos
    rw [hgx, map_zero, neg_zero] at hpos
    exact (lt_irrefl 0) hpos
  rw [← hUdim, ← LinearMap.finrank_range_of_inj hg]
  apply le_sigNeg_of_negDef (Q := Q) (V := LinearMap.range g)
  intro y hy0
  obtain ⟨x, hx⟩ := y.2
  have hx0 : x ≠ 0 := by
    intro h
    apply hy0
    apply Subtype.ext
    simpa only [h, map_zero, Submodule.coe_zero] using hx.symm
  have hpos := hUneg x hx0
  change 0 < -Q y.1
  change 0 < -Q (f x.1) at hpos
  change 0 < -Q (g x) at hpos
  rw [hx] at hpos
  exact hpos

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- An invertible linear change of coordinates preserves the negative index. -/
theorem sigNeg_comp_linearEquiv (Q : QuadraticForm ℝ E) (e : F ≃ₗ[ℝ] E) :
    sigNeg (Q.comp e.toLinearMap) = sigNeg Q := by
  have h : Q.Equivalent (Q.comp e.toLinearMap) := ⟨Q.isometryEquivOfCompLinearEquiv e⟩
  exact h.sigNeg_eq.symm

/-- If a form factors through its restriction to a subspace, that restriction
has the same negative index. This applies in particular to a projection along
a direction killed by the form. -/
theorem sigNeg_restrict_eq_of_factor (Q : QuadraticForm ℝ E) (S : Submodule ℝ E)
    (P : E →ₗ[ℝ] S) (hP : ∀ x, Q x = Q (P x).1) :
    sigNeg (Q.restrict S) = sigNeg Q := by
  apply Nat.le_antisymm (QuadraticForm.sigNeg_restrict_le Q S)
  have hfactor : Q = (Q.restrict S).comp P := by
    ext x
    exact hP x
  calc
    sigNeg Q = sigNeg ((Q.restrict S).comp P) := congrArg sigNeg hfactor
    _ ≤ sigNeg (Q.restrict S) := sigNeg_comp_le (Q.restrict S) P

end SharpTopologicalOverlap.Spectral
