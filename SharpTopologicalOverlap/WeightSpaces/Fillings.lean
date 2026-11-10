module

public import SharpTopologicalOverlap.WeightSpaces.Face
public import SharpTopologicalOverlap.WeightSpaces.Deformation

/-! # Ambient weight-space fillings from the sublevel theorem

The analytic vanishing remains an explicit hypothesis here. This module
performs its reindexing, topological-pair transport, deletion deformation,
and lifting to chains in the fixed ambient probability simplex.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace SharpTopologicalOverlap.IntersectionData

open _root_.SharpTopologicalOverlap.Simplicial WeightPolynomial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}
  (I : IntersectionData T f)

theorem remainingVertices_eq_compl {p : ℕ} (τ : Cell T p) :
    I.remainingVertices τ = (I.exceptionalSet τ)ᶜ := rfl

theorem weightSpace_eq_carrier {p : ℕ} (τ : Cell T p) :
    I.weightSpace τ = WeightDeletion.carrier (I.exceptionalSet τ) (d + 1)
      (upwardSupport I.cochain τ) (overlapThreshold d) := rfl

theorem remainingWeightSpace_eq_faceCarrier {p : ℕ} (τ : Cell T p) :
    I.remainingWeightSpace τ = WeightDeletion.faceCarrier (I.exceptionalSet τ) (d + 1)
      (upwardSupport I.cochain τ) (overlapThreshold d) := rfl

/-- Lemma 6.2(iii), with the sole remaining analytic input stated as the
actual relative homology of the cocycle sublevel pair on `Y_τ`. -/
theorem weightSpace_fills_of_sublevel {p : ℕ} (τ : Cell T p) (hd : 0 < d) (j : ℕ)
    (hH : IsZero ((Sublevel.sublevelPair d (I.remainingFamily τ)).singularHomology
      (ModuleCat.of Coeff Coeff) j)) :
    Singular.Fills (X := TopCat.of (Simplex (Fin n))) (I.weightSpace τ) (I.independentSpace τ) j := by
  rw [I.weightSpace_eq_carrier τ]
  apply WeightDeletion.fills_carrier_of_face_homology (I.exceptionalSet τ) (d + 1) (by omega)
    (upwardSupport I.cochain τ) (overlapThreshold d) (I.independentSpace τ)
    (show I.independentSpace τ ⊆ WeightDeletion.faceCarrier (I.exceptionalSet τ) (d + 1)
      (upwardSupport I.cochain τ) (overlapThreshold d) from
      I.independentSpace_subset_remainingWeightSpace τ) j
  exact I.isZero_remainingFace_of_sublevel τ hd j hH

end SharpTopologicalOverlap.IntersectionData
