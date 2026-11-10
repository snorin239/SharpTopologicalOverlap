module

public import SharpTopologicalOverlap.WeightSpaces.Fillings
public import SharpTopologicalOverlap.Sublevel

/-! # Lemma 6.2: unconditional weight-space fillings and relative vanishing -/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace SharpTopologicalOverlap.IntersectionData

open _root_.SharpTopologicalOverlap.Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}
  (I : IntersectionData T f)

/-- The actual ambient relative fillings of Lemma 6.2. -/
theorem weightSpace_fills {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (hn : deletionBound d < n) (j : ℕ) (hj : j ≤ d) :
    Singular.Fills (X := TopCat.of (Simplex (Fin n)))
      (I.weightSpace τ) (I.independentSpace τ) j := by
  obtain ⟨i, hi⟩ := I.remainingVertices_nonempty τ hn
  let : Nonempty (I.remainingVertices τ) := ⟨⟨i, hi⟩⟩
  exact I.weightSpace_fills_of_sublevel τ hd j
    (Sublevel.sublevel_homology_vanishes d (I.remainingFamily τ)
      (I.remainingFamily_uniform τ) (I.remainingFamily_hasCocycleParity τ) j hj)

/-- Lemma 6.2(iii) for the actual pair of nested weight spaces. -/
theorem weightSpace_homology_vanishes {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (hn : deletionBound d < n) (j : ℕ) (hj : j ≤ d) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of (Simplex (Fin n)))
      (I.independentSpace_subset_weightSpace τ)).singularHomology
        (ModuleCat.of Coeff Coeff) j) :=
  Singular.isZero_homology_of_fills (I.independentSpace_subset_weightSpace τ) j
    (I.weightSpace_fills τ hd hn j hj)

end SharpTopologicalOverlap.IntersectionData
