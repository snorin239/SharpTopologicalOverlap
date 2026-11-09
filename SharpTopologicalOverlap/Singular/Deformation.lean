module

public import SharpTopologicalOverlap.Singular.Relative
public import SharpTopologicalOverlap.Singular.Prism

/-! # Fillings from strong deformation retracts -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Singular

/-- Lemma 2.2(b), with its filling chains in the original ambient space.
The homotopy is the standard `HomotopyRel` presentation of a strong
deformation retraction. Its direction is reversed by the imported theorem. -/
theorem fills_of_homotopyRel {X : TopCat.{0}} {J B : Set X} (hJB : J ⊆ B)
    (r : C(B, J))
    (H : ((ContinuousMap.inclusion hJB).comp r).HomotopyRel (ContinuousMap.id B)
      {x | (x : X) ∈ J}) (k : ℕ) : Fills B J k :=
  fills_of_isZero_homology hJB k
    (TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel hJB r H
      (ModuleCat.of Coeff Coeff) k)

end SharpTopologicalOverlap.Singular
