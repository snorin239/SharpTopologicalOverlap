module

public import SharpTopologicalOverlap.Barrier
public import SharpTopologicalOverlap.Sublevel.Assembly

/-! # Theorem 5.1: relative homology vanishes below the overlap threshold -/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace SharpTopologicalOverlap.Sublevel

variable {V : Type} [Fintype V] [LinearOrder V] [Nonempty V]

/-- The concrete relative filling assertion underlying Theorem 5.1. -/
theorem sublevel_cycle_fills (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (j : ℕ) (hj : j ≤ d) :
    Singular.Fills (X := TopCat.of (Simplex V)) (strictSublevel d G) (zeroSet d G) j := by
  apply sublevel_cycle_fills_of_index_persistence d G ?_ j hj
  intro h₀ h₁ h₀pos h₀₁ h₁θ
  obtain ⟨δ, hδ, hindex⟩ :=
    Barrier.exists_manifold_index_persistence d G hG hpar h₀pos h₀₁ h₁θ
  exact ⟨δ, hδ, fun ε hε hεδ α _ hα => hindex ε hε hεδ α hα⟩

/-- Theorem 5.1 for the actual polynomial sublevel/zero-set pair, with
ordinary relative singular homology over `ZMod 2`, including degree zero. -/
theorem sublevel_homology_vanishes (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (j : ℕ) (hj : j ≤ d) :
    IsZero ((sublevelPair d G).singularHomology (ModuleCat.of Simplicial.Coeff Simplicial.Coeff) j) :=
  Singular.isZero_homology_of_fills (zeroSet_subset_strictSublevel d G) j
    (sublevel_cycle_fills d G hG hpar j hj)

end SharpTopologicalOverlap.Sublevel
