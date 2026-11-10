module

public import SharpTopologicalOverlap.Barrier.Generic
public import SharpTopologicalOverlap.Singular.Relative
public import TauCeti.Geometry.Manifold.Morse.Cell.Band

/-! # Morse bands on the open probability simplex

These are the actual barrier sublevels. The coefficient object and chain
fillings agree with the ambient singular-chain API used in Theorem 5.1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Manifold ContDiff

namespace SharpTopologicalOverlap.Sublevel

open Barrier

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The closed sublevel inside the boundaryless open simplex. -/
def barrierSublevel (d : ℕ) (G : Finset (Finset V)) (ε : ℝ) (α : V → ℝ) (r : ℝ) :
    Set (openSimplexDomain (V := V)) := {z | barrier d G ε α z ≤ r}

theorem barrierSublevel_mono (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (α : V → ℝ) {a b : ℝ} (hab : a ≤ b) :
    barrierSublevel d G ε α a ⊆ barrierSublevel d G ε α b :=
  fun _ hz => hz.trans hab

theorem isCompact_barrier_band (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ) (a b : ℝ) :
    IsCompact ((barrier d G ε α) ⁻¹' Icc a b) :=
  (isProperMap_barrier d G hε α).isCompact_preimage isCompact_Icc

/-- Regular levels exist in every nonempty interval for a Morse barrier. -/
theorem exists_regular_barrier_level (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ)
    (hM : TauCeti.IsMorse 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α))
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b,
      TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) (barrier d G ε α) r :=
  hM.exists_isRegularValue_mem_Ioo hab (isCompact_barrier_band d G hε α a b)

/-- Lemma 5.5 specialized to the actual logarithmic barrier and F₂ chains. -/
theorem barrier_band_homology_vanishes (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ)
    (hM : TauCeti.IsMorse 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α))
    {a b : ℝ} (hab : a ≤ b)
    (ha : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) (barrier d G ε α) a)
    (hb : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) (barrier d G ε α) b)
    (hindex : ∀ z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V))
      (barrier d G ε α) ∩ (barrier d G ε α) ⁻¹' Icc a b,
      d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
        (barrier d G ε α) z)
    {j : ℕ} (hj : j ≤ d) :
    IsZero ((TauCeti.sublevelPair (barrier d G ε α) hab).singularHomology
      (ModuleCat.of Simplicial.Coeff Simplicial.Coeff) j) :=
  hM.isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex hab
    (isCompact_barrier_band d G hε α a b) ha hb hindex _ (by omega)

/-- The homology statement above gives an actual boundary plus a chain in the
lower sublevel, retaining both support conditions in one ambient chain module. -/
theorem barrier_band_fills (d : ℕ) (G : Finset (Finset V))
    {ε : ℝ} (hε : 0 < ε) (α : V → ℝ)
    (hM : TauCeti.IsMorse 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α))
    {a b : ℝ} (hab : a ≤ b)
    (ha : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) (barrier d G ε α) a)
    (hb : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V)) 𝓘(ℝ) (barrier d G ε α) b)
    (hindex : ∀ z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V))
      (barrier d G ε α) ∩ (barrier d G ε α) ⁻¹' Icc a b,
      d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
        (barrier d G ε α) z)
    {j : ℕ} (hj : j ≤ d) :
    Singular.Fills (X := TopCat.of (openSimplexDomain (V := V)))
      (barrierSublevel d G ε α b) (barrierSublevel d G ε α a) j := by
  apply Singular.fills_of_isZero_homology (barrierSublevel_mono d G ε α hab) j
  exact barrier_band_homology_vanishes d G hε α hM hab ha hb hindex hj

end SharpTopologicalOverlap.Sublevel
