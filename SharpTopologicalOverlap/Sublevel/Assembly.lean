module

public import SharpTopologicalOverlap.Sublevel.Parameters
public import SharpTopologicalOverlap.Sublevel.Neighborhood
public import SharpTopologicalOverlap.Sublevel.Margins
public import SharpTopologicalOverlap.Sublevel.CycleFilling
public import SharpTopologicalOverlap.Singular.Vanishing
public import SharpTopologicalOverlap.Singular.Deformation

/-! # Relative sublevel fillings from critical-index persistence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Manifold unitInterval
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Sublevel

open Barrier

variable {V : Type} [Fintype V] [Nonempty V]

/-- The full chain construction of Theorem 5.1, with its remaining
critical-index persistence input explicit. -/
theorem sublevel_cycle_fills_of_index_persistence (d : ℕ) (G : Finset (Finset V))
    (hpersist : ∀ h₀ h₁ : ℝ, 0 < h₀ → h₀ < h₁ → h₁ < overlapThreshold d →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ α : V → ℝ,
        (∑ i, α i) = 0 → ‖α‖ < δ → ∀ z : openSimplexDomain (V := V),
        z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α) →
        barrier d G ε α z ∈ Icc h₀ h₁ →
        d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
          (barrier d G ε α) z)
    (j : ℕ) (hj : j ≤ d) :
    Singular.Fills (X := TopCat.of (Simplex V)) (strictSublevel d G) (zeroSet d G) j := by
  classical
  intro c hcB hcZ
  by_cases hzero : c = 0
  · subst c
    exact ⟨0, 0, Singular.carriedBy_zero _, Singular.carriedBy_zero _, by simp⟩
  obtain ⟨κ, hκ, hκθ, hK⟩ := exists_chain_margin d G c hcB hzero
  obtain ⟨U, hZU, hUopen, hUB, r, _, ⟨HR⟩⟩ := exists_retracting_neighborhood d G
  have hUZ : Singular.Fills (X := TopCat.of (Simplex V)) U (zeroSet d G) j :=
    Singular.fills_of_homotopyRel hZU r HR j
  obtain ⟨γ, hγ, hγκ, hU⟩ := exists_small_sublevel_subset d G hUopen hZU hκ
  obtain ⟨δ, hδ, hindex⟩ := hpersist (2 * γ) (overlapThreshold d - κ)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨D⟩ := exists_morseBandData d G (Singular.image c) U hκ hκθ hγ hγκ hU hK hδ hindex
  let g := pushInsideMap (V := V) D.t₀
  let H := pushInsideHomotopy (V := V) D.t₀
  have hcomp : pushToOpenSimplex D.t₀ D.time_pos ≫ openSimplexInclusion = g :=
    pushToOpenSimplex_comp_inclusion D.t₀ D.time_pos
  have hend := endpoint_fill_of_push (pushToOpenSimplex D.t₀ D.time_pos)
    openSimplexInclusion hcomp (D.band_fills j hj) D.upper_carrier D.lower_carrier
    D.push_zero c hcZ D.push_carrier
  have hHZ : ∀ (t : unitInterval) (μ : Simplex V), μ ∈ zeroSet d G → H (t, μ) ∈ U :=
    D.homotopy_zero
  have hP : Singular.CarriedBy (strictSublevel d G) (Singular.prism H j c) := by
    apply Singular.carriedBy_prism H (A := Singular.image c)
    · exact D.homotopy_carrier
    · exact (Singular.carriedBy_iff_image_subset _ _).mpr Set.Subset.rfl
  exact fill_after_push hUB hUZ H hHZ c hcZ hP hend

end SharpTopologicalOverlap.Sublevel
