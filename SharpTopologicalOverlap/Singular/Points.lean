module

public import SharpTopologicalOverlap.Singular

/-! # Point chains and subspace carriers -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Singular

variable {X Y : TopCat.{0}}

theorem pushforward_pointChain (f : X ⟶ Y) (x : X) :
    pushforward f 0 (TauCeti.pointChain Coeff x) = TauCeti.pointChain Coeff (f x) := by
  change (((TauCeti.singularChains Coeff).map f).f 0) (TauCeti.pointChain Coeff x) = _
  rw [TauCeti.singularChains_map_f_simplexChain]
  simp

theorem carriedBy_pointChain {A : Set X} {x : X} (hx : x ∈ A) :
    CarriedBy A (TauCeti.pointChain Coeff x) :=
  ⟨TauCeti.pointChain Coeff (⟨x, hx⟩ : A), pushforward_pointChain (inclusion A) _⟩

end SharpTopologicalOverlap.Singular
