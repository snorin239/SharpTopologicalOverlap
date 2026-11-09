module

public import SharpTopologicalOverlap.Simplicial

/-! # Chains and cochains on ambient subcomplexes

A precomplex may omit vertices of the ambient complex. Its chains are therefore
represented by the already defined submodule of ambient chains carried by it.
Its cochains are functions on the ambient cells belonging to that precomplex.
No enlargement by unused vertices, or reindexing of vertices, is needed here.
For arbitrary `L` these are the cells in the intersection with `K`; when `L ≤ K`,
as in the applications, they are exactly the cells of `L`.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Simplicial

variable {V : Type*} {K : AbstractSimplicialComplex V}
  {L M : PreAbstractSimplicialComplex V} {k : ℕ}

/-- Ambient cells that belong to a possibly vertex-omitting subcomplex. -/
abbrev SubcomplexCell (K : AbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex V) (k : ℕ) :=
  {s : Cell K k // s.1.1 ∈ L}

/-- Chains of the subcomplex, as an actual submodule of ambient chains. -/
abbrev SubcomplexChain (K : AbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex V) (k : ℕ) :=
  ↥(carriedSubmodule (K := K) (k := k) L)

/-- Cochains are functions on exactly the cells of the subcomplex. -/
abbrev SubcomplexCochain (K : AbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex V) (k : ℕ) :=
  SubcomplexCell K L k → Coeff

/-- Include a carried chain in the ambient chain module. -/
def includeSubcomplexChain (L : PreAbstractSimplicialComplex V) :
    SubcomplexChain K L k →ₗ[Coeff] Chain K k :=
  (carriedSubmodule L).subtype

theorem includeSubcomplexChain_injective :
    Function.Injective (includeSubcomplexChain (K := K) (k := k) L) :=
  Subtype.val_injective

/-- Restrict an ambient cochain to the cells of a subcomplex. -/
def restrictToSubcomplex (L : PreAbstractSimplicialComplex V) (a : Cochain K k) :
    SubcomplexCochain K L k := fun s => a s.1

/-- Extend a subcomplex cochain by zero on the other ambient cells. -/
def extendFromSubcomplex (a : SubcomplexCochain K L k) : Cochain K k := by
  classical
  exact fun s => if h : s.1.1 ∈ L then a ⟨s, h⟩ else 0

@[simp] theorem restrict_extendFromSubcomplex (a : SubcomplexCochain K L k) :
    restrictToSubcomplex L (extendFromSubcomplex a) = a := by
  classical
  funext s
  simp [restrictToSubcomplex, extendFromSubcomplex, s.2]

theorem restrictToSubcomplex_eq_zero_iff (a : Cochain K k) :
    restrictToSubcomplex L a = 0 ↔ VanishesOn L a := by
  constructor
  · intro h s hs
    exact congrFun h ⟨s, hs⟩
  · intro h
    funext s
    exact h s.1 s.2

/-- Evaluation on a carried chain, by the linear extension of a subcomplex cochain. -/
def subcomplexEvaluation (a : SubcomplexCochain K L k) :
    SubcomplexChain K L k →ₗ[Coeff] Coeff :=
  (evaluation (extendFromSubcomplex a)).comp (includeSubcomplexChain L)

/-- Restriction changes neither a cochain's value nor its evaluation on carried chains. -/
theorem evaluation_restrictToSubcomplex (a : Cochain K k)
    (c : SubcomplexChain K L k) :
    subcomplexEvaluation (restrictToSubcomplex L a) c = evaluation a c.1 := by
  classical
  change c.1.sum (fun s r => r • extendFromSubcomplex (restrictToSubcomplex L a) s) =
    c.1.sum (fun s r => r • a s)
  apply Finset.sum_congr rfl
  intro s hs
  have hc : CarriedBy L c.1 := c.2
  simp [extendFromSubcomplex, restrictToSubcomplex, hc s hs]

theorem subcomplexEvaluation_eq_zero_of_vanishesOn {a : Cochain K k}
    (ha : VanishesOn L a) (c : SubcomplexChain K L k) :
    subcomplexEvaluation (restrictToSubcomplex L a) c = 0 := by
  rw [evaluation_restrictToSubcomplex]
  exact evaluation_eq_zero_of_carriedBy ha c.2

/-- Boundary restricts to the chain modules of any ambient subcomplex. -/
def subcomplexBoundary [LinearOrder V] (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    SubcomplexChain K L (k + 1) →ₗ[Coeff] SubcomplexChain K L k :=
  (boundary k).restrict (fun _ hc => carriedBy_boundary hc)

@[simp] theorem include_subcomplexBoundary [LinearOrder V]
    (c : SubcomplexChain K L (k + 1)) :
    includeSubcomplexChain L (subcomplexBoundary L k c) = boundary k c.1 := rfl

theorem subcomplexBoundary_squared [LinearOrder V] (c : SubcomplexChain K L (k + 2)) :
    subcomplexBoundary L k (subcomplexBoundary L (k + 1) c) = 0 := by
  apply Subtype.ext
  exact boundary_boundary c.1

/-- An inclusion of ambient subcomplexes gives an inclusion of their chain modules. -/
def subcomplexChainInclusion (hLM : L ≤ M) :
    SubcomplexChain K L k →ₗ[Coeff] SubcomplexChain K M k :=
  Submodule.inclusion (fun _ hc => carriedBy_mono hLM hc)

@[simp] theorem boundary_subcomplexChainInclusion [LinearOrder V] (hLM : L ≤ M)
    (c : SubcomplexChain K L (k + 1)) :
    subcomplexBoundary M k (subcomplexChainInclusion hLM c) =
      subcomplexChainInclusion hLM (subcomplexBoundary L k c) := rfl

end SharpTopologicalOverlap.Simplicial
