module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex

/-! # Simplicial chains and cochains over `𝔽₂`

Cells and chains are exactly the types used by TauCeti's ordered simplicial chain
complex. Cochains are functions on the same cells. In particular the source may
be the full simplex, even when a continuous map is only given on its skeleton.
-/

@[expose] public section

noncomputable section

open Finsupp

namespace SharpTopologicalOverlap.Simplicial

variable {V : Type*}

/-- The coefficient field used throughout the paper. -/
abbrev Coeff := ZMod 2

/-- A `k`-cell is a face with `k + 1` vertices. -/
abbrev Cell (K : AbstractSimplicialComplex V) (k : ℕ) :=
  AbstractSimplicialComplex.RealizationCell K k

/-- Finite simplicial chains with coefficients in `𝔽₂`. -/
abbrev Chain (K : AbstractSimplicialComplex V) (k : ℕ) :=
  TauCeti.OrderedSimplicialChain K Coeff k

/-- Cochains use the very same face indexing as chains. -/
abbrev Cochain (K : AbstractSimplicialComplex V) (k : ℕ) := Cell K k → Coeff

variable {K : AbstractSimplicialComplex V} {k : ℕ}

/-- Evaluate a cochain by linear extension from the face basis. -/
def evaluation (a : Cochain K k) : Chain K k →ₗ[Coeff] Coeff :=
  Finsupp.linearCombination Coeff a

@[simp] theorem evaluation_single (a : Cochain K k) (s : Cell K k) (r : Coeff) :
    evaluation a (Finsupp.single s r) = r * a s := by
  simp [evaluation, smul_eq_mul]

@[simp] theorem evaluation_zero (a : Cochain K k) : evaluation a 0 = 0 := map_zero _

@[simp] theorem evaluation_zero_cochain (c : Chain K k) : evaluation (0 : Cochain K k) c = 0 := by
  simp [evaluation]

theorem evaluation_add_cochain (a b : Cochain K k) (c : Chain K k) :
    evaluation (a + b) c = evaluation a c + evaluation b c := by
  simp [evaluation, Finsupp.linearCombination_apply, Finsupp.sum, mul_add,
    Finset.sum_add_distrib]

theorem evaluation_smul_cochain (r : Coeff) (a : Cochain K k) (c : Chain K k) :
    evaluation (r • a) c = r * evaluation a c := by
  simp [evaluation, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
    Finset.mul_sum, mul_left_comm]

section Ordered

variable [LinearOrder V]

/-- Boundary in successor degrees; this is TauCeti's checked boundary. -/
abbrev boundary (k : ℕ) : Chain K (k + 1) →ₗ[Coeff] Chain K k :=
  TauCeti.OrderedSimplicialChain.boundary Coeff k

/-- The unaugmented degree-zero boundary has a zero-dimensional target.
This is distinct from the augmentation, which takes values in `Coeff`. -/
def boundaryZero : Chain K 0 →ₗ[Coeff] (Fin 0 → Coeff) := 0

omit [LinearOrder V] in
@[simp] theorem boundaryZero_apply (c : Chain K 0) : boundaryZero c = 0 := rfl

/-- The imported unaugmented chain complex also has zero differential out of degree zero. -/
theorem chainComplex_d_zero (j : ℕ) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).d 0 j = 0 := by
  apply HomologicalComplex.shape
  simp [ComplexShape.down_Rel]

/-- Over `𝔽₂` every alternating sign in the simplicial boundary is one. -/
theorem boundary_single (s : Cell K (k + 1)) (r : Coeff) :
    boundary k (Finsupp.single s r) =
      ∑ j : Fin (k + 2), Finsupp.single (s.face j) r := by
  simp [boundary, TauCeti.OrderedSimplicialChain.boundary_single,
    show (-1 : Coeff) = 1 by decide]

theorem boundary_boundary (c : Chain K (k + 2)) :
    boundary k (boundary (k + 1) c) = 0 := by
  exact LinearMap.congr_fun (TauCeti.OrderedSimplicialChain.boundary_boundary Coeff k) c

/-- Coboundary is dual to boundary, with no truncated subtraction in its degree. -/
def coboundary (a : Cochain K k) : Cochain K (k + 1) :=
  fun s => evaluation a (boundary k (Finsupp.single s 1))

theorem coboundary_apply (a : Cochain K k) (s : Cell K (k + 1)) :
    coboundary a s = ∑ j : Fin (k + 2), a (s.face j) := by
  simp [coboundary]

/-- Evaluation and coboundary are adjoint to the chain boundary. -/
theorem evaluation_coboundary (a : Cochain K k) (c : Chain K (k + 1)) :
    evaluation (coboundary a) c = evaluation a (boundary k c) := by
  have h : evaluation (coboundary a) = (evaluation a).comp (boundary k) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [coboundary]
  exact LinearMap.congr_fun h c

@[simp] theorem coboundary_zero : coboundary (0 : Cochain K k) = 0 := by
  funext s
  simp [coboundary]

theorem coboundary_add (a b : Cochain K k) :
    coboundary (a + b) = coboundary a + coboundary b := by
  funext s
  simp [coboundary_apply, Finset.sum_add_distrib]

theorem coboundary_smul (r : Coeff) (a : Cochain K k) :
    coboundary (r • a) = r • coboundary a := by
  funext s
  simp [coboundary_apply, Finset.mul_sum, smul_eq_mul]

/-- The degree-zero cochain taking value one at every vertex. -/
def oneCochain (K : AbstractSimplicialComplex V) : Cochain K 0 := fun _ => 1

omit [LinearOrder V] in
@[simp] theorem oneCochain_apply (s : Cell K 0) : oneCochain K s = 1 := rfl

theorem coboundary_oneCochain : coboundary (oneCochain K) = 0 := by
  funext s
  simp only [coboundary_apply, oneCochain, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Pi.zero_apply]
  decide

/-- The second coboundary is zero, using the imported boundary-square identity. -/
theorem coboundary_coboundary (a : Cochain K k) : coboundary (coboundary a) = 0 := by
  funext s
  simp only [coboundary, Pi.zero_apply]
  rw [evaluation_coboundary, boundary_boundary, evaluation_zero]

/-- A simplicial cocycle. -/
def IsCocycle (a : Cochain K k) : Prop := coboundary a = 0

theorem isCocycle_one : IsCocycle (oneCochain K) := coboundary_oneCochain

omit [LinearOrder V] in
@[simp] theorem evaluation_one_single (s : Cell K 0) :
    evaluation (oneCochain K) (Finsupp.single s 1) = 1 := by simp

theorem isCocycle_iff (a : Cochain K k) :
    IsCocycle a ↔ ∀ s : Cell K (k + 1), ∑ j : Fin (k + 2), a (s.face j) = 0 := by
  simp only [IsCocycle, funext_iff, coboundary_apply, Pi.zero_apply]

end Ordered

/-- A chain is carried by an ambient subcomplex if each supported face belongs to it.
The subcomplex can omit vertices, hence its type is `PreAbstractSimplicialComplex`. -/
def CarriedBy (L : PreAbstractSimplicialComplex V) (c : Chain K k) : Prop :=
  ∀ s ∈ c.support, s.1.1 ∈ L

/-- The ambient submodule of chains carried by a subcomplex. -/
def carriedSubmodule (L : PreAbstractSimplicialComplex V) : Submodule Coeff (Chain K k) :=
  Finsupp.supported Coeff Coeff {s : Cell K k | s.1.1 ∈ L}

theorem carriedBy_iff_mem (L : PreAbstractSimplicialComplex V) (c : Chain K k) :
    CarriedBy L c ↔ c ∈ carriedSubmodule L := Iff.rfl

/-- Vanishing is expressed using the same ambient cells as the chains. -/
def VanishesOn (L : PreAbstractSimplicialComplex V) (a : Cochain K k) : Prop :=
  ∀ s : Cell K k, s.1.1 ∈ L → a s = 0

theorem evaluation_eq_zero_of_carriedBy {L : PreAbstractSimplicialComplex V}
    {a : Cochain K k} {c : Chain K k} (ha : VanishesOn L a) (hc : CarriedBy L c) :
    evaluation a c = 0 := by
  classical
  change c.sum (fun s r => r • a s) = 0
  apply Finset.sum_eq_zero
  intro s hs
  simp [ha s (hc s hs)]

theorem carriedBy_mono {L M : PreAbstractSimplicialComplex V} {c : Chain K k}
    (hLM : L ≤ M) (hc : CarriedBy L c) : CarriedBy M c :=
  fun s hs => hLM (hc s hs)

@[simp] theorem carriedBy_zero (L : PreAbstractSimplicialComplex V) :
    CarriedBy L (0 : Chain K k) := by simp [CarriedBy]

theorem carriedBy_add {L : PreAbstractSimplicialComplex V} {c d : Chain K k}
    (hc : CarriedBy L c) (hd : CarriedBy L d) : CarriedBy L (c + d) :=
  (carriedSubmodule L).add_mem hc hd

theorem carriedBy_smul {L : PreAbstractSimplicialComplex V} {c : Chain K k}
    (r : Coeff) (hc : CarriedBy L c) : CarriedBy L (r • c) :=
  (carriedSubmodule L).smul_mem r hc

/-- Boundary stays in the same ambient subcomplex. -/
theorem carriedBy_boundary [LinearOrder V] {L : PreAbstractSimplicialComplex V} {c : Chain K (k + 1)}
    (hc : CarriedBy L c) : CarriedBy L (boundary k c) := by
  classical
  change boundary k c ∈ carriedSubmodule L
  have hdec : boundary k c =
      ∑ s ∈ c.support, ∑ j : Fin (k + 2), Finsupp.single (s.face j) (c s) := by
    calc
      boundary k c = boundary k (c.sum Finsupp.single) :=
        congrArg (boundary k) c.sum_single.symm
      _ = _ := by simp [Finsupp.sum]
  rw [hdec]
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.sum_mem
  intro j _
  apply Finsupp.single_mem_supported
  apply L.isRelLowerSet_faces.mem_of_le (hc s hs)
  · rw [AbstractSimplicialComplex.RealizationCell.face_val]
    exact Finset.erase_subset _ _
  · exact Finset.card_pos.mp (by rw [(s.face j).2]; omega)

/-- Every cell has an unambiguous underlying finite vertex set. -/
theorem cell_vertices_injective :
    Function.Injective (fun s : Cell K k => s.1.1) := by
  intro s t h
  exact Subtype.ext (Subtype.ext h)

/-- Include cells along an inclusion of complexes on a fixed ambient vertex type. -/
def includeCell {L : AbstractSimplicialComplex V} (h : K ≤ L) (s : Cell K k) : Cell L k :=
  ⟨⟨s.1.1, h s.1.2⟩, s.2⟩

@[simp] theorem includeCell_vertices {L : AbstractSimplicialComplex V}
    (h : K ≤ L) (s : Cell K k) : (includeCell h s).1.1 = s.1.1 := rfl

theorem includeCell_injective {L : AbstractSimplicialComplex V} (h : K ≤ L) :
    Function.Injective (includeCell (k := k) h) := by
  intro s t hst
  apply cell_vertices_injective
  exact congrArg (fun c : Cell L k => c.1.1) hst

@[simp] theorem includeCell_face [LinearOrder V] {L : AbstractSimplicialComplex V}
    (h : K ≤ L) (s : Cell K (k + 1)) (j : Fin (k + 2)) :
    includeCell h (s.face j) = (includeCell h s).face j := by
  apply cell_vertices_injective
  have h₁ : ⇑s.vertexEmbedding = s.1.1.orderEmbOfFin s.2 :=
    Finset.orderEmbOfFin_unique s.2 s.vertexEmbedding_mem s.strictMono_vertexEmbedding
  have h₂ : ⇑(includeCell h s).vertexEmbedding = s.1.1.orderEmbOfFin s.2 :=
    Finset.orderEmbOfFin_unique s.2 (includeCell h s).vertexEmbedding_mem
      (includeCell h s).strictMono_vertexEmbedding
  simp only [includeCell_vertices, AbstractSimplicialComplex.RealizationCell.face_val]
  rw [congrFun h₁ j, congrFun h₂ j]

/-- Include chains by the inclusion of their face bases. -/
def includeChain {L : AbstractSimplicialComplex V} (h : K ≤ L) :
    Chain K k →ₗ[Coeff] Chain L k :=
  Finsupp.lmapDomain Coeff Coeff (includeCell h)

@[simp] theorem includeChain_single {L : AbstractSimplicialComplex V}
    (h : K ≤ L) (s : Cell K k) (r : Coeff) :
    includeChain h (Finsupp.single s r) = Finsupp.single (includeCell h s) r := by
  simp [includeChain]

theorem includeChain_injective {L : AbstractSimplicialComplex V} (h : K ≤ L) :
    Function.Injective (includeChain (k := k) h) :=
  Finsupp.mapDomain_injective (includeCell_injective h)

/-- Restriction of cochains is precomposition with the cell inclusion. -/
def restrictCochain {L : AbstractSimplicialComplex V} (h : K ≤ L)
    (a : Cochain L k) : Cochain K k := a ∘ includeCell h

theorem evaluation_restrict {L : AbstractSimplicialComplex V} (h : K ≤ L)
    (a : Cochain L k) (c : Chain K k) :
    evaluation (restrictCochain h a) c = evaluation a (includeChain h c) := by
  have he : evaluation (restrictCochain h a) = (evaluation a).comp (includeChain h) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [restrictCochain]
  exact LinearMap.congr_fun he c

theorem boundary_includeChain [LinearOrder V] {L : AbstractSimplicialComplex V} (h : K ≤ L)
    (c : Chain K (k + 1)) : boundary k (includeChain h c) = includeChain h (boundary k c) := by
  have he : (boundary k).comp (includeChain h) = (includeChain h).comp (boundary k) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp
  exact LinearMap.congr_fun he c

theorem coboundary_restrict [LinearOrder V] {L : AbstractSimplicialComplex V} (h : K ≤ L)
    (a : Cochain L k) : coboundary (restrictCochain h a) = restrictCochain h (coboundary a) := by
  funext s
  simp [coboundary_apply, restrictCochain]

/-- Cells of the full simplex are exactly finite sets with the specified cardinality. -/
def fullCellEquiv (V : Type*) (k : ℕ) :
    Cell (⊤ : AbstractSimplicialComplex V) k ≃ {s : Finset V // s.card = k + 1} where
  toFun s := ⟨s.1.1, s.2⟩
  invFun s := ⟨⟨s.1, by
    change s.1.Nonempty
    exact Finset.card_pos.mp (by rw [s.2]; omega)⟩, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A uniform finite family consists of sets of exactly the given size. -/
def IsUniform (r : ℕ) (G : Finset (Finset V)) : Prop := ∀ s ∈ G, s.card = r

section Finite

variable [Fintype V]

instance cellFintype (K : AbstractSimplicialComplex V) (k : ℕ) : Fintype (Cell K k) :=
  Fintype.ofFinite _

/-- The finite family of vertex sets on which a cochain has coefficient one. -/
def supportFamily (a : Cochain K k) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter fun s : Cell K k => a s ≠ 0).image fun s => s.1.1

@[simp] theorem mem_supportFamily (a : Cochain K k) (s : Cell K k) :
    s.1.1 ∈ supportFamily a ↔ a s ≠ 0 := by
  classical
  simp only [supportFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hts⟩
    exact cell_vertices_injective hts ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

theorem supportFamily_uniform (a : Cochain K k) : IsUniform (k + 1) (supportFamily a) := by
  classical
  intro s hs
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
  exact t.2

theorem supportFamily_faces (a : Cochain K k) : ∀ s ∈ supportFamily a, s ∈ K := by
  classical
  intro s hs
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
  exact t.1.2

/-- A finite family defines its characteristic cochain on the ambient complex. -/
def cochainOfFamily (G : Finset (Finset V)) : Cochain K k := by
  classical
  exact fun s => if s.1.1 ∈ G then 1 else 0

omit [Fintype V] in
@[simp] theorem cochainOfFamily_ne_zero (G : Finset (Finset V)) (s : Cell K k) :
    cochainOfFamily G s ≠ 0 ↔ s.1.1 ∈ G := by classical simp [cochainOfFamily]

theorem cochainOfFamily_supportFamily (a : Cochain K k) :
    cochainOfFamily (supportFamily a) = a := by
  funext s
  obtain h | h := (show ∀ r : Coeff, r = 0 ∨ r = 1 by decide) (a s)
  · simp [cochainOfFamily, mem_supportFamily, h]
  · simp [cochainOfFamily, mem_supportFamily, h]

theorem supportFamily_cochainOfFamily (G : Finset (Finset V))
    (hG : IsUniform (k + 1) G) (hK : ∀ s ∈ G, s ∈ K) :
    supportFamily (cochainOfFamily G : Cochain K k) = G := by
  classical
  apply Finset.Subset.antisymm
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact (cochainOfFamily_ne_zero G t).mp (Finset.mem_filter.mp ht).2
  · intro s hs
    let t : Cell K k := ⟨⟨s, hK s hs⟩, hG s hs⟩
    exact (mem_supportFamily (cochainOfFamily G) t).mpr
      ((cochainOfFamily_ne_zero G t).mpr hs)

end Finite

section OrderedParity

variable [LinearOrder V]

/-- The number of supported facets of a cell. -/
def supportedFacetCount (a : Cochain K k) (s : Cell K (k + 1)) : ℕ :=
  (Finset.univ.filter fun j : Fin (k + 2) => a (s.face j) ≠ 0).card

theorem coboundary_eq_supportedFacetCount (a : Cochain K k) (s : Cell K (k + 1)) :
    coboundary a s = (supportedFacetCount a s : Coeff) := by
  classical
  rw [coboundary_apply, supportedFacetCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  obtain h | h := (show ∀ r : Coeff, r = 0 ∨ r = 1 by decide) (a (s.face j))
  · simp [h]
  · simp [h]

/-- The cocycle condition is precisely even parity of supported facets. -/
theorem isCocycle_iff_even (a : Cochain K k) :
    IsCocycle a ↔ ∀ s : Cell K (k + 1), Even (supportedFacetCount a s) := by
  simp only [IsCocycle, funext_iff, coboundary_eq_supportedFacetCount, Pi.zero_apply,
    ZMod.natCast_eq_zero_iff_even]

section FiniteParity

variable [Fintype V]

/-- Counting supported facets by vertex sets gives the same count as the ordered faces. -/
theorem supportedFacetCount_eq_supportFamily (a : Cochain K k) (s : Cell K (k + 1)) :
    supportedFacetCount a s = ((supportFamily a).filter fun t => t ⊆ s.1.1).card := by
  classical
  have himage :
      (Finset.univ.filter fun j : Fin (k + 2) => a (s.face j) ≠ 0).image
          (fun j => (s.face j).1.1) =
        (supportFamily a).filter (fun t => t ⊆ s.1.1) := by
    ext t
    constructor
    · intro ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr
        ⟨(mem_supportFamily a (s.face j)).mpr (Finset.mem_filter.mp hj).2,
          by rw [AbstractSimplicialComplex.RealizationCell.face_val]
             exact Finset.erase_subset _ _⟩
    · intro ht
      obtain ⟨htG, hts⟩ := Finset.mem_filter.mp ht
      let c : Cell K k := ⟨⟨t, supportFamily_faces a t htG⟩, supportFamily_uniform a t htG⟩
      obtain ⟨j, hj⟩ := (s.exists_face_eq_iff_subset c).mpr hts
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hj]
        exact (mem_supportFamily a c).mp htG
      · exact congrArg (fun d : Cell K k => d.1.1) hj
  rw [← himage]
  exact (Finset.card_image_of_injective _ (fun i j hij =>
    s.face_injective (cell_vertices_injective hij))).symm

/-- A uniform family has cocycle parity when each one-size-larger set contains
an even number of its members. This formulation has no ordering indices. -/
def HasCocycleParity (r : ℕ) (G : Finset (Finset V)) : Prop :=
  ∀ s : Finset V, s.card = r + 1 → Even ((G.filter fun t => t ⊆ s).card)

/-- On the full simplex, the algebraic cocycle condition is exactly the paper's
even-parity condition for every `(k + 2)`-element vertex set. -/
theorem isCocycle_full_iff_parity (a : Cochain (⊤ : AbstractSimplicialComplex V) k) :
    IsCocycle a ↔ HasCocycleParity (k + 1) (supportFamily a) := by
  rw [isCocycle_iff_even]
  constructor
  · intro h s hs
    let c : Cell (⊤ : AbstractSimplicialComplex V) (k + 1) :=
      ⟨⟨s, by change s.Nonempty; exact Finset.card_pos.mp (by rw [hs]; omega)⟩, hs⟩
    have hc := h c
    rw [supportedFacetCount_eq_supportFamily] at hc
    exact hc
  · intro h s
    rw [supportedFacetCount_eq_supportFamily]
    exact h s.1.1 s.2

end FiniteParity

end OrderedParity

end SharpTopologicalOverlap.Simplicial
