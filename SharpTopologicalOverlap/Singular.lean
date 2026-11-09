module

public import SharpTopologicalOverlap.Simplicial
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Subspace

/-! # Singular chains and their carriers

The chains are the actual degree objects of TauCeti's singular chain complex.
A carrier means membership in the image of a subspace inclusion, rather than
a new abstract support condition. The concrete support description below
identifies this with the image convention in §2.3 of the manuscript.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Simplicial

namespace SharpTopologicalOverlap.Singular

abbrev Coeff := Simplicial.Coeff

abbrev Chain (X : TopCat.{0}) (k : ℕ) := ((TauCeti.singularChains Coeff).obj X).X k

abbrev Simplex (X : TopCat.{0}) (k : ℕ) := (TopCat.toSSet.obj X) _⦋k⦌

variable {X Y Z : TopCat.{0}} {k : ℕ}

@[simp] theorem add_self (c : Chain X k) : c + c = 0 := by
  have htwo : (2 : Coeff) = 0 := by decide
  calc
    c + c = (2 : Coeff) • c := (two_smul Coeff c).symm
    _ = 0 := by rw [htwo, zero_smul]

abbrev coefficients (X : TopCat.{0}) (k : ℕ) : Chain X k ≃ₗ[Coeff] (Simplex X k →₀ Coeff) :=
  (TopCat.toSSet.obj X).chainsLinearEquivFinsupp Coeff k

abbrev pushforward (f : X ⟶ Y) (k : ℕ) : Chain X k →ₗ[Coeff] Chain Y k :=
  (((TauCeti.singularChains Coeff).map f).f k).hom

abbrev boundary (k : ℕ) : Chain X (k + 1) →ₗ[Coeff] Chain X k :=
  (((TauCeti.singularChains Coeff).obj X).d (k + 1) k).hom

theorem boundary_boundary (c : Chain X (k + 2)) : boundary k (boundary (k + 1) c) = 0 := by
  exact ConcreteCategory.congr_hom
    (((TauCeti.singularChains Coeff).obj X).d_comp_d (k + 2) (k + 1) k) c

theorem boundary_pushforward (f : X ⟶ Y) (c : Chain X (k + 1)) :
    boundary k (pushforward f (k + 1) c) = pushforward f k (boundary k c) := by
  exact ConcreteCategory.congr_hom (((TauCeti.singularChains Coeff).map f).comm (k + 1) k) c

theorem pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (c : Chain X k) :
    pushforward (f ≫ g) k c = pushforward g k (pushforward f k c) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun h => h.f k) ((TauCeti.singularChains Coeff).map_comp f g)) c

@[simp] theorem pushforward_id (c : Chain X k) : pushforward (𝟙 X) k c = c := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun h => h.f k) ((TauCeti.singularChains Coeff).map_id X)) c

theorem coefficients_pushforward (f : X ⟶ Y) (c : Chain X k) :
    coefficients Y k (pushforward f k c) =
      Finsupp.mapDomain ((TopCat.toSSet.map f).app _) (coefficients X k c) :=
  SSet.chainsLinearEquivFinsupp_chainComplexMap_f _ _ _

abbrev inclusion (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom (ContinuousMap.subtypeVal A)

/-- Chains coming from the indicated subspace of the one ambient space. -/
def CarriedBy (A : Set X) (c : Chain X k) : Prop := c ∈ LinearMap.range (pushforward (inclusion A) k)

theorem carriedBy_iff_exists (A : Set X) (c : Chain X k) :
    CarriedBy A c ↔ ∃ b : Chain (TopCat.of A) k, pushforward (inclusion A) k b = c := Iff.rfl

@[simp] theorem carriedBy_zero (A : Set X) : CarriedBy A (0 : Chain X k) :=
  (LinearMap.range _).zero_mem

theorem carriedBy_add {A : Set X} {c b : Chain X k}
    (hc : CarriedBy A c) (hb : CarriedBy A b) : CarriedBy A (c + b) :=
  (LinearMap.range _).add_mem hc hb

theorem carriedBy_smul {A : Set X} {c : Chain X k} (r : Coeff)
    (hc : CarriedBy A c) : CarriedBy A (r • c) := (LinearMap.range _).smul_mem r hc

theorem carriedBy_boundary {A : Set X} {c : Chain X (k + 1)}
    (hc : CarriedBy A c) : CarriedBy A (boundary k c) := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨boundary k b, (boundary_pushforward _ _).symm⟩

theorem carriedBy_mono {A B : Set X} (hAB : A ⊆ B) {c : Chain X k}
    (hc : CarriedBy A c) : CarriedBy B c := by
  obtain ⟨b, rfl⟩ := hc
  let f : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom ⟨Set.inclusion hAB, continuous_inclusion hAB⟩
  refine ⟨pushforward f k b, ?_⟩
  rw [← pushforward_comp]
  rfl

theorem simplexMap_injective {f : X ⟶ Y} (hf : Function.Injective f) :
    Function.Injective ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk k))) := by
  intro s t h
  apply (X.toSSetObjEquiv _).injective
  ext z
  apply hf
  have hz := congrArg (fun a => Y.toSSetObjEquiv _ a z) h
  simpa only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply] using hz

theorem pushforward_injective {f : X ⟶ Y} (hf : Function.Injective f) :
    Function.Injective (pushforward f k) := by
  intro c b h
  apply (coefficients X k).injective
  apply Finsupp.mapDomain_injective (simplexMap_injective hf)
  simpa only [← coefficients_pushforward] using congrArg (coefficients Y k) h

theorem inclusion_injective (A : Set X) : Function.Injective (pushforward (inclusion A) k) :=
  pushforward_injective Subtype.val_injective

/-- A chain's image is the finite union of the images of its nonzero simplices. -/
def image (c : Chain X k) : Set X :=
  ⋃ s ∈ (coefficients X k c).support, Set.range (X.toSSetObjEquiv _ s)

theorem carriedBy_iff_support (A : Set X) (c : Chain X k) :
    CarriedBy A c ↔ ∀ s ∈ (coefficients X k c).support,
      Set.range (X.toSSetObjEquiv _ s) ⊆ A := by
  let f := (TopCat.toSSet.map (inclusion A)).app (Opposite.op (SimplexCategory.mk k))
  have hf : Function.Injective f := simplexMap_injective Subtype.val_injective
  have hr : ∀ s : Simplex X k, s ∈ Set.range f ↔ Set.range (X.toSSetObjEquiv _ s) ⊆ A := by
    intro s
    exact TopCat.mem_range_toSSet_subtypeVal_iff A _ s
  constructor
  · rintro ⟨b, rfl⟩ s hs
    apply (hr s).mp
    exact Finsupp.mem_range_of_mapDomain_ne_zero (f := f)
      (x := coefficients (TopCat.of A) k b)
      (by rw [← coefficients_pushforward]; exact Finsupp.mem_support_iff.mp hs)
  · intro hc
    have hzero : ∀ s ∉ Set.range f, coefficients X k c s = 0 := by
      intro s hs
      by_contra h
      exact hs ((hr s).mpr (hc s (Finsupp.mem_support_iff.mpr h)))
    obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff f hf _).mpr hzero
    refine ⟨(coefficients (TopCat.of A) k).symm b, ?_⟩
    apply (coefficients X k).injective
    rw [coefficients_pushforward, LinearEquiv.apply_symm_apply]
    exact hb

theorem carriedBy_iff_image_subset (A : Set X) (c : Chain X k) :
    CarriedBy A c ↔ image c ⊆ A := by
  rw [carriedBy_iff_support]
  simp only [image, Set.iUnion_subset_iff]

theorem isCompact_image (c : Chain X k) : IsCompact (image c) := by
  classical
  apply Set.Finite.isCompact_biUnion (Finset.finite_toSet _)
  intro s _
  exact isCompact_range (map_continuous (X.toSSetObjEquiv _ s))

@[simp] theorem image_zero : image (0 : Chain X k) = ∅ := by
  simp [image]

theorem image_add_subset (c b : Chain X k) : image (c + b) ⊆ image c ∪ image b := by
  classical
  intro x hx
  obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
  have hs' : s ∈ (coefficients X k c).support ∪ (coefficients X k b).support :=
    Finsupp.support_add (by simpa using hs)
  rcases Finset.mem_union.mp hs' with hs' | hs'
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨s, hs', hx⟩)
  · exact Or.inr (Set.mem_iUnion₂.mpr ⟨s, hs', hx⟩)

theorem carriedBy_pushforward (f : X ⟶ Y) {A : Set X} {c : Chain X k}
    (hc : CarriedBy A c) : CarriedBy (f '' A) (pushforward f k c) := by
  obtain ⟨b, rfl⟩ := hc
  let g : TopCat.of A ⟶ TopCat.of (f '' A) := TopCat.ofHom
    ⟨fun x => ⟨f x, Set.mem_image_of_mem f x.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨pushforward g k b, ?_⟩
  rw [← pushforward_comp, ← pushforward_comp]
  rfl

theorem image_pushforward_subset (f : X ⟶ Y) (c : Chain X k) :
    image (pushforward f k c) ⊆ f '' image c :=
  (carriedBy_iff_image_subset _ _).mp
    (carriedBy_pushforward f ((carriedBy_iff_image_subset _ _).mpr Set.Subset.rfl))

/-- The relative cycle convention also covers degree zero: every zero-chain
is a relative cycle in the unaugmented complex. -/
def IsRelativeCycle (A : Set X) (k : ℕ) : Chain X k → Prop :=
  Nat.rec (motive := fun j => Chain X j → Prop) (fun _ => True)
    (fun j _ c => CarriedBy A (boundary j c)) k

@[simp] theorem isRelativeCycle_zero (A : Set X) (c : Chain X 0) :
    IsRelativeCycle A 0 c := trivial

@[simp] theorem isRelativeCycle_succ (A : Set X) (c : Chain X (k + 1)) :
    IsRelativeCycle A (k + 1) c ↔ CarriedBy A (boundary k c) := Iff.rfl

end SharpTopologicalOverlap.Singular
