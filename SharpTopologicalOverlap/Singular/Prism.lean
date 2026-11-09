module

public import SharpTopologicalOverlap.Singular
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! # A support-controlled singular prism

The operator is the existing simplicial chain homotopy. Naturality for maps
of topological pairs proves the carrier bound, including for the actual
image of an individual chain.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology

namespace SharpTopologicalOverlap.Singular

variable {X Y : TopCat.{0}} {f g : X ⟶ Y}

abbrev chainHomotopy (H : TopCat.Homotopy f g) :=
  H.toSSet.chainComplexMap (ModuleCat.of Coeff Coeff)

/-- The prism raises degree by one. -/
def prism (H : TopCat.Homotopy f g) (k : ℕ) : Chain X k →ₗ[Coeff] Chain Y (k + 1) :=
  ((chainHomotopy H).hom k (k + 1)).hom

theorem prism_identity_zero (H : TopCat.Homotopy f g) (c : Chain X 0) :
    pushforward f 0 c = boundary 0 (prism H 0 c) + pushforward g 0 c := by
  have h := (chainHomotopy H).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  exact congrArg (fun a => a.hom c) h

theorem prism_identity_succ (H : TopCat.Homotopy f g) (k : ℕ) (c : Chain X (k + 1)) :
    pushforward f (k + 1) c = prism H k (boundary k c) +
      boundary (k + 1) (prism H (k + 1) c) + pushforward g (k + 1) c := by
  have h := (chainHomotopy H).comm (k + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  exact congrArg (fun a => a.hom c) h

theorem boundary_prism_zero (H : TopCat.Homotopy f g) (c : Chain X 0) :
    boundary 0 (prism H 0 c) = pushforward f 0 c + pushforward g 0 c := by
  have h := congrArg (fun a => a + pushforward g 0 c) (prism_identity_zero H c)
  simpa only [add_assoc, add_self, add_zero] using h.symm

theorem boundary_prism_succ (H : TopCat.Homotopy f g) (k : ℕ) (c : Chain X (k + 1)) :
    boundary (k + 1) (prism H (k + 1) c) + prism H k (boundary k c) =
      pushforward f (k + 1) c + pushforward g (k + 1) c := by
  have h := congrArg (fun a => a + pushforward g (k + 1) c) (prism_identity_succ H k c)
  have h' : prism H k (boundary k c) + boundary (k + 1) (prism H (k + 1) c) =
      pushforward f (k + 1) c + pushforward g (k + 1) c := by
    simpa only [add_assoc, add_self, add_zero] using h.symm
  exact (add_comm _ _).trans h'

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting a homotopy to source and target carriers commutes with its prism. -/
theorem carriedBy_prism (H : TopCat.Homotopy f g) {A : Set X} {B : Set Y}
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B)
    {k : ℕ} {c : Chain X k} (hc : CarriedBy A c) :
    CarriedBy B (prism H k c) := by
  let fA : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom
    ⟨fun x => ⟨f x, H.apply_zero x ▸ hH 0 x x.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let gA : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom
    ⟨fun x => ⟨g x, H.apply_one x ▸ hH 1 x x.property⟩,
      (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let HA : TopCat.Homotopy fA gA :=
    { toFun := fun p => ⟨H (p.1, p.2), hH p.1 p.2 p.2.property⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Subtype.ext (H.apply_zero x)
      map_one_left := fun x => Subtype.ext (H.apply_one x) }
  let pf : TopPair.ofSubset A ⟶ TopPair.ofSubset B := TopPair.ofHom f fA (by ext; rfl)
  let pg : TopPair.ofSubset A ⟶ TopPair.ofSubset B := TopPair.ofHom g gA (by ext; rfl)
  let HP : TopPair.Homotopy pf pg := { fst := H, snd := HA, w := by ext; rfl }
  obtain ⟨b, rfl⟩ := hc
  refine ⟨prism HP.snd k b, ?_⟩
  have h := SSet.Homotopy.chainComplexMap_hom_comm HP.toSSetPair.left HP.toSSetPair.right
    HP.toSSetPair.w (ModuleCat.of Coeff Coeff) k (k + 1)
  rw [TopPair.Homotopy.toSSetPair_left, TopPair.Homotopy.toSSetPair_right] at h
  exact (congrArg (fun a => a.hom b) h).symm

/-- The image of the prism is contained in the homotopy tracks of the chain's
own image. This is a carrier bound even when simplices cancel in the prism. -/
theorem image_prism_subset (H : TopCat.Homotopy f g) {k : ℕ} (c : Chain X k) :
    image (prism H k c) ⊆ H '' (Set.univ ×ˢ image c) := by
  apply (carriedBy_iff_image_subset _ _).mp
  apply carriedBy_prism H
  · intro t x hx
    exact Set.mem_image_of_mem H ⟨Set.mem_univ t, hx⟩
  · exact (carriedBy_iff_image_subset _ _).mpr Set.Subset.rfl

end SharpTopologicalOverlap.Singular
