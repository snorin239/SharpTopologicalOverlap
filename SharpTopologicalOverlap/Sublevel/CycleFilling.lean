module

public import SharpTopologicalOverlap.Singular.Prism
public import SharpTopologicalOverlap.Singular.Relative

/-! # The final chain argument for relative sublevel vanishing

After the analytic Morse band fills the pushed chain modulo a retracting
neighborhood, the prism brings it back and the neighborhood fills the
residual chain modulo the zero set. All chains remain in one ambient space.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace SharpTopologicalOverlap.Sublevel

open SharpTopologicalOverlap.Singular

variable {X : TopCat.{0}} {Z U B : Set X} {k : ℕ}

theorem refine_relative_filling (hUB : U ⊆ B) (hUZ : Fills U Z k)
    {c y : Chain X k} {w : Chain X (k + 1)}
    (hc : IsRelativeCycle Z k c) (hw : CarriedBy B w) (hy : CarriedBy U y)
    (heq : c = boundary k w + y) :
    ∃ (v : Chain X (k + 1)) (b : Chain X k),
      CarriedBy B v ∧ CarriedBy Z b ∧ c = boundary k v + b := by
  obtain ⟨w', b, hw'U, hbZ, hy'⟩ := hUZ y hy (remainder_isRelativeCycle hc heq)
  refine ⟨w + w', b, carriedBy_add hw (carriedBy_mono hUB hw'U), hbZ, ?_⟩
  rw [heq, hy', map_add]
  abel

/-- The chain-level assembly in the last paragraph of Theorem 5.1. The
endpoint filling is supplied by an actual Morse band, not an assumed
filling for the original relative cycle. -/
theorem fill_after_push (hUB : U ⊆ B) (hUZ : Fills U Z k)
    {g : X ⟶ X} (H : TopCat.Homotopy (𝟙 X) g)
    (hHZ : ∀ (t : unitInterval) (x : X), x ∈ Z → H (t, x) ∈ U)
    (c : Chain X k) (hc : IsRelativeCycle Z k c)
    (hP : CarriedBy B (prism H k c))
    (hend : ∃ (w : Chain X (k + 1)) (z : Chain X k),
      CarriedBy B w ∧ CarriedBy U z ∧ pushforward g k c = boundary k w + z) :
    ∃ (v : Chain X (k + 1)) (b : Chain X k),
      CarriedBy B v ∧ CarriedBy Z b ∧ c = boundary k v + b := by
  obtain ⟨w, z, hwB, hzU, heq⟩ := hend
  cases k with
  | zero =>
    have hp := prism_identity_zero H c
    rw [pushforward_id, heq] at hp
    apply refine_relative_filling hUB hUZ hc (carriedBy_add hP hwB) hzU
    rw [map_add]
    exact hp.trans (add_assoc _ _ _).symm
  | succ j =>
    have hbdU : CarriedBy U (prism H j (boundary j c)) := carriedBy_prism H hHZ hc
    have hp := prism_identity_succ H j c
    rw [pushforward_id, heq] at hp
    apply refine_relative_filling hUB hUZ hc (carriedBy_add hP hwB) (carriedBy_add hbdU hzU)
    rw [map_add]
    apply hp.trans
    abel

/-- Push the cycle into a Morse domain, fill its band pair there, and
transport the filling back to the original ambient space. -/
theorem endpoint_fill_of_push {M : TopCat.{0}} (a : X ⟶ M) (e : M ⟶ X) {g : X ⟶ X}
    (hcomp : a ≫ e = g) {A₀ A₁ : Set M} (hF : Fills A₁ A₀ k)
    (he₁ : Set.MapsTo e A₁ B) (he₀ : Set.MapsTo e A₀ U)
    (haZ : Set.MapsTo a Z A₀) (c : Chain X k) (hc : IsRelativeCycle Z k c)
    (haC : Set.MapsTo a (image c) A₁) :
    ∃ (w : Chain X (k + 1)) (z : Chain X k),
      CarriedBy B w ∧ CarriedBy U z ∧ pushforward g k c = boundary k w + z := by
  have hcarried : CarriedBy A₁ (pushforward a k c) := by
    apply carriedBy_mono _ (carriedBy_pushforward a
      ((carriedBy_iff_image_subset (image c) c).mpr Set.Subset.rfl))
    rintro _ ⟨x, hx, rfl⟩
    exact haC hx
  have hrelative : IsRelativeCycle A₀ k (pushforward a k c) := by
    cases k with
    | zero => trivial
    | succ j =>
      change CarriedBy A₀ (boundary j (pushforward a (j + 1) c))
      rw [boundary_pushforward]
      apply carriedBy_mono _ (carriedBy_pushforward a hc)
      rintro _ ⟨x, hx, rfl⟩
      exact haZ hx
  obtain ⟨w, z, hw, hz, heq⟩ := hF _ hcarried hrelative
  refine ⟨pushforward e (k + 1) w, pushforward e k z, ?_, ?_, ?_⟩
  · apply carriedBy_mono _ (carriedBy_pushforward e hw)
    rintro _ ⟨x, hx, rfl⟩
    exact he₁ hx
  · apply carriedBy_mono _ (carriedBy_pushforward e hz)
    rintro _ ⟨x, hx, rfl⟩
    exact he₀ hx
  · calc
      pushforward g k c = pushforward e k (pushforward a k c) := by
        rw [← pushforward_comp, hcomp]
      _ = pushforward e k (boundary k w + z) := congrArg (pushforward e k) heq
      _ = boundary k (pushforward e (k + 1) w) + pushforward e k z := by
        rw [map_add, boundary_pushforward]

end SharpTopologicalOverlap.Sublevel
