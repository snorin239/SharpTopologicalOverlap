module

public import SharpTopologicalOverlap.BMN.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! # Change of coordinates for BMN configurations -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

variable {V E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem mem_convexHull_image_linearEquiv_iff (e : E ≃ₗ[ℝ] F) (p : V → E)
    (s : Set V) (r : F) :
    r ∈ convexHull ℝ ((e ∘ p) '' s) ↔ e.symm r ∈ convexHull ℝ (p '' s) := by
  have himage : (e ∘ p) '' s = e '' (p '' s) := by
    simpa only [Function.comp_def] using (Set.image_image (e : E → F) p s).symm
  have he := e.toLinearMap.image_convexHull (p '' s)
  simp only [LinearEquiv.coe_toLinearMap] at he
  rw [himage, ← he]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hx
    exact ⟨e.symm r, hx, e.apply_symm_apply r⟩

theorem convexIndependent_linearEquiv (e : E ≃ₗ[ℝ] F) {p : V → E}
    (hp : ConvexIndependent ℝ p) : ConvexIndependent ℝ (e ∘ p) := by
  intro s i hi
  apply hp s i
  have h := (mem_convexHull_image_linearEquiv_iff e p s (e (p i))).mp hi
  simpa using h

theorem affineIndependent_linearEquiv (e : E ≃ₗ[ℝ] F) {p : V → E}
    (hp : AffineIndependent ℝ p) : AffineIndependent ℝ (e ∘ p) :=
  e.toAffineEquiv.affineIndependent_iff.mpr hp

/-- In convex position, different source subsets span different convex hulls. -/
theorem convexHull_injective_of_convexIndependent {p : V → E}
    (hp : ConvexIndependent ℝ p) :
    Function.Injective (fun σ : Finset V => convexHull ℝ (p '' (σ : Set V))) := by
  classical
  intro σ τ h
  change convexHull ℝ (p '' (σ : Set V)) = convexHull ℝ (p '' (τ : Set V)) at h
  ext i
  change i ∈ (σ : Set V) ↔ i ∈ (τ : Set V)
  rw [← hp.mem_convexHull_iff (σ : Set V) i,
    ← hp.mem_convexHull_iff (τ : Set V) i, h]

variable [Fintype V]

@[simp] theorem hullFacesAt_linearEquiv (d : ℕ) (e : E ≃ₗ[ℝ] F)
    (p : V → E) (r : F) :
    hullFacesAt d (e ∘ p) r = hullFacesAt d p (e.symm r) := by
  classical
  ext σ
  simp only [mem_hullFacesAt, mem_convexHull_image_linearEquiv_iff]

@[simp] theorem hullCount_linearEquiv (d : ℕ) (e : E ≃ₗ[ℝ] F)
    (p : V → E) (r : F) :
    hullCount d (e ∘ p) r = hullCount d p (e.symm r) := by
  simp only [hullCount, hullFacesAt_linearEquiv]

end SharpTopologicalOverlap.BMN
