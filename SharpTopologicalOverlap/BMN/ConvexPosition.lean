module

public import SharpTopologicalOverlap.BMN.Configuration

/-! # Convex position of separated configurations -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

/-- A functional exposing a point using its first two coordinates. -/
def exposingFunctional {d : ℕ} (a b : Fin d) (x y : ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun z := x * z b - 2 * y * z a
  map_add' z w := by simp only [Pi.add_apply]; ring
  map_smul' c z := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem exposingFunctional_apply {d : ℕ} (a b : Fin d)
    (x y : ℝ) (z : Fin d → ℝ) :
    exposingFunctional a b x y z = x * z b - 2 * y * z a := rfl

theorem exposingFunctional_lt {d n : ℕ} (hd : 2 ≤ d)
    {p : Fin n → Fin d → ℝ} (hp : Separated p) (i k : Fin n) (hki : k ≠ i) :
    let a : Fin d := ⟨0, by omega⟩
    let b : Fin d := ⟨1, by omega⟩
    exposingFunctional a b (p i a) (p i b) (p i) <
      exposingFunctional a b (p i a) (p i b) (p k) := by
  dsimp only
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  change exposingFunctional a b (p i a) (p i b) (p i) <
    exposingFunctional a b (p i a) (p i b) (p k)
  simp only [exposingFunctional_apply]
  have hxi := hp.one_lt i a
  have hyi := hp.one_lt i b
  have hxk := hp.one_lt k a
  have hyk := hp.one_lt k b
  rcases lt_or_gt_of_ne hki with h | h
  · have hdouble : 2 * p k a < p i a :=
      (growth_two_mul_lt hd hxk).trans (hp.gap k i a a (Or.inr ⟨rfl, h⟩))
    nlinarith [mul_pos (by linarith : 0 < p i a) (by linarith : 0 < p k b)]
  · have hcross : p k a < p i b := hp.cross_coordinate_lt k i (by
      change (0 : ℕ) < 1
      omega)
    have hsquare : 4 * (p i b) ^ 2 < p k b :=
      (growth_four_sq_lt hd hyi).trans (hp.gap i k b b (Or.inr ⟨rfl, h⟩))
    have hprod : 0 < p i a * p i b := mul_pos (by linarith) (by linarith)
    have hxy : p k b < p i a * p k b := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hcross (by linarith : 0 < p i b)]

theorem convexIndependent_of_separated {d n : ℕ} (hd : 2 ≤ d)
    {p : Fin n → Fin d → ℝ} (hp : Separated p) : ConvexIndependent ℝ p := by
  classical
  intro s i hi
  by_contra hnot
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  let f := exposingFunctional a b (p i a) (p i b)
  have hstrict : ∀ k ∈ s, f (p i) < f (p k) := by
    intro k hk
    have hki : k ≠ i := by
      intro heq
      exact hnot (heq ▸ hk)
    exact exposingFunctional_lt hd hp i k hki
  have hsubset : convexHull ℝ (p '' s) ⊆ {z | f (p i) < f z} := by
    apply convexHull_min
    · rintro _ ⟨k, hk, rfl⟩
      exact hstrict k hk
    · exact convex_halfSpace_gt f.isLinear (f (p i))
  have hbad := hsubset hi
  change f (p i) < f (p i) at hbad
  exact (lt_irrefl _) hbad

theorem configuration_convexIndependent {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ConvexIndependent ℝ (configuration d n) :=
  convexIndependent_of_separated hd (configuration_separated d n)

end SharpTopologicalOverlap.BMN
