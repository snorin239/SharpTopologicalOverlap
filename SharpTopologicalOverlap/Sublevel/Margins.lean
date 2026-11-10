module

public import SharpTopologicalOverlap.Sublevel.Definitions
public import SharpTopologicalOverlap.Singular

/-! # Compact carrier margins for a relative sublevel cycle -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Singular

open CategoryTheory _root_.SharpTopologicalOverlap.Simplicial

theorem image_nonempty_of_ne_zero {X : TopCat.{0}} {k : ℕ} {c : Chain X k} (hc : c ≠ 0) :
    (image c).Nonempty := by
  classical
  have hcoeff : coefficients X k c ≠ 0 := by
    intro h
    exact hc ((coefficients X k).injective (h.trans (map_zero _).symm))
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  let z : SharpTopologicalOverlap.Simplex (Fin (k + 1)) := vertex ⟨0, by omega⟩
  exact ⟨X.toSSetObjEquiv _ s z, Set.mem_iUnion₂.mpr ⟨s, hs, ⟨z, rfl⟩⟩⟩

end SharpTopologicalOverlap.Singular

namespace SharpTopologicalOverlap.Sublevel

open WeightPolynomial

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem exists_chain_margin (d : ℕ) (G : Finset (Finset V)) {k : ℕ}
    (c : Singular.Chain (TopCat.of (Simplex V)) k)
    (hc : Singular.CarriedBy (strictSublevel d G) c) (hne : c ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ 4 * κ ≤ overlapThreshold d ∧
      ∀ μ ∈ Singular.image c,
        weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≤ overlapThreshold d - 4 * κ := by
  let P : Simplex V → ℝ := fun μ => weightPolynomial (d + 1) G (μ.weights : V → ℝ)
  have hP : Continuous P := (WeightPolynomial.contDiff (d + 1) G 0).continuous.comp
    coordinateHomeomorph.continuous.subtype_val
  obtain ⟨μ₀, hμ₀, hmax⟩ := (Singular.isCompact_image c).exists_isMaxOn
    (Singular.image_nonempty_of_ne_zero hne) hP.continuousOn
  have hsmall : P μ₀ < overlapThreshold d :=
    (Singular.carriedBy_iff_image_subset _ _).mp hc hμ₀
  have hnonneg : 0 ≤ P μ₀ := WeightPolynomial.nonneg (d + 1) G (coordinate_nonneg μ₀)
  refine ⟨(overlapThreshold d - P μ₀) / 4, by linarith, by linarith, ?_⟩
  intro μ hμ
  have h := hmax hμ
  change P μ ≤ P μ₀ at h
  change P μ ≤ _
  linarith

end SharpTopologicalOverlap.Sublevel
