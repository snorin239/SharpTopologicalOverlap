module

public import SharpTopologicalOverlap.Barrier.Basic
public import TauCeti.Analysis.Calculus.Morse.Generic

/-! # Arbitrarily small Morse tilts

The exact finite-dimensional linear-perturbation theorem from TauCeti supplies
the Sard argument. Euclidean tangent vectors give zero-sum coordinate tilts,
and their coordinate sup norm is bounded by their Euclidean norm.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold Topology InnerProductSpace
open TauCeti SharpTopologicalOverlap.Spectral

namespace SharpTopologicalOverlap.Barrier

theorem isMorse_openSubtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (F : E → ℝ)
    (hF : ContDiffOn ℝ ∞ F U) (hND : HasNondegenerateCriticalPointsOn F U) :
    IsMorse 𝓘(ℝ, E) (F ∘ Subtype.val : U → ℝ) := by
  apply isMorse_iff.mpr
  refine ⟨hF.contMDiffOn.comp_contMDiff contMDiff_subtype_val Subtype.prop, ?_⟩
  intro x hx
  rw [openSubtype_fderiv_coordinate] at hx
  have hcrit := (hasNondegenerateCriticalPointsOn_iff.mp hND) x.2 hx
  rw [isManifoldNondegenerateCriticalPoint_iff, openSubtype_chart_point]
  exact hcrit.congr_of_eventuallyEq (openSubtype_coordinate_germ U F x).symm

variable {V : Type*} [Fintype V] [Nonempty V]

omit [Nonempty V] in
theorem tangentCoordinates_norm_le (v : euclideanZeroSumSpace (V := V)) :
    ‖tangentCoordinates v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact PiLp.norm_apply_le v.1 i

theorem linearTilt_tangent_affine (v z : euclideanZeroSumSpace (V := V)) :
    linearTilt (tangentCoordinates v) (affineCoordinates z) = ⟪v, z⟫_ℝ := by
  change (∑ i, v.1 i * ((uniform : Simplex V).weights i + z.1 i)) = ⟪v.1, z.1⟫_ℝ
  simp only [mul_add, Finset.sum_add_distrib, coordinate_uniform]
  have hz : (∑ i, v.1 i * (Fintype.card V : ℝ)⁻¹) = 0 := by
    rw [← Finset.sum_mul, show (∑ i, v.1 i) = 0 from v.2, zero_mul]
  rw [hz, zero_add, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Nonempty V] in
@[simp] theorem linearTilt_zero (x : V → ℝ) : linearTilt 0 x = 0 := by simp [linearTilt]

omit [Nonempty V] in
theorem linearTilt_neg_left (α x : V → ℝ) : linearTilt (-α) x = -linearTilt α x := by
  simp [linearTilt, Finset.sum_neg_distrib]

theorem coordinateBarrier_neg_tangent_tilt (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    (v z : euclideanZeroSumSpace (V := V)) :
    coordinateBarrier d G ε (-tangentCoordinates v) z =
      coordinateBarrier d G ε 0 z - ⟪v, z⟫_ℝ := by
  change WeightPolynomial.weightPolynomial (d + 1) G (affineCoordinates z) +
      ε * logBarrier (affineCoordinates z) + linearTilt (-tangentCoordinates v) (affineCoordinates z) =
    (WeightPolynomial.weightPolynomial (d + 1) G (affineCoordinates z) +
      ε * logBarrier (affineCoordinates z) + linearTilt 0 (affineCoordinates z)) - ⟪v, z⟫_ℝ
  rw [linearTilt_neg_left, linearTilt_tangent_affine, linearTilt_zero, add_zero, sub_eq_add_neg]

/-- Lemma 5.6(c): a zero-sum tilt of arbitrarily small coordinate sup norm
makes the actual barrier on the open simplex a Morse function. -/
theorem exists_small_morse_tilt (d : ℕ) (G : Finset (Finset V)) (ε : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : V → ℝ, (∑ i, α i) = 0 ∧ ‖α‖ < δ ∧
      IsMorse 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α) := by
  obtain ⟨v, hvnorm, hvM⟩ := exists_norm_lt_hasNondegenerateCriticalPointsOn_sub_inner
    (openSimplexDomain (V := V)).isOpen (contDiffOn_coordinateBarrier d G ε 0 2) hδ
  let α : V → ℝ := -tangentCoordinates v
  refine ⟨α, ?_, ?_, ?_⟩
  · simp only [α, Pi.neg_apply, Finset.sum_neg_distrib, sum_tangentCoordinates, neg_zero]
  · have hnorm : ‖α‖ ≤ ‖v‖ := by
      simpa only [α, norm_neg] using tangentCoordinates_norm_le v
    exact hnorm.trans_lt hvnorm
  · apply isMorse_openSubtype _ _ (contDiffOn_coordinateBarrier d G ε α ∞)
    have hfun : coordinateBarrier d G ε α =
        fun z => coordinateBarrier d G ε 0 z - ⟪v, z⟫_ℝ :=
      funext fun z => coordinateBarrier_neg_tangent_tilt d G ε v z
    rw [hfun]
    exact hvM

end SharpTopologicalOverlap.Barrier
