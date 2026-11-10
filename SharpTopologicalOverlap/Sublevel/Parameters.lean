module

public import SharpTopologicalOverlap.Sublevel.Band
public import SharpTopologicalOverlap.Sublevel.PushInside
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-! # Choosing a Morse band for a compactly carried relative cycle

The only analytic input is the small-parameter critical-index estimate.
Every map and support bound in the resulting package is for the actual
barrier on the open simplex.
-/

@[expose] public noncomputable section

open CategoryTheory Set
open scoped Manifold unitInterval
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Sublevel

open Barrier

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The endpoint of the uniform push as a map of topological spaces. -/
def pushInsideMap (t : unitInterval) : TopCat.of (Simplex V) ⟶ TopCat.of (Simplex V) :=
  TopCat.ofHom ⟨pushInside t,
    continuous_pushInside.comp (continuous_const.prodMk continuous_id)⟩

/-- The push homotopy, parametrized on the whole unit interval. -/
def pushInsideHomotopy (t : unitInterval) :
    TopCat.Homotopy (𝟙 (TopCat.of (Simplex V))) (pushInsideMap t) where
  toFun q := pushInside (q.1 * t) q.2
  continuous_toFun := continuous_pushInside.comp
    ((continuous_fst.mul continuous_const).prodMk continuous_snd)
  map_zero_left μ := by simp
  map_one_left μ := by simp [pushInsideMap]

/-- Include the open coordinate simplex in the closed probability simplex. -/
def openSimplexInclusion : TopCat.of (openSimplexDomain (V := V)) ⟶
    TopCat.of (Simplex V) :=
  TopCat.ofHom ⟨fun z => (toPositiveSimplex z).1,
    continuous_subtype_val.comp openSimplexHomeomorph.continuous⟩

/-- The positive uniform push, expressed in the open coordinate chart. -/
def pushToOpenSimplex (t : unitInterval) (ht : 0 < (t : ℝ)) :
    TopCat.of (Simplex V) ⟶ TopCat.of (openSimplexDomain (V := V)) :=
  TopCat.ofHom ⟨fun μ => fromPositiveSimplex (pushInsidePositive t ht μ),
    openSimplexHomeomorph.symm.continuous.comp (pushInsidePositive t ht).continuous⟩

@[simp] theorem inclusion_pushToOpenSimplex (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ : Simplex V) :
    openSimplexInclusion (pushToOpenSimplex t ht μ) = pushInside t μ :=
  congrArg Subtype.val (openSimplexHomeomorph.apply_symm_apply (pushInsidePositive t ht μ))

theorem pushToOpenSimplex_comp_inclusion (t : unitInterval) (ht : 0 < (t : ℝ)) :
    pushToOpenSimplex t ht ≫ openSimplexInclusion = pushInsideMap (V := V) t := by
  apply TopCat.ext
  intro μ
  exact inclusion_pushToOpenSimplex t ht μ

@[simp] theorem barrier_pushToOpenSimplex (d : ℕ) (G : Finset (Finset V))
    (ε : ℝ) (α : V → ℝ) (t : unitInterval) (ht : 0 < (t : ℝ)) (μ : Simplex V) :
    barrier d G ε α (pushToOpenSimplex t ht μ) =
      ambientBarrier d G ε α ((pushInside t μ).weights : V → ℝ) := by
  rw [barrier_eq_ambient]
  exact congrArg (fun ν : Simplex V => ambientBarrier d G ε α (ν.weights : V → ℝ))
    (inclusion_pushToOpenSimplex t ht μ)

/-- The concrete choices needed by the final prism and neighborhood argument. -/
structure MorseBandData (d : ℕ) (G : Finset (Finset V)) (K U : Set (Simplex V))
    (κ γ : ℝ) where
  t₀ : unitInterval
  time_pos : 0 < (t₀ : ℝ)
  ε : ℝ
  epsilon_pos : 0 < ε
  α : V → ℝ
  tilt_sum : (∑ i, α i) = 0
  r₀ : ℝ
  r₁ : ℝ
  lower_level : r₀ ∈ Ioo (2 * γ) (3 * γ)
  upper_level : r₁ ∈ Ioo (overlapThreshold d - 2 * κ) (overlapThreshold d - κ)
  levels_ordered : r₀ ≤ r₁
  morse : TauCeti.IsMorse 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α)
  lower_regular : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V))
    𝓘(ℝ) (barrier d G ε α) r₀
  upper_regular : TauCeti.IsRegularValue 𝓘(ℝ, euclideanZeroSumSpace (V := V))
    𝓘(ℝ) (barrier d G ε α) r₁
  push_control : ∀ t : unitInterval, t ≤ t₀ → ∀ μ : Simplex V,
    |weightPolynomial (d + 1) G ((pushInside t μ).weights : V → ℝ) -
      weightPolynomial (d + 1) G (μ.weights : V → ℝ)| < γ
  homotopy_carrier : ∀ (t : unitInterval) (μ : Simplex V), μ ∈ K →
    pushInsideHomotopy t₀ (t, μ) ∈ strictSublevel d G
  homotopy_zero : ∀ (t : unitInterval) (μ : Simplex V), μ ∈ zeroSet d G →
    pushInsideHomotopy t₀ (t, μ) ∈ U
  push_carrier : ∀ μ ∈ K,
    pushToOpenSimplex t₀ time_pos μ ∈ barrierSublevel d G ε α r₁
  push_zero : ∀ μ ∈ zeroSet d G,
    pushToOpenSimplex t₀ time_pos μ ∈ barrierSublevel d G ε α r₀
  upper_carrier : ∀ z ∈ barrierSublevel d G ε α r₁,
    openSimplexInclusion z ∈ strictSublevel d G
  lower_carrier : ∀ z ∈ barrierSublevel d G ε α r₀,
    openSimplexInclusion z ∈ U
  band_fills : ∀ j ≤ d,
    Singular.Fills (X := TopCat.of (openSimplexDomain (V := V)))
      (barrierSublevel d G ε α r₁) (barrierSublevel d G ε α r₀) j

theorem exists_morseBandData (d : ℕ) (G : Finset (Finset V))
    (K U : Set (Simplex V)) {κ γ δ : ℝ}
    (hκ : 0 < κ) (hκθ : 4 * κ ≤ overlapThreshold d)
    (hγ : 0 < γ) (hγκ : γ < κ / 3)
    (hU : {μ : Simplex V | weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≤ 4 * γ} ⊆ U)
    (hK : ∀ μ ∈ K, weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≤
      overlapThreshold d - 4 * κ)
    (hδ : 0 < δ)
    (hpersist : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ α : V → ℝ,
      (∑ i, α i) = 0 → ‖α‖ < δ → ∀ z : openSimplexDomain (V := V),
      z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α) →
      barrier d G ε α z ∈ Icc (2 * γ) (overlapThreshold d - κ) →
      d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
        (barrier d G ε α) z) :
    Nonempty (MorseBandData d G K U κ γ) := by
  obtain ⟨t₀, ht₀, hpush⟩ := exists_pushInside_polynomial_control d G hγ
  let C : ℝ := (Fintype.card V : ℝ) * Real.log ((Fintype.card V : ℝ) / (t₀ : ℝ))
  obtain ⟨η, hη, hηC⟩ := exists_pos_mul_lt (show 0 < γ / 2 by linarith) (max C 0)
  let ε := min (δ / 2) η
  have hε : 0 < ε := lt_min (by linarith) hη
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hεC : ε * C < γ / 2 := by
    have h₁ : ε * C ≤ ε * max C 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hε.le
    have h₂ : ε * max C 0 ≤ η * max C 0 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (le_max_right _ _)
    nlinarith
  obtain ⟨α, hαsum, hα, hM⟩ := exists_small_morse_tilt d G ε
    (show 0 < min δ (γ / 2) from lt_min hδ (by linarith))
  have hαδ : ‖α‖ < δ := hα.trans_le (min_le_left _ _)
  have hαγ : ‖α‖ < γ / 2 := hα.trans_le (min_le_right _ _)
  obtain ⟨r₀, hr₀, hreg₀⟩ := exists_regular_barrier_level d G hε α hM
    (show 2 * γ < 3 * γ by linarith)
  obtain ⟨r₁, hr₁, hreg₁⟩ := exists_regular_barrier_level d G hε α hM
    (show overlapThreshold d - 2 * κ < overlapThreshold d - κ by linarith)
  have hlevels : r₀ ≤ r₁ := by linarith [hr₀.2, hr₁.1]
  have herror (μ : Simplex V) :
      |ambientBarrier d G ε α ((pushInside t₀ μ).weights : V → ℝ) -
        weightPolynomial (d + 1) G ((pushInside t₀ μ).weights : V → ℝ)| < γ := by
    have h := pushInside_barrier_error_le d G hε.le α ht₀ μ
    change _ ≤ ε * (Fintype.card V : ℝ) *
      Real.log ((Fintype.card V : ℝ) / (t₀ : ℝ)) + ‖α‖ at h
    have hbound : ε * (Fintype.card V : ℝ) *
        Real.log ((Fintype.card V : ℝ) / (t₀ : ℝ)) < γ / 2 := by
      simpa only [C, mul_assoc] using hεC
    linarith
  have hp_le (z : openSimplexDomain (V := V)) :
      weightPolynomial (d + 1) G ((openSimplexInclusion z).weights : V → ℝ) ≤
        barrier d G ε α z + ‖α‖ := by
    have hlog := mul_nonneg hε.le (logBarrier_nonneg (openSimplexInclusion z))
    have htilt := (abs_le.mp (linearTilt_abs_le_norm α (openSimplexInclusion z))).1
    rw [barrier_eq_ambient]
    change _ ≤ ambientBarrier d G ε α ((openSimplexInclusion z).weights : V → ℝ) + ‖α‖
    unfold ambientBarrier
    linarith
  have hindex : ∀ z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V))
      (barrier d G ε α) ∩ (barrier d G ε α) ⁻¹' Icc r₀ r₁,
      d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
        (barrier d G ε α) z := by
    intro z hz
    exact hpersist ε hε hεδ α hαsum hαδ z hz.1
      ⟨hr₀.1.le.trans hz.2.1, hz.2.2.trans hr₁.2.le⟩
  refine ⟨{
    t₀ := t₀
    time_pos := ht₀
    ε := ε
    epsilon_pos := hε
    α := α
    tilt_sum := hαsum
    r₀ := r₀
    r₁ := r₁
    lower_level := hr₀
    upper_level := hr₁
    levels_ordered := hlevels
    morse := hM
    lower_regular := hreg₀
    upper_regular := hreg₁
    push_control := hpush
    homotopy_carrier := ?_
    homotopy_zero := ?_
    push_carrier := ?_
    push_zero := ?_
    upper_carrier := ?_
    lower_carrier := ?_
    band_fills := fun j hj => barrier_band_fills d G hε α hM hlevels hreg₀ hreg₁ hindex hj }⟩
  · intro t μ hμ
    change weightPolynomial (d + 1) G ((pushInside (t * t₀) μ).weights : V → ℝ) < _
    have hp := (abs_lt.mp (hpush (t * t₀) unitInterval.mul_le_right μ)).2
    have hKμ := hK μ hμ
    linarith
  · intro t μ hμ
    apply hU
    change weightPolynomial (d + 1) G ((pushInside (t * t₀) μ).weights : V → ℝ) ≤ 4 * γ
    have hp := (abs_lt.mp (hpush (t * t₀) unitInterval.mul_le_right μ)).2
    change weightPolynomial (d + 1) G (μ.weights : V → ℝ) = 0 at hμ
    linarith
  · intro μ hμ
    change barrier d G ε α (pushToOpenSimplex t₀ ht₀ μ) ≤ r₁
    rw [barrier_pushToOpenSimplex]
    have hp := (abs_lt.mp (hpush t₀ le_rfl μ)).2
    have he := (abs_lt.mp (herror μ)).2
    have hKμ := hK μ hμ
    linarith [hr₁.1]
  · intro μ hμ
    change barrier d G ε α (pushToOpenSimplex t₀ ht₀ μ) ≤ r₀
    rw [barrier_pushToOpenSimplex]
    have hp := (abs_lt.mp (hpush t₀ le_rfl μ)).2
    have he := (abs_lt.mp (herror μ)).2
    change weightPolynomial (d + 1) G (μ.weights : V → ℝ) = 0 at hμ
    linarith [hr₀.1]
  · intro z hz
    change weightPolynomial (d + 1) G ((openSimplexInclusion z).weights : V → ℝ) < _
    change barrier d G ε α z ≤ r₁ at hz
    linarith [hp_le z, hr₁.2]
  · intro z hz
    apply hU
    change barrier d G ε α z ≤ r₀ at hz
    change weightPolynomial (d + 1) G ((openSimplexInclusion z).weights : V → ℝ) ≤ 4 * γ
    linarith [hp_le z, hr₀.2]

end SharpTopologicalOverlap.Sublevel
