module

public import SharpTopologicalOverlap.Barrier.CriticalLimit
public import SharpTopologicalOverlap.Barrier.LimitIndex
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform persistence of the strict-sublevel index bound

The compactness argument takes limits of critical points and retains only the
Hessian directions in the support of the limit. No convergence of the full
barrier Hessian at disappearing coordinates is needed.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped Manifold
open SharpTopologicalOverlap.Spectral SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Barrier

variable {V : Type*} [Fintype V] [LinearOrder V]

attribute [local instance 1] Classical.propDecidable

theorem exists_barrier_index_persistence (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) {h₀ h₁ : ℝ}
    (h₀pos : 0 < h₀) (_h₀₁ : h₀ < h₁) (h₁θ : h₁ < overlapThreshold d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ α : V → ℝ, ‖α‖ < δ →
      ∀ ν : Simplex V, (∀ i, 0 < ν.weights i) → IsBarrierCritical d G ε α ν →
        ambientBarrier d G ε α (ν.weights : V → ℝ) ∈ Set.Icc h₀ h₁ →
          d + 1 ≤ sigNeg (barrierTangentForm d G ε ν) := by
  let : FirstCountableTopology (Simplex V) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).firstCountableTopology
  by_contra h
  push Not at h
  let cap : ℝ := 1 / ((Fintype.card V : ℝ) + 1)
  let δ : ℕ → ℝ := fun n => cap * (1 / ((n : ℝ) + 1))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hcap₁ : cap ≤ 1 := by
    dsimp [cap]
    exact (div_le_one (by positivity)).mpr (by
      have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      linarith)
  have hNcap : (Fintype.card V : ℝ) * cap ≤ 1 := by
    dsimp [cap]
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδcap (n : ℕ) : δ n ≤ cap := by
    apply mul_le_of_le_one_right hcap.le
    exact (div_le_one (by positivity)).mpr (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hex : ∀ n : ℕ, ∃ (ε : ℝ) (α : V → ℝ) (ν : Simplex V),
      0 < ε ∧ ε < δ n ∧ ‖α‖ < δ n ∧ (∀ i, 0 < ν.weights i) ∧
        IsBarrierCritical d G ε α ν ∧
          ambientBarrier d G ε α (ν.weights : V → ℝ) ∈ Set.Icc h₀ h₁ ∧
            sigNeg (barrierTangentForm d G ε ν) < d + 1 := by
    intro n
    obtain ⟨ε, hε, hεδ, α, hα, ν, hν, hc, hv, hi⟩ := h (δ n) (hδpos n)
    exact ⟨ε, α, ν, hε, hεδ, hα, hν, hc, hv, hi⟩
  choose ε α ν hε hεδ hα hν hc hv hi using hex
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => (hε n).le)
      (Eventually.of_forall fun n => (hεδ n).le) hδlim
  have hαlim : Tendsto α atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg (α n))
      (Eventually.of_forall fun n => (hα n).le) hδlim
  obtain ⟨μ, φ, hφ, hνlim⟩ := CompactSpace.tendsto_subseq ν
  have hεφ := hεlim.comp hφ.tendsto_atTop
  have hαφ := hαlim.comp hφ.tendsto_atTop
  have hcrit : ∀ᶠ n in atTop,
      0 < ε (φ n) ∧ (∀ i, 0 < (ν (φ n)).weights i) ∧
        IsBarrierCritical d G (ε (φ n)) (α (φ n)) (ν (φ n)) ∧
          (Fintype.card V : ℝ) * ε (φ n) ≤ 1 ∧ ‖α (φ n)‖ ≤ 1 := by
    apply Eventually.of_forall
    intro n
    refine ⟨hε _, hν _, hc _, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_left ((hεδ _).le.trans (hδcap _))
        (Nat.cast_nonneg _)).trans hNcap
    · exact (hα _).le.trans ((hδcap _).trans hcap₁)
  have hcritical : IsFaceCritical d G μ :=
    faceCritical_of_critical_limit d G hεφ hαφ hνlim (Eventually.of_forall fun n => hc (φ n))
  have hvalue := tendsto_critical_barrier_value d G hεφ hαφ hνlim hcrit
  have hband : weightPolynomial (d + 1) G (μ.weights : V → ℝ) ∈ Set.Icc h₀ h₁ :=
    isClosed_Icc.mem_of_tendsto hvalue (Eventually.of_forall fun n => hv (φ n))
  have hindex := faceCritical_index_ge d G hG hpar μ hcritical
    (h₀pos.trans_le hband.1) (hband.2.trans_lt h₁θ)
  have hevent := eventually_faceIndex_le_barrierIndex_of_tendsto d G μ hεφ hνlim
  obtain ⟨n, hn⟩ := hevent.exists
  exact (Nat.not_lt_of_ge (hindex.trans hn)) (hi (φ n))

section Manifold

variable [Nonempty V]

/-- Lemma 5.7 on the actual open-simplex manifold and with TauCeti's actual
Morse-index convention. The linear tilt need not satisfy a zero-sum condition. -/
theorem exists_manifold_index_persistence (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) {h₀ h₁ : ℝ}
    (h₀pos : 0 < h₀) (h₀₁ : h₀ < h₁) (h₁θ : h₁ < overlapThreshold d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ α : V → ℝ, ‖α‖ < δ →
      ∀ z : openSimplexDomain (V := V),
        z ∈ TauCeti.criticalPoints 𝓘(ℝ, euclideanZeroSumSpace (V := V)) (barrier d G ε α) →
          barrier d G ε α z ∈ Set.Icc h₀ h₁ →
            d + 1 ≤ TauCeti.manifoldMorseIndex 𝓘(ℝ, euclideanZeroSumSpace (V := V))
              (barrier d G ε α) z := by
  obtain ⟨δ, hδ, hpersist⟩ := exists_barrier_index_persistence d G hG hpar h₀pos h₀₁ h₁θ
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ α hα z hc hv
  rw [manifoldMorseIndex_barrier]
  apply hpersist ε hε hεδ α hα (toPositiveSimplex z).1 (toPositiveSimplex z).2
  · exact (barrier_critical_iff d G ε α z).mp
      (TauCeti.mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.mp hc)
  · simpa only [barrier_eq_ambient] using hv

end Manifold

end SharpTopologicalOverlap.Barrier
