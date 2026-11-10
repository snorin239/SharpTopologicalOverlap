module

public import SharpTopologicalOverlap.Sublevel.Definitions
public import SharpTopologicalOverlap.Comparison.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.IteratedNeighborhood

/-! # A small retracting neighbourhood of the polynomial zero set

This transports TauCeti's cofinal iterated simplicial neighbourhoods through
the coordinate-preserving full-simplex realization homeomorphism.
-/

@[expose] public noncomputable section

open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Sublevel

variable {V : Type} [Fintype V] [DecidableEq V]

theorem realizedComplex_top :
    realizedComplex (⊤ : AbstractSimplicialComplex V).toPreAbstractSimplicialComplex = Set.univ := by
  ext μ
  exact iff_of_true (support_nonempty μ) (Set.mem_univ μ)

/-- The weak realization of the full simplex is the coordinate simplex. -/
def fullSimplexHomeomorph : (⊤ : AbstractSimplicialComplex V).Realization ≃ₜ Simplex V :=
  (Comparison.realizedComplexHomeomorph ⊤).trans
    ((Homeomorph.setCongr realizedComplex_top).trans (Homeomorph.Set.univ _))

@[simp] theorem fullSimplexHomeomorph_weights
    (x : (⊤ : AbstractSimplicialComplex V).Realization) :
    (fullSimplexHomeomorph x).weights = x.1 := rfl

theorem image_independence_polyhedron (d : ℕ) (G : Finset (Finset V)) :
    fullSimplexHomeomorph ''
      {x : (⊤ : AbstractSimplicialComplex V).Realization |
        x.1.support ∈ independenceComplex (d + 1) G} = zeroSet d G := by
  ext μ
  constructor
  · rintro ⟨x, hx, rfl⟩
    change weightPolynomial (d + 1) G ((fullSimplexHomeomorph x).weights : V → ℝ) = 0
    have hmem : fullSimplexHomeomorph x ∈ realizedComplex (independenceComplex (d + 1) G) := hx
    rwa [realized_independenceComplex] at hmem
  · intro hμ
    refine ⟨fullSimplexHomeomorph.symm μ, ?_, fullSimplexHomeomorph.apply_symm_apply μ⟩
    have hmem : μ ∈ realizedComplex (independenceComplex (d + 1) G) := by
      rwa [realized_independenceComplex]
    have heq : (fullSimplexHomeomorph.symm μ).1 = μ.weights := by
      have h := congrArg Convexity.StdSimplex.weights (fullSimplexHomeomorph.apply_symm_apply μ)
      exact h
    change (fullSimplexHomeomorph.symm μ).1.support ∈ independenceComplex (d + 1) G
    rw [heq]
    exact hmem

theorem isOpen_strictSublevel (d : ℕ) (G : Finset (Finset V)) :
    IsOpen (strictSublevel d G : Set (Simplex V)) := by
  have hc : Continuous (fun μ : Simplex V => weightPolynomial (d + 1) G (μ.weights : V → ℝ)) :=
    (WeightPolynomial.contDiff (d + 1) G 0).continuous.comp
      coordinateHomeomorph.continuous.subtype_val
  exact isOpen_lt hc continuous_const

/-- The open set `U` in the first paragraph of the proof of Theorem 5.1,
together with its actual strong deformation retraction onto `Z={p=0}`. -/
theorem exists_retracting_neighborhood (d : ℕ) (G : Finset (Finset V)) :
    ∃ (U : Set (Simplex V)) (hZU : zeroSet d G ⊆ U),
      IsOpen U ∧ U ⊆ strictSublevel d G ∧
      ∃ r : C(U, zeroSet d G),
        (∀ z, r (ContinuousMap.inclusion hZU z) = z) ∧
        Nonempty (((ContinuousMap.inclusion hZU).comp r).HomotopyRel (.id U)
          {z | (z : Simplex V) ∈ zeroSet d G}) := by
  let K : AbstractSimplicialComplex V := ⊤
  let P := independenceComplex (d + 1) G
  let e := fullSimplexHomeomorph (V := V)
  let Z : Set K.Realization := {x | x.1.support ∈ P}
  let B : Set K.Realization := e ⁻¹' strictSublevel d G
  have hB : IsOpen B := (isOpen_strictSublevel d G).preimage e.continuous
  have hZB : Z ⊆ B := by
    intro x hx
    apply zeroSet_subset_strictSublevel d G
    exact image_independence_polyhedron d G ▸ Set.mem_image_of_mem e hx
  obtain ⟨m, hm⟩ := K.exists_iteratedOpenSimplicialNeighborhood_subset P
    (Set.toFinite K.faces) hB hZB
  let N := K.iteratedOpenSimplicialNeighborhood P m
  let U := e '' N
  have hZN : Z ⊆ N := K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P m
  have heZ : e '' Z = zeroSet d G := image_independence_polyhedron d G
  have hZU : zeroSet d G ⊆ U := by
    rw [← heZ]
    exact Set.image_mono hZN
  refine ⟨U, hZU, e.isOpenMap _ (K.isOpen_iteratedOpenSimplicialNeighborhood P m), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hm hx
  · exact e.exists_deformation_of_image_eq hZN hZU rfl heZ
      (K.exists_deformation_iteratedOpenSimplicialNeighborhood P m)

/-- A sufficiently small closed polynomial sublevel is inside any open
neighbourhood of the zero set, with the quantitative margin used in §5.1. -/
theorem exists_small_sublevel_subset (d : ℕ) (G : Finset (Finset V))
    {U : Set (Simplex V)} (hU : IsOpen U) (hZU : zeroSet d G ⊆ U)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ γ : ℝ, 0 < γ ∧ γ < κ / 3 ∧
      {μ : Simplex V | weightPolynomial (d + 1) G (μ.weights : V → ℝ) ≤ 4 * γ} ⊆ U := by
  let P : Simplex V → ℝ := fun μ => weightPolynomial (d + 1) G (μ.weights : V → ℝ)
  have hP : Continuous P := (WeightPolynomial.contDiff (d + 1) G 0).continuous.comp
    coordinateHomeomorph.continuous.subtype_val
  by_cases hC : (Uᶜ).Nonempty
  · obtain ⟨μ₀, hμ₀, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hC hP.continuousOn
    have hp : 0 < P μ₀ := by
      have hnonneg := WeightPolynomial.nonneg (d + 1) G (coordinate_nonneg μ₀)
      have hne : P μ₀ ≠ 0 := by
        intro hz
        exact hμ₀ (hZU hz)
      exact lt_of_le_of_ne hnonneg hne.symm
    let γ := min (κ / 6) (P μ₀ / 8)
    have hγ : 0 < γ := lt_min (by linarith) (by linarith)
    refine ⟨γ, hγ, (min_le_left _ _).trans_lt (by linarith), ?_⟩
    intro μ hμ
    by_contra hμU
    have hlow := hmin hμU
    change P μ₀ ≤ P μ at hlow
    have hsmall : γ ≤ P μ₀ / 8 := min_le_right _ _
    change P μ ≤ 4 * γ at hμ
    nlinarith
  · refine ⟨κ / 6, by linarith, by linarith, ?_⟩
    intro μ _
    by_contra hμ
    exact hC ⟨μ, hμ⟩

end SharpTopologicalOverlap.Sublevel
