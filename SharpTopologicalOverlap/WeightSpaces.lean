module

public import SharpTopologicalOverlap.Deletion
public import SharpTopologicalOverlap.Polynomial
public import SharpTopologicalOverlap.Polynomial.Threshold
public import SharpTopologicalOverlap.Singular.Deformation

/-! # The nested weight spaces

All carriers live in the original probability simplex. Reindexing to the
remaining vertex subtype is reserved for the proof of relative filling.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open _root_.SharpTopologicalOverlap.Simplicial WeightPolynomial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}

namespace IntersectionData

variable (I : IntersectionData T f)

/-- The total exceptional mass at a target cell. -/
def exceptionalMass {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n)) : ℝ :=
  ∑ i ∈ I.exceptionalSet τ, μ.weights i

/-- The open carrier `B_τ` in the fixed ambient simplex. -/
def weightSpace {p : ℕ} (τ : Cell T p) : Set (Simplex (Fin n)) :=
  {μ | weightPolynomial (d + 1) (upwardSupport I.cochain τ) (μ.weights : Fin n → ℝ) <
    overlapThreshold d * (1 - I.exceptionalMass τ μ) ^ (d + 1)}

/-- The independence precomplex includes only the remaining vertices. -/
def independenceSubcomplex {p : ℕ} (τ : Cell T p) : PreAbstractSimplicialComplex (Fin n) where
  faces := {s | s.Nonempty ∧ s ⊆ I.remainingVertices τ ∧
    ∀ e ∈ I.restrictedFamily τ, ¬ e ⊆ s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hts.trans hs.2.1, fun e he het => hs.2.2 e he (het.trans hts)⟩

/-- The smaller carrier `J_τ` as the realization of its ambient subcomplex. -/
def independentSpace {p : ℕ} (τ : Cell T p) : Set (Simplex (Fin n)) :=
  realizedComplex (I.independenceSubcomplex τ)

@[simp] theorem mem_independenceSubcomplex {p : ℕ} (τ : Cell T p) (s : Finset (Fin n)) :
    s ∈ I.independenceSubcomplex τ ↔ s.Nonempty ∧ s ⊆ I.remainingVertices τ ∧
      ∀ e ∈ I.restrictedFamily τ, ¬ e ⊆ s := Iff.rfl

theorem coordinate_zero_of_support_subset {S : Finset (Fin n)} {μ : Simplex (Fin n)}
    (hμ : support μ ⊆ S) {i : Fin n} (hi : i ∉ S) : μ.weights i = 0 := by
  by_contra hne
  exact hi (hμ (mem_support.mpr hne))

theorem polynomial_restrict_remaining {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n))
    (hμ : support μ ⊆ I.remainingVertices τ) :
    weightPolynomial (d + 1) (I.restrictedFamily τ) (μ.weights : Fin n → ℝ) =
      weightPolynomial (d + 1) (upwardSupport I.cochain τ) (μ.weights : Fin n → ℝ) := by
  exact restrict_eq (d + 1) (I.remainingVertices τ) (upwardSupport I.cochain τ)
    (fun i hi => coordinate_zero_of_support_subset hμ hi)

theorem mem_independentSpace_iff {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n)) :
    μ ∈ I.independentSpace τ ↔ support μ ⊆ I.remainingVertices τ ∧
      weightPolynomial (d + 1) (I.restrictedFamily τ) (μ.weights : Fin n → ℝ) = 0 := by
  rw [independentSpace, mem_realizedComplex, mem_independenceSubcomplex,
    and_iff_right (support_nonempty μ), eq_zero_iff_support,
    homogeneousPart_eq_self (I.restrictedFamily_uniform τ)]

theorem exceptionalMass_nonneg {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n)) :
    0 ≤ I.exceptionalMass τ μ := Finset.sum_nonneg (fun i _ => coordinate_nonneg μ i)

theorem exceptionalMass_le_one {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n)) :
    I.exceptionalMass τ μ ≤ 1 := by
  calc
    _ ≤ ∑ i, μ.weights i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => coordinate_nonneg μ i)
    _ = 1 := sum_coordinates μ

theorem exceptionalMass_mono {p r : ℕ} {σ : Cell T p} {τ : Cell T r}
    (hστ : σ.1.1 ⊆ τ.1.1) (μ : Simplex (Fin n)) :
    I.exceptionalMass σ μ ≤ I.exceptionalMass τ μ :=
  Finset.sum_le_sum_of_subset_of_nonneg (I.exceptionalSet_mono hστ)
    (fun i _ _ => coordinate_nonneg μ i)

theorem exceptionalMass_eq_zero_of_remaining {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n))
    (hμ : support μ ⊆ I.remainingVertices τ) : I.exceptionalMass τ μ = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply coordinate_zero_of_support_subset hμ
  exact fun hrem => ((I.mem_remainingVertices τ i).mp hrem) hi

theorem independentSpace_subset_weightSpace {p : ℕ} (τ : Cell T p) :
    I.independentSpace τ ⊆ I.weightSpace τ := by
  intro μ hμ
  obtain ⟨hrem, hzero⟩ := (I.mem_independentSpace_iff τ μ).mp hμ
  change _ < _
  rw [← I.polynomial_restrict_remaining τ μ hrem, hzero,
    I.exceptionalMass_eq_zero_of_remaining τ μ hrem]
  simpa using overlapThreshold_pos d

theorem weightSpace_mono {p r : ℕ} {σ : Cell T p} {τ : Cell T r}
    (hστ : σ.1.1 ⊆ τ.1.1) : I.weightSpace τ ⊆ I.weightSpace σ := by
  intro μ hμ
  change _ < _ at hμ ⊢
  calc
    _ ≤ weightPolynomial (d + 1) (upwardSupport I.cochain τ) (μ.weights : Fin n → ℝ) :=
      mono_family (d + 1) (upwardSupport_mono I.cochain hστ) (coordinate_nonneg μ)
    _ < overlapThreshold d * (1 - I.exceptionalMass τ μ) ^ (d + 1) := hμ
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr (I.exceptionalMass_le_one τ μ))
        (sub_le_sub_left (I.exceptionalMass_mono hστ μ) 1) (d + 1))
      (le_of_lt (overlapThreshold_pos d))

theorem independentSpace_mono {p r : ℕ} {σ : Cell T p} {τ : Cell T r}
    (hστ : σ.1.1 ⊆ τ.1.1) : I.independentSpace τ ⊆ I.independentSpace σ := by
  intro μ hμ
  obtain ⟨hrem, hz⟩ := (I.mem_independentSpace_iff τ μ).mp hμ
  have hrem' := hrem.trans (I.remainingVertices_antitone hστ)
  apply (I.mem_independentSpace_iff σ μ).mpr
  refine ⟨hrem', le_antisymm ?_ (nonneg _ _ (coordinate_nonneg μ))⟩
  rw [I.polynomial_restrict_remaining σ μ hrem',
    I.polynomial_restrict_remaining τ μ hrem] at *
  exact (mono_family (d + 1) (upwardSupport_mono I.cochain hστ) (coordinate_nonneg μ)).trans_eq hz

theorem independenceSubcomplex_mono {p r : ℕ} {σ : Cell T p} {τ : Cell T r}
    (hστ : σ.1.1 ⊆ τ.1.1) : I.independenceSubcomplex τ ≤ I.independenceSubcomplex σ := by
  intro s hs
  obtain ⟨hne, hrem, hfree⟩ := (I.mem_independenceSubcomplex τ s).mp hs
  apply (I.mem_independenceSubcomplex σ s).mpr
  refine ⟨hne, hrem.trans (I.remainingVertices_antitone hστ), ?_⟩
  intro e he hes
  have heP := I.restrictedFamily_subset_upwardSupport σ he
  have heτ := upwardSupport_mono I.cochain hστ heP
  exact hfree e ((I.mem_restrictedFamily τ e).mpr ⟨heτ, hes.trans hrem⟩) hes

/-- The intersection cochain vanishes on its independence carrier, in all
complementary degrees. This is the annihilation used after applying `ρ`. -/
theorem cochain_vanishes_independence {p q : ℕ} (τ : Cell T p) (h : p + q = d)
    (hd : 0 < d) : VanishesOn (I.independenceSubcomplex τ) (I.cochain p q h τ) := by
  intro s hs
  obtain ⟨_, hrem, hfree⟩ := (I.mem_independenceSubcomplex τ s.1.1).mp hs
  by_cases hp : 0 < p
  · exact I.cochain_eq_zero_on_remaining τ τ h hp (Finset.Subset.refl _) s hrem
  · have hp0 : p = 0 := by omega
    subst p
    have hqd : q = d := by omega
    subst q
    by_contra hne
    have hv : I.cochain 0 d (Nat.zero_add d)
        (AbstractSimplicialComplex.RealizationCell.vertex T (τ.vertexEmbedding 0)) s ≠ 0 := by
      simpa only [← τ.eq_vertex] using hne
    have hmem := (I.mem_restrictedFamily_iff_vertex τ hd (τ.vertexEmbedding 0)
      (τ.vertexEmbedding_mem 0) s hrem).mpr hv
    exact hfree s.1.1 hmem (Finset.Subset.refl _)

theorem evaluation_eq_zero_on_independence {p q : ℕ} (τ : Cell T p) (h : p + q = d)
    (hd : 0 < d) {c : Chain (⊤ : AbstractSimplicialComplex (Fin n)) q}
    (hc : CarriedBy (I.independenceSubcomplex τ) c) : evaluation (I.cochain p q h τ) c = 0 :=
  evaluation_eq_zero_of_carriedBy (I.cochain_vanishes_independence τ h hd) hc

theorem exceptionalMass_uniform [NeZero n] {p : ℕ} (τ : Cell T p) :
    I.exceptionalMass τ (uniform : Simplex (Fin n)) = (I.exceptionalSet τ).card / (n : ℝ) := by
  simp [exceptionalMass, coordinate_uniform, nsmul_eq_mul, div_eq_mul_inv]

theorem uniform_mem_weightSpace [NeZero n] {p : ℕ} (τ : Cell T p)
    (hn : deletionBound d < n)
    (hsmall : (overlap f : ℝ) < (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1)) :
    (uniform : Simplex (Fin n)) ∈ I.weightSpace τ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hkpos : (0 : ℝ) < (d + 1 : ℝ) := by positivity
  have hfac : (0 : ℝ) < (d + 1).factorial := Nat.cast_pos.mpr (d + 1).factorial_pos
  have hnPow := pow_pos hnpos (d + 1)
  have hcard : ((upwardSupport I.cochain τ).card : ℝ) ≤ overlap f :=
    Nat.cast_le.mpr (I.upwardSupport_card_le_overlap τ)
  have hS : ((I.exceptionalSet τ).card : ℝ) ≤ deletionBound d :=
    Nat.cast_le.mpr (I.exceptionalSet_card_le τ)
  have hCn : (deletionBound d : ℝ) < n := Nat.cast_lt.mpr hn
  change _ < _
  rw [uniform_value, homogeneousPart_eq_self (upwardSupport_uniform I.cochain τ),
    Fintype.card_fin, I.exceptionalMass_uniform τ]
  calc
    _ ≤ ((d + 1).factorial : ℝ) * (overlap f : ℝ) / (n : ℝ) ^ (d + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hfac.le) hnPow.le
    _ < ((d + 1).factorial : ℝ) *
        ((((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1)) / (n : ℝ) ^ (d + 1) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsmall hfac) hnPow
    _ = overlapThreshold d * (((n : ℝ) - deletionBound d) / n) ^ (d + 1) := by
      rw [overlapThreshold, div_pow, div_pow]
      field_simp
    _ ≤ overlapThreshold d * (1 - ((I.exceptionalSet τ).card : ℝ) / n) ^ (d + 1) := by
      apply mul_le_mul_of_nonneg_left _ (overlapThreshold_pos d).le
      apply pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hCn.le) hnpos.le)
      apply (div_le_iff₀ hnpos).mpr
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hnpos.ne']
      linarith

end IntersectionData

end SharpTopologicalOverlap
