module

public import SharpTopologicalOverlap.WeightSpaces

/-! # Deleting exceptional mass by a homotopy

The proof uses coordinate monotonicity and homogeneity directly: along the
homotopy every coordinate is bounded by the common rescaling factor times
its original coordinate. This includes zero exceptional mass.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.WeightDeletion

open WeightPolynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

def mass (S : Finset V) (μ : Simplex V) : ℝ := ∑ i ∈ S, μ.weights i

theorem mass_nonneg (S : Finset V) (μ : Simplex V) : 0 ≤ mass S μ :=
  Finset.sum_nonneg fun i _ => coordinate_nonneg μ i

theorem mass_le_one (S : Finset V) (μ : Simplex V) : mass S μ ≤ 1 := by
  calc
    _ ≤ ∑ i, μ.weights i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => coordinate_nonneg μ i)
    _ = 1 := sum_coordinates μ

theorem mass_compl (S : Finset V) (μ : Simplex V) : mass Sᶜ μ = 1 - mass S μ := by
  have h := Finset.sum_add_sum_compl S (fun i => μ.weights i)
  rw [sum_coordinates] at h
  change mass S μ + mass Sᶜ μ = 1 at h
  linarith

/-- Normalize the coordinates outside `S`, retaining the ambient simplex. -/
def normalize (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) : Simplex V :=
  coordinateHomeomorph.symm ⟨fun i => if i ∈ Sᶜ then μ.weights i / (1 - mass S μ) else 0,
    (fun i => by
      change 0 ≤ if i ∈ Sᶜ then μ.weights i / (1 - mass S μ) else 0
      split_ifs
      · exact div_nonneg (coordinate_nonneg μ i) (sub_nonneg.mpr ht.le)
      · exact le_rfl), by
      simp only [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_div]
      change mass Sᶜ μ / (1 - mass S μ) = 1
      rw [mass_compl, div_self (by linarith)]⟩

@[simp] theorem normalize_coordinate (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) (i : V) :
    (normalize S μ ht).weights i = if i ∈ S then 0 else μ.weights i / (1 - mass S μ) := by
  change (coordinateHomeomorph (normalize S μ ht)).1 i = _
  simp only [normalize, Homeomorph.apply_symm_apply, Finset.mem_compl, ite_not]

/-- Affinely interpolate to the normalized remaining coordinates. -/
def homotopyPoint (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) (r : unitInterval) : Simplex V :=
  Convexity.convexCombPair (1 - (r : ℝ)) (r : ℝ) (by linarith [r.property.2])
    r.property.1 (by ring) μ (normalize S μ ht)

theorem homotopyPoint_coordinate (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1)
    (r : unitInterval) (i : V) :
    (homotopyPoint S μ ht r).weights i =
      if i ∈ S then (1 - (r : ℝ)) * μ.weights i else
        ((1 - (1 - (r : ℝ)) * mass S μ) / (1 - mass S μ)) * μ.weights i := by
  rw [homotopyPoint, Convexity.StdSimplex.weights_convexCombPair]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, normalize_coordinate]
  split_ifs
  · ring
  · field_simp
    ring

theorem mass_homotopyPoint (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1)
    (r : unitInterval) : mass S (homotopyPoint S μ ht r) = (1 - (r : ℝ)) * mass S μ := by
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [homotopyPoint_coordinate, ite_eq_left hi]

theorem scale_pos (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) (r : unitInterval) :
    0 < (1 - (1 - (r : ℝ)) * mass S μ) / (1 - mass S μ) := by
  have hs : (1 - (r : ℝ)) * mass S μ ≤ mass S μ := by
    exact mul_le_of_le_one_left (mass_nonneg S μ) (by linarith [r.property.1])
  exact div_pos (by linarith) (by linarith)

theorem coordinate_le_scale (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1)
    (r : unitInterval) (i : V) :
    (homotopyPoint S μ ht r).weights i ≤
      ((1 - (1 - (r : ℝ)) * mass S μ) / (1 - mass S μ)) * μ.weights i := by
  rw [homotopyPoint_coordinate]
  split_ifs
  · apply mul_le_mul_of_nonneg_right _ (coordinate_nonneg μ i)
    apply (le_div_iff₀ (sub_pos.mpr ht)).mpr
    nlinarith [r.property.1]
  · exact le_rfl

/-- Homogeneity and coordinate monotonicity keep the deletion homotopy in
the same strict polynomial carrier. -/
theorem polynomial_homotopyPoint_lt (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1)
    (r : unitInterval) (k : ℕ) (G : Finset (Finset V)) (θ : ℝ)
    (hμ : weightPolynomial k G (μ.weights : V → ℝ) < θ * (1 - mass S μ) ^ k) :
    weightPolynomial k G ((homotopyPoint S μ ht r).weights : V → ℝ) <
      θ * (1 - mass S (homotopyPoint S μ ht r)) ^ k := by
  let a := (1 - (1 - (r : ℝ)) * mass S μ) / (1 - mass S μ)
  have ha : 0 < a := scale_pos S μ ht r
  have hprod : a * (1 - mass S μ) = 1 - (1 - (r : ℝ)) * mass S μ :=
    div_mul_cancel₀ _ (sub_pos.mpr ht).ne'
  calc
    _ ≤ weightPolynomial k G (a • (μ.weights : V → ℝ)) :=
      mono_coordinates k G (coordinate_nonneg _) (coordinate_le_scale S μ ht r)
    _ = a ^ k * weightPolynomial k G (μ.weights : V → ℝ) := homogeneous k G a _
    _ < a ^ k * (θ * (1 - mass S μ) ^ k) := mul_lt_mul_of_pos_left hμ (pow_pos ha k)
    _ = θ * (1 - mass S (homotopyPoint S μ ht r)) ^ k := by
      rw [mass_homotopyPoint, ← hprod, mul_pow]
      ring

theorem homotopyPoint_zero (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) :
    homotopyPoint S μ ht 0 = μ := by
  simp [homotopyPoint, Convexity.convexCombPair_one]

theorem homotopyPoint_one (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) :
    homotopyPoint S μ ht 1 = normalize S μ ht := by
  simp [homotopyPoint, Convexity.convexCombPair_zero]

theorem support_homotopyPoint_one (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1) :
    support (homotopyPoint S μ ht 1) ⊆ Sᶜ := by
  intro i hi
  rw [Finset.mem_compl]
  intro hiS
  have hz : (homotopyPoint S μ ht 1).weights i = 0 := by
    rw [homotopyPoint_coordinate, ite_eq_left hiS]
    simp
  exact (mem_support.mp hi) hz

theorem continuous_mass (S : Finset V) : Continuous (mass S) := by
  unfold mass
  fun_prop

abbrev Domain (S : Finset V) := {μ : Simplex V // mass S μ < 1}

theorem continuous_normalize (S : Finset V) :
    Continuous (fun μ : Domain S => normalize S μ.1 μ.2) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous (fun μ : Domain S => (normalize S μ.1 μ.2).weights i)
  simp_rw [normalize_coordinate]
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi]
    exact continuous_const
  · simp only [ite_eq_right hi]
    exact ((continuous_coordinate i).comp continuous_subtype_val).div
      (continuous_const.sub ((continuous_mass S).comp continuous_subtype_val))
      (fun μ => (sub_pos.mpr μ.2).ne')

theorem continuous_homotopyPoint (S : Finset V) :
    Continuous (fun p : Domain S × unitInterval => homotopyPoint S p.1.1 p.1.2 p.2) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous (fun p : Domain S × unitInterval =>
    (homotopyPoint S p.1.1 p.1.2 p.2).weights i)
  simp only [homotopyPoint, Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_coordinate i).comp (continuous_subtype_val.comp continuous_fst))).add
    ((continuous_subtype_val.comp continuous_snd).mul
      ((continuous_coordinate i).comp ((continuous_normalize S).comp continuous_fst)))

theorem mass_eq_zero_of_support_compl (S : Finset V) (μ : Simplex V)
    (hμ : support μ ⊆ Sᶜ) : mass S μ = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  exact (Finset.mem_compl.mp (hμ (mem_support.mpr hne))) hi

theorem homotopyPoint_fixed (S : Finset V) (μ : Simplex V) (ht : mass S μ < 1)
    (hμ : support μ ⊆ Sᶜ) (r : unitInterval) : homotopyPoint S μ ht r = μ := by
  apply (coordinateHomeomorph (V := V)).injective
  apply Subtype.ext
  funext i
  change (homotopyPoint S μ ht r).weights i = μ.weights i
  rw [homotopyPoint_coordinate, mass_eq_zero_of_support_compl S μ hμ]
  by_cases hi : i ∈ S
  · have hz : μ.weights i = 0 := by
      by_contra hne
      exact (Finset.mem_compl.mp (hμ (mem_support.mpr hne))) hi
    simp [hi, hz]
  · simp [hi]

end SharpTopologicalOverlap.WeightDeletion
