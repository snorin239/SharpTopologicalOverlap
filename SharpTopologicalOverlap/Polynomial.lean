module

public import SharpTopologicalOverlap.Simplex
public import SharpTopologicalOverlap.Simplicial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Weight polynomials

The degree parameter is the number of vertices of an edge: the manuscript uses
`k = d + 1`. The definition filters the family by cardinality, as in (2.1).
-/

@[expose] public noncomputable section

open scoped BigOperators ContDiff

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace SharpTopologicalOverlap.WeightPolynomial

variable {V : Type*} [DecidableEq V]

/-- The square-free monomial associated with a finite vertex set. -/
def monomial (e : Finset V) (x : V → ℝ) : ℝ := ∏ i ∈ e, x i

/-- Retain exactly the edges of the prescribed cardinality. -/
def homogeneousPart (k : ℕ) (G : Finset (Finset V)) : Finset (Finset V) :=
  G.filter fun e => e.card = k

/-- The polynomial of a family, normalized by the factorial of its degree. -/
def weightPolynomial (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) : ℝ :=
  (k.factorial : ℝ) * ∑ e ∈ homogeneousPart k G, monomial e x

omit [DecidableEq V] in
@[simp] theorem mem_homogeneousPart {k : ℕ} {G : Finset (Finset V)} {e : Finset V} :
    e ∈ homogeneousPart k G ↔ e ∈ G ∧ e.card = k := by
  simp [homogeneousPart]

omit [DecidableEq V] in
theorem homogeneousPart_eq_self {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) : homogeneousPart k G = G := by
  exact Finset.filter_eq_self.mpr hG

omit [DecidableEq V] in
theorem weightPolynomial_of_uniform {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (x : V → ℝ) :
    weightPolynomial k G x = (k.factorial : ℝ) * ∑ e ∈ G, monomial e x := by
  rw [weightPolynomial, homogeneousPart_eq_self hG]

omit [DecidableEq V] in
@[simp] theorem weightPolynomial_empty (k : ℕ) (x : V → ℝ) :
    weightPolynomial k (∅ : Finset (Finset V)) x = 0 := by
  simp [weightPolynomial, homogeneousPart]

omit [DecidableEq V] in
theorem monomial_nonneg {e : Finset V} {x : V → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ monomial e x := Finset.prod_nonneg fun i _ => hx i

omit [DecidableEq V] in
theorem monomial_mono {e : Finset V} {x y : V → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) : monomial e x ≤ monomial e y := by
  exact Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => hxy i)

omit [DecidableEq V] in
theorem nonneg (k : ℕ) (G : Finset (Finset V)) {x : V → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ weightPolynomial k G x := by
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => monomial_nonneg hx)

omit [DecidableEq V] in
theorem mono_coordinates (k : ℕ) (G : Finset (Finset V)) {x y : V → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    weightPolynomial k G x ≤ weightPolynomial k G y := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun _ _ => monomial_mono hx hxy

omit [DecidableEq V] in
theorem mono_family (k : ℕ) {G H : Finset (Finset V)} (hGH : G ⊆ H)
    {x : V → ℝ} (hx : ∀ i, 0 ≤ x i) :
    weightPolynomial k G x ≤ weightPolynomial k H x := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hGH)
  exact fun _ _ _ => monomial_nonneg hx

omit [DecidableEq V] in
theorem monomial_smul (e : Finset V) (a : ℝ) (x : V → ℝ) :
    monomial e (a • x) = a ^ e.card * monomial e x := by
  simp [monomial, Finset.prod_mul_distrib]

omit [DecidableEq V] in
theorem homogeneous (k : ℕ) (G : Finset (Finset V)) (a : ℝ) (x : V → ℝ) :
    weightPolynomial k G (a • x) = a ^ k * weightPolynomial k G x := by
  unfold weightPolynomial
  have h : (∑ e ∈ homogeneousPart k G, monomial e (a • x)) =
      a ^ k * ∑ e ∈ homogeneousPart k G, monomial e x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [monomial_smul, (mem_homogeneousPart.mp he).2]
  rw [h]
  ring

omit [DecidableEq V] in
theorem monomial_pos_iff {e : Finset V} {x : V → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 < monomial e x ↔ ∀ i ∈ e, 0 < x i := by
  constructor
  · intro h i hi
    exact (hx i).lt_of_ne' (by intro hzero; exact ne_of_gt h (Finset.prod_eq_zero hi hzero))
  · exact fun h => Finset.prod_pos h

omit [DecidableEq V] in
theorem eq_zero_iff (k : ℕ) (G : Finset (Finset V)) {x : V → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    weightPolynomial k G x = 0 ↔
      ∀ e ∈ homogeneousPart k G, ∃ i ∈ e, x i = 0 := by
  rw [weightPolynomial, mul_eq_zero, or_iff_right (by exact_mod_cast k.factorial_ne_zero),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => monomial_nonneg hx)]
  simp [monomial, Finset.prod_eq_zero_iff]

theorem eq_zero_iff_support (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    weightPolynomial k G (μ.weights : V → ℝ) = 0 ↔
      ∀ e ∈ homogeneousPart k G, ¬ e ⊆ support μ := by
  rw [eq_zero_iff k G (coordinate_nonneg μ)]
  simp only [Finset.not_subset, mem_support, not_not]

/-- The independence complex can omit vertices, notably for degree one. -/
def independenceComplex (k : ℕ) (G : Finset (Finset V)) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∀ e ∈ homogeneousPart k G, ¬ e ⊆ s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun e he het => hs.2 e he (het.trans hts)⟩

omit [DecidableEq V] in
@[simp] theorem mem_independenceComplex (k : ℕ) (G : Finset (Finset V)) (s : Finset V) :
    s ∈ independenceComplex k G ↔
      s.Nonempty ∧ ∀ e ∈ homogeneousPart k G, ¬ e ⊆ s := Iff.rfl

theorem realized_independenceComplex (k : ℕ) (G : Finset (Finset V)) :
    realizedComplex (independenceComplex k G) =
      {μ : Simplex V | weightPolynomial k G (μ.weights : V → ℝ) = 0} := by
  ext μ
  simp only [mem_realizedComplex, mem_independenceComplex, Set.mem_ofPred_eq,
    eq_zero_iff_support, support_nonempty μ, true_and]

omit [DecidableEq V] in
theorem uniform_value [Fintype V] [Nonempty V] (k : ℕ) (G : Finset (Finset V)) :
    weightPolynomial k G ((uniform : Simplex V).weights : V → ℝ) =
      (k.factorial : ℝ) * (homogeneousPart k G).card / (Fintype.card V : ℝ) ^ k := by
  unfold weightPolynomial
  have h : ∀ e ∈ homogeneousPart k G,
      monomial e ((uniform : Simplex V).weights : V → ℝ) = (Fintype.card V : ℝ)⁻¹ ^ k := by
    intro e he
    simp [monomial, coordinate_uniform, (mem_homogeneousPart.mp he).2]
  simp_rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  simp [div_eq_mul_inv, inv_pow, mul_assoc]

/-- Restrict a family to the prescribed vertex set. -/
def restrictFamily (S : Finset V) (G : Finset (Finset V)) : Finset (Finset V) :=
  G.filter (· ⊆ S)

theorem homogeneousPart_restrict (k : ℕ) (S : Finset V) (G : Finset (Finset V)) :
    homogeneousPart k (restrictFamily S G) = (homogeneousPart k G).filter (· ⊆ S) := by
  ext e
  simp [homogeneousPart, restrictFamily, and_comm, and_left_comm]

omit [DecidableEq V] in
theorem monomial_eq_zero_of_not_subset {S e : Finset V} {x : V → ℝ}
    (hx : ∀ i ∉ S, x i = 0) (he : ¬ e ⊆ S) : monomial e x = 0 := by
  obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp he
  exact Finset.prod_eq_zero hi (hx i hiS)

theorem restrict_eq (k : ℕ) (S : Finset V) (G : Finset (Finset V)) {x : V → ℝ}
    (hx : ∀ i ∉ S, x i = 0) :
    weightPolynomial k (restrictFamily S G) x = weightPolynomial k G x := by
  rw [weightPolynomial, weightPolynomial, homogeneousPart_restrict, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ⊆ S
  · simp [he]
  · simp [he, monomial_eq_zero_of_not_subset hx he]

section Calculus

variable [Fintype V]

omit [DecidableEq V] in
theorem contDiff_monomial (e : Finset V) (n : ℕ∞ω) :
    ContDiff ℝ n (monomial e : (V → ℝ) → ℝ) := by
  exact contDiff_prod fun i _ => contDiff_apply ℝ (fun _ : V => ℝ) i

omit [DecidableEq V] in
theorem contDiff (k : ℕ) (G : Finset (Finset V)) (n : ℕ∞ω) :
    ContDiff ℝ n (weightPolynomial k G : (V → ℝ) → ℝ) := by
  exact contDiff_const.mul (ContDiff.sum fun e _ => contDiff_monomial e n)

/-- The differential of one square-free monomial. -/
def monomialDifferential (e : Finset V) (x : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ e, monomial (e.erase i) x • ContinuousLinearMap.proj i

theorem hasFDerivAt_monomial (e : Finset V) (x : V → ℝ) :
    HasFDerivAt (monomial e) (monomialDifferential e x) x := by
  exact HasFDerivAt.finsetProd fun i _ => hasFDerivAt_apply i x

/-- The differential of the weight polynomial, written without coordinate choices. -/
def differential (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ℝ :=
  (k.factorial : ℝ) • ∑ e ∈ homogeneousPart k G, monomialDifferential e x

theorem hasFDerivAt (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    HasFDerivAt (weightPolynomial k G) (differential k G x) x := by
  change HasFDerivAt (fun y => (k.factorial : ℝ) * ∑ e ∈ homogeneousPart k G, monomial e y)
    ((k.factorial : ℝ) • ∑ e ∈ homogeneousPart k G, monomialDifferential e x) x
  simpa only [Finset.sum_apply] using
    (HasFDerivAt.sum (fun e (_ : e ∈ homogeneousPart k G) => hasFDerivAt_monomial e x)).const_mul
      (k.factorial : ℝ)

theorem fderiv_eq (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    fderiv ℝ (weightPolynomial k G) x = differential k G x :=
  (hasFDerivAt k G x).fderiv

/-- The coordinate partial derivative, expressed as a finite monomial sum. -/
def coordinatePartial (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) : ℝ :=
  (k.factorial : ℝ) * ∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), monomial (e.erase i) x

theorem monomialDifferential_single (e : Finset V) (i : V) (x : V → ℝ) :
    monomialDifferential e x (Pi.single i 1) =
      if i ∈ e then monomial (e.erase i) x else 0 := by
  simp [monomialDifferential, Pi.single_apply, eq_comm]

theorem differential_single (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) :
    differential k G x (Pi.single i 1) = coordinatePartial k G i x := by
  simp [differential, coordinatePartial, monomialDifferential_single, Finset.sum_filter]

omit [Fintype V] in
theorem partial_nonneg (k : ℕ) (G : Finset (Finset V)) (i : V) {x : V → ℝ}
    (hx : ∀ j, 0 ≤ x j) : 0 ≤ coordinatePartial k G i x := by
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => monomial_nonneg hx)

theorem monomial_euler (e : Finset V) (x : V → ℝ) :
    monomialDifferential e x x = (e.card : ℝ) * monomial e x := by
  simp only [monomialDifferential, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    (∑ i ∈ e, monomial (e.erase i) x * x i) = ∑ _i ∈ e, monomial e x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.prod_erase_mul e x hi
    _ = _ := by simp [nsmul_eq_mul]

theorem euler (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    differential k G x x = (k : ℝ) * weightPolynomial k G x := by
  simp only [differential, smul_apply, sum_apply,
    smul_eq_mul, monomial_euler]
  have h : (∑ e ∈ homogeneousPart k G, (e.card : ℝ) * monomial e x) =
      (k : ℝ) * ∑ e ∈ homogeneousPart k G, monomial e x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [(mem_homogeneousPart.mp he).2]
  rw [h, weightPolynomial]
  ring

theorem differential_apply (k : ℕ) (G : Finset (Finset V)) (x y : V → ℝ) :
    differential k G x y = ∑ i, y i * coordinatePartial k G i x := by
  have hy : (∑ i, Pi.single i (y i)) = y := by ext j; simp
  conv_lhs => rw [← hy]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (y i) = y i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [h, map_smul, differential_single, smul_eq_mul]

/-- The link family occurring in a first partial derivative. -/
def link (k : ℕ) (G : Finset (Finset V)) (i : V) : Finset (Finset V) :=
  ((homogeneousPart (k + 1) G).filter (i ∈ ·)).image (fun e => e.erase i)

omit [Fintype V] in
theorem link_uniform (k : ℕ) (G : Finset (Finset V)) (i : V) :
    Simplicial.IsUniform k (link k G i) := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hs
  rw [Finset.card_erase_of_mem hi, (mem_homogeneousPart.mp hs).2]
  omega

omit [Fintype V] in
theorem erase_injective_on_containing (s t : Finset V) (i : V)
    (hs : i ∈ s) (ht : i ∈ t) (h : s.erase i = t.erase i) : s = t := by
  have h' := congrArg (insert i) h
  simpa [Finset.insert_erase hs, Finset.insert_erase ht] using h'

omit [Fintype V] in
theorem partial_eq_link (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) :
    coordinatePartial (k + 1) G i x = (k + 1 : ℝ) * weightPolynomial k (link k G i) x := by
  rw [weightPolynomial_of_uniform (link_uniform k G i)]
  unfold link
  rw [Finset.sum_image]
  · simp only [coordinatePartial, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  · intro s hs t ht hst
    exact erase_injective_on_containing s t i (Finset.mem_filter.mp hs).2
      (Finset.mem_filter.mp ht).2 hst

theorem weightPolynomial_succ (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    weightPolynomial (k + 1) G x = ∑ i, x i * weightPolynomial k (link k G i) x := by
  have h := euler (k + 1) G x
  rw [differential_apply] at h
  simp_rw [partial_eq_link] at h
  have hr : (∑ i, x i * ((k + 1 : ℝ) * weightPolynomial k (link k G i) x)) =
      (k + 1 : ℝ) * ∑ i, x i * weightPolynomial k (link k G i) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hr] at h
  norm_cast at h
  exact (mul_left_cancel₀ (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0) h).symm

/-- Counting ordered distinct samples, proved recursively through link families. -/
theorem le_sum_pow (k : ℕ) (G : Finset (Finset V)) {x : V → ℝ}
    (hx : ∀ i, 0 ≤ x i) : weightPolynomial k G x ≤ (∑ i, x i) ^ k := by
  induction k generalizing G with
  | zero =>
      have h : homogeneousPart 0 G ⊆ {∅} := by
        intro e he
        simp [Finset.card_eq_zero.mp (mem_homogeneousPart.mp he).2]
      have hsum : (∑ e ∈ homogeneousPart 0 G, monomial e x) ≤
          ∑ e ∈ ({∅} : Finset (Finset V)), monomial e x := by
        exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => monomial_nonneg hx)
      simpa [weightPolynomial, monomial] using hsum
  | succ k ih =>
      rw [weightPolynomial_succ]
      calc
        (∑ i, x i * weightPolynomial k (link k G i) x) ≤
            ∑ i, x i * (∑ j, x j) ^ k := by
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih _) (hx i)
        _ = (∑ i, x i) ^ (k + 1) := by rw [← Finset.sum_mul, pow_succ]; ring

theorem simplex_le_one (k : ℕ) (G : Finset (Finset V)) (μ : Simplex V) :
    weightPolynomial k G (μ.weights : V → ℝ) ≤ 1 := by
  simpa [sum_coordinates] using le_sum_pow k G (coordinate_nonneg μ)

theorem simplex_partial_le (k : ℕ) (G : Finset (Finset V)) (i : V) (μ : Simplex V) :
    coordinatePartial (k + 1) G i (μ.weights : V → ℝ) ≤ k + 1 := by
  rw [partial_eq_link]
  exact (mul_le_mul_of_nonneg_left (simplex_le_one k (link k G i) μ) (by positivity)).trans_eq
    (mul_one _)

/-- The differential of a coordinate partial. -/
def partialDifferential (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ℝ :=
  (k.factorial : ℝ) • ∑ e ∈ (homogeneousPart k G).filter (i ∈ ·),
    monomialDifferential (e.erase i) x

theorem hasFDerivAt_coordinatePartial (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) :
    HasFDerivAt (coordinatePartial k G i) (partialDifferential k G i x) x := by
  change HasFDerivAt
    (fun y => (k.factorial : ℝ) *
      ∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), monomial (e.erase i) y)
    ((k.factorial : ℝ) • ∑ e ∈ (homogeneousPart k G).filter (i ∈ ·),
      monomialDifferential (e.erase i) x) x
  simpa only [Finset.sum_apply] using
    (HasFDerivAt.sum (fun e (_ : e ∈ (homogeneousPart k G).filter (i ∈ ·)) =>
      hasFDerivAt_monomial (e.erase i) x)).const_mul (k.factorial : ℝ)

/-- Matrix entries of the actual second derivative. -/
def hessianEntry (k : ℕ) (G : Finset (Finset V)) (i j : V) (x : V → ℝ) : ℝ :=
  partialDifferential k G i x (Pi.single j 1)

theorem hessianEntry_eq (k : ℕ) (G : Finset (Finset V)) (i j : V) (x : V → ℝ) :
    hessianEntry k G i j x =
      (k.factorial : ℝ) * ∑ e ∈ homogeneousPart k G,
        if i ∈ e ∧ j ∈ e ∧ i ≠ j then monomial ((e.erase i).erase j) x else 0 := by
  simp only [hessianEntry, partialDifferential, smul_apply,
    sum_apply, smul_eq_mul, monomialDifferential_single,
    Finset.mem_erase, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : i ∈ e <;> by_cases hj : j ∈ e <;> by_cases hij : i = j <;>
    simp_all [monomialDifferential_single, ne_comm]

@[simp] theorem hessianEntry_diagonal (k : ℕ) (G : Finset (Finset V))
    (i : V) (x : V → ℝ) : hessianEntry k G i i x = 0 := by
  simp [hessianEntry_eq]

theorem hessianEntry_symm (k : ℕ) (G : Finset (Finset V)) (i j : V) (x : V → ℝ) :
    hessianEntry k G i j x = hessianEntry k G j i x := by
  rw [hessianEntry_eq, hessianEntry_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  have he : (e.erase i).erase j = (e.erase j).erase i := by ext a; simp; tauto
  rw [he]
  by_cases hi : i ∈ e <;> by_cases hj : j ∈ e <;> by_cases hij : i = j <;>
    simp_all [ne_comm]

theorem partial_euler (k : ℕ) (G : Finset (Finset V)) (i : V) (x : V → ℝ) :
    partialDifferential (k + 1) G i x x = (k : ℝ) * coordinatePartial (k + 1) G i x := by
  simp only [partialDifferential, smul_apply, sum_apply,
    smul_eq_mul, monomial_euler]
  have h : (∑ e ∈ (homogeneousPart (k + 1) G).filter (i ∈ ·),
      ((e.erase i).card : ℝ) * monomial (e.erase i) x) =
      (k : ℝ) * ∑ e ∈ (homogeneousPart (k + 1) G).filter (i ∈ ·), monomial (e.erase i) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨he, hi⟩ := Finset.mem_filter.mp he
    rw [Finset.card_erase_of_mem hi, (mem_homogeneousPart.mp he).2]
    simp
  rw [h, coordinatePartial]
  ring

theorem partialDifferential_apply (k : ℕ) (G : Finset (Finset V)) (i : V) (x y : V → ℝ) :
    partialDifferential k G i x y = ∑ j, y j * hessianEntry k G i j x := by
  have hy : (∑ j, Pi.single j (y j)) = y := by ext j; simp
  conv_lhs => rw [← hy]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : Pi.single j (y j) = y j • Pi.single j (1 : ℝ) := by ext a; simp [Pi.single_apply]
  rw [h, map_smul]
  rfl

/-- The second differential of a square-free monomial. -/
def monomialHessian (e : Finset V) (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ((V → ℝ) →L[ℝ] ℝ) :=
  ∑ i ∈ e, (monomialDifferential (e.erase i) x).smulRight
    (ContinuousLinearMap.proj i)

theorem hasFDerivAt_monomialDifferential (e : Finset V) (x : V → ℝ) :
    HasFDerivAt (monomialDifferential e) (monomialHessian e x) x := by
  change HasFDerivAt
    (fun y => ∑ i ∈ e, monomial (e.erase i) y • ContinuousLinearMap.proj i)
    (∑ i ∈ e, (monomialDifferential (e.erase i) x).smulRight
      (ContinuousLinearMap.proj i)) x
  exact HasFDerivAt.fun_sum (fun i (_ : i ∈ e) =>
    (hasFDerivAt_monomial (e.erase i) x).smul_const
      (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ))

/-- The actual Fréchet derivative of the differential. -/
def hessian (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    (V → ℝ) →L[ℝ] ((V → ℝ) →L[ℝ] ℝ) :=
  (k.factorial : ℝ) • ∑ e ∈ homogeneousPart k G, monomialHessian e x

theorem hasFDerivAt_differential (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    HasFDerivAt (differential k G) (hessian k G x) x := by
  change HasFDerivAt
    (fun y => (k.factorial : ℝ) • ∑ e ∈ homogeneousPart k G, monomialDifferential e y)
    ((k.factorial : ℝ) • ∑ e ∈ homogeneousPart k G, monomialHessian e x) x
  exact (HasFDerivAt.fun_sum (fun e (_ : e ∈ homogeneousPart k G) =>
      hasFDerivAt_monomialDifferential e x)).fun_const_smul (k.factorial : ℝ)

theorem fderiv_differential_eq (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    fderiv ℝ (differential k G) x = hessian k G x :=
  (hasFDerivAt_differential k G x).fderiv

theorem hessian_single (k : ℕ) (G : Finset (Finset V)) (i j : V) (x : V → ℝ) :
    hessian k G x (Pi.single j 1) (Pi.single i 1) = hessianEntry k G i j x := by
  simp only [hessian, monomialHessian, smul_apply,
    sum_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', hessianEntry, partialDifferential,
    Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : i ∈ e <;> simp [hi, eq_comm]

theorem hessian_eq_fderiv_fderiv (k : ℕ) (G : Finset (Finset V)) (x : V → ℝ) :
    hessian k G x = fderiv ℝ (fderiv ℝ (weightPolynomial k G)) x := by
  have h : fderiv ℝ (weightPolynomial k G) = differential k G := funext (fderiv_eq k G)
  rw [h, fderiv_differential_eq]

omit [Fintype V] in
theorem partial_restrict_eq (k : ℕ) (S : Finset V) (G : Finset (Finset V))
    {i : V} (hi : i ∈ S) {x : V → ℝ} (hx : ∀ j ∉ S, x j = 0) :
    coordinatePartial k (restrictFamily S G) i x = coordinatePartial k G i x := by
  simp only [coordinatePartial, homogeneousPart_restrict, Finset.filter_filter]
  congr 1
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ⊆ S <;> by_cases hie : i ∈ e
  · simp [he, hie]
  · simp [hie]
  · have h' : ¬ e.erase i ⊆ S := by
      intro h
      apply he
      intro j hj
      by_cases hji : j = i
      · exact hji ▸ hi
      · exact h (Finset.mem_erase.mpr ⟨hji, hj⟩)
    simp [he, hie, monomial_eq_zero_of_not_subset hx h']
  · simp [hie]

theorem hessianEntry_restrict_eq (k : ℕ) (S : Finset V) (G : Finset (Finset V))
    {i j : V} (hi : i ∈ S) (hj : j ∈ S) {x : V → ℝ}
    (hx : ∀ a ∉ S, x a = 0) :
    hessianEntry k (restrictFamily S G) i j x = hessianEntry k G i j x := by
  rw [hessianEntry_eq, hessianEntry_eq, homogeneousPart_restrict, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ⊆ S
  · simp [he]
  · have h' : ¬ (e.erase i).erase j ⊆ S := by
      intro h
      apply he
      intro a ha
      by_cases hai : a = i
      · exact hai ▸ hi
      by_cases haj : a = j
      · exact haj ▸ hj
      exact h (Finset.mem_erase.mpr ⟨haj, Finset.mem_erase.mpr ⟨hai, ha⟩⟩)
    simp [he, monomial_eq_zero_of_not_subset hx h']

theorem continuousLinearMap_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (V → ℝ) →L[ℝ] F) (y : V → ℝ) :
    f y = ∑ i, y i • f (Pi.single i 1) := by
  have hy : (∑ i, Pi.single i (y i)) = y := by ext j; simp
  conv_lhs => rw [← hy]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (y i) = y i • Pi.single i (1 : ℝ) := by ext j; simp [Pi.single_apply]
  rw [h, map_smul]

theorem hessian_apply (k : ℕ) (G : Finset (Finset V)) (x y z : V → ℝ) :
    hessian k G x y z = ∑ i, ∑ j, z i * y j * hessianEntry k G i j x := by
  rw [continuousLinearMap_apply_eq_sum (hessian k G x y) z]
  apply Finset.sum_congr rfl
  intro i _
  rw [continuousLinearMap_apply_eq_sum (hessian k G x) y]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, hessian_single]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hessian_restrict_eq (k : ℕ) (S : Finset V) (G : Finset (Finset V))
    {x y z : V → ℝ} (hx : ∀ i ∉ S, x i = 0)
    (hy : ∀ i ∉ S, y i = 0) (hz : ∀ i ∉ S, z i = 0) :
    hessian k (restrictFamily S G) x y z = hessian k G x y z := by
  rw [hessian_apply, hessian_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [hessianEntry_restrict_eq k S G hi hj hx]
    · simp [hy j hj]
  · simp [hz i hi]

end Calculus

end SharpTopologicalOverlap.WeightPolynomial
