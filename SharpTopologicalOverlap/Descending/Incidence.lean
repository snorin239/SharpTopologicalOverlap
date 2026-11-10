module

public import SharpTopologicalOverlap.Simplicial
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Transposed target incidence

The descending construction sums a chain over the cofaces of a target
face. Transposing the actual simplicial boundary gives this operation
without a separate combinatorial double-counting convention.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Descending

open Simplicial

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {K : AbstractSimplicialComplex V} {k : ℕ}

abbrev chainAsCochain (K : AbstractSimplicialComplex V) (k : ℕ) :
    Chain K k ≃ₗ[Coeff] Cochain K k :=
  Finsupp.linearEquivFunOnFinite Coeff Coeff (Cell K k)

omit [LinearOrder V] in
@[simp] theorem chainAsCochain_apply (c : Chain K k) (s : Cell K k) :
    chainAsCochain K k c s = c s := rfl

/-- The transpose of the actual target boundary. -/
def transposeBoundary (k : ℕ) : Chain K k →ₗ[Coeff] Chain K (k + 1) where
  toFun c := (chainAsCochain K (k + 1)).symm (coboundary (chainAsCochain K k c))
  map_add' c b := by
    apply (chainAsCochain K (k + 1)).injective
    simp only [LinearEquiv.map_add, LinearEquiv.apply_symm_apply, coboundary_add]
  map_smul' r c := by
    apply (chainAsCochain K (k + 1)).injective
    simp only [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, coboundary_smul,
      RingHom.id_apply]

@[simp] theorem cochain_transposeBoundary (c : Chain K k) :
    chainAsCochain K (k + 1) (transposeBoundary k c) =
      coboundary (chainAsCochain K k c) :=
  (chainAsCochain K (k + 1)).apply_symm_apply _

theorem transposeBoundary_squared (c : Chain K k) :
    transposeBoundary (k + 1) (transposeBoundary k c) = 0 := by
  apply (chainAsCochain K (k + 2)).injective
  simp only [cochain_transposeBoundary, coboundary_coboundary, map_zero]

theorem evaluation_transposeBoundary (c : Chain K k) (b : Chain K (k + 1)) :
    evaluation (chainAsCochain K (k + 1) (transposeBoundary k c)) b =
      evaluation (chainAsCochain K k c) (boundary k b) := by
  rw [cochain_transposeBoundary, evaluation_coboundary]

@[simp] theorem evaluation_indicator (s : Cell K k) (c : Chain K k) :
    evaluation (Pi.single s 1) c = c s := by
  classical
  simp [evaluation, Finsupp.linearCombination_apply, Finsupp.sum_fintype, Pi.single_apply]

@[simp] theorem transposeBoundary_single_apply (s : Cell K k) (t : Cell K (k + 1)) :
    transposeBoundary k (Finsupp.single s 1) t = boundary k (Finsupp.single t 1) s := by
  have h := evaluation_transposeBoundary (Finsupp.single s 1) (Finsupp.single t 1)
  have hs : chainAsCochain K k (Finsupp.single s 1) = Pi.single s 1 :=
    Finsupp.linearEquivFunOnFinite_single Coeff Coeff _ s 1
  rw [hs] at h
  simpa only [evaluation_single, one_mul, chainAsCochain_apply,
    evaluation_indicator] using h

theorem transposeBoundary_single_apply_eq (s : Cell K k) (t : Cell K (k + 1)) :
    transposeBoundary k (Finsupp.single s 1) t = if s.1.1 ⊆ t.1.1 then 1 else 0 := by
  classical
  rw [transposeBoundary_single_apply]
  rw [TauCeti.OrderedSimplicialChain.boundary_single_one]
  by_cases hst : s.1.1 ⊆ t.1.1
  · obtain ⟨j, rfl⟩ := (t.exists_face_eq_iff_subset s).mpr hst
    simp only [ite_eq_left (t.face_val_subset j)]
    simp [TauCeti.OrderedSimplicialChain.boundaryCell_apply_face,
      show (-1 : Coeff) = 1 by decide]
  · rw [ite_eq_right hst]
    exact TauCeti.OrderedSimplicialChain.boundaryCell_apply_eq_zero_of_not_subset Coeff t s hst

variable {M : Type*} [AddCommGroup M] [Module Coeff M]

/-- Sum values on the cofaces of a given face, with the checked target
boundary coefficients. -/
def cofaceSum (c : Cell K (k + 1) → M) (s : Cell K k) : M :=
  Finsupp.linearCombination Coeff c (transposeBoundary k (Finsupp.single s 1))

theorem cofaceSum_eq (c : Cell K (k + 1) → M) (s : Cell K k) :
    cofaceSum c s = ∑ t : Cell K (k + 1), if s.1.1 ⊆ t.1.1 then c t else 0 := by
  classical
  rw [cofaceSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro t _
    rw [transposeBoundary_single_apply_eq]
    split_ifs <;> simp
  · intro t
    exact zero_smul Coeff (c t)

theorem linearCombination_cofaceSum (c : Cell K (k + 2) → M) (b : Chain K (k + 1)) :
    Finsupp.linearCombination Coeff (cofaceSum c) b =
      Finsupp.linearCombination Coeff c (transposeBoundary (k + 1) b) := by
  have h : Finsupp.linearCombination Coeff (cofaceSum c) =
      (Finsupp.linearCombination Coeff c).comp (transposeBoundary (k + 1)) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp [cofaceSum]
  exact LinearMap.congr_fun h b

/-- Each two-step coface occurs twice; this follows directly from the
checked simplicial boundary-square identity. -/
theorem cofaceSum_cofaceSum (c : Cell K (k + 2) → M) (s : Cell K k) :
    cofaceSum (cofaceSum c) s = 0 := by
  rw [cofaceSum, linearCombination_cofaceSum, transposeBoundary_squared, map_zero]

theorem map_cofaceSum {N : Type*} [AddCommGroup N] [Module Coeff N]
    (L : M →ₗ[Coeff] N) (c : Cell K (k + 1) → M) (s : Cell K k) :
    L (cofaceSum c s) = cofaceSum (fun t => L (c t)) s := by
  classical
  simp only [cofaceSum_eq, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem cofaceSum_add (c b : Cell K (k + 1) → M) (s : Cell K k) :
    cofaceSum (fun t => c t + b t) s = cofaceSum c s + cofaceSum b s := by
  classical
  simp only [cofaceSum_eq]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

omit [LinearOrder V] in
theorem evaluation_symmetric (b c : Chain K k) :
    evaluation (chainAsCochain K k b) c = evaluation (chainAsCochain K k c) b := by
  classical
  change c.sum (fun s r => r * b s) = b.sum (fun s r => r * c s)
  rw [Finsupp.sum_fintype c (fun s r => r * b s) (fun _ => zero_mul _),
    Finsupp.sum_fintype b (fun s r => r * c s) (fun _ => zero_mul _)]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

omit [Fintype V] [LinearOrder V] in
theorem linearCombination_smul (a : Cochain K k) (b : Chain K k) (u : M) :
    Finsupp.linearCombination Coeff (fun s => a s • u) b = evaluation a b • u := by
  have h : Finsupp.linearCombination Coeff (fun s => a s • u) =
      (LinearMap.toSpanSingleton Coeff M u).comp (evaluation a) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp
  exact LinearMap.congr_fun h b

/-- The top initialization is closed under the coface sum because the
given target chain is a cycle. -/
theorem cofaceSum_cycle (ζ : Chain K (k + 1)) (hζ : boundary k ζ = 0)
    (u : M) (s : Cell K k) : cofaceSum (fun t => ζ t • u) s = 0 := by
  rw [cofaceSum, linearCombination_smul]
  have h : evaluation (chainAsCochain K (k + 1) ζ)
      (transposeBoundary k (Finsupp.single s 1)) = 0 := by
    rw [evaluation_symmetric, evaluation_transposeBoundary, hζ, evaluation_zero]
  change evaluation (chainAsCochain K (k + 1) ζ)
    (transposeBoundary k (Finsupp.single s 1)) • u = 0
  rw [h, zero_smul]

omit [Module Coeff M] in
/-- Rewrite the ordered facets as the finite set of codimension-one subfaces. -/
theorem sum_facets_eq (t : Cell K (k + 1)) (a : Cell K k → M) :
    ∑ j : Fin (k + 2), a (t.face j) =
      ∑ s : Cell K k, if s.1.1 ⊆ t.1.1 then a s else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => t.face j)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.face_val_subset j⟩
  · intro i _ j _ hij
    exact t.face_injective hij
  · intro s hs
    obtain ⟨j, hj⟩ := (t.exists_face_eq_iff_subset s).mpr (Finset.mem_filter.mp hs).2
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro j _
    rfl

/-- The finite summation identity used to compare adjacent evaluations. -/
theorem sum_pairing_coface (a : Cell K k → M →ₗ[Coeff] Coeff)
    (c : Cell K (k + 1) → M) :
    ∑ s : Cell K k, a s (cofaceSum c s) =
      ∑ t : Cell K (k + 1), ∑ j : Fin (k + 2), a (t.face j) (c t) := by
  classical
  simp only [cofaceSum_eq, map_sum]
  have h : ∀ s : Cell K k, ∀ t : Cell K (k + 1),
      a s (if s.1.1 ⊆ t.1.1 then c t else 0) =
        if s.1.1 ⊆ t.1.1 then a s (c t) else 0 := by
    intro s t
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (sum_facets_eq t (fun s => a s (c t))).symm

end SharpTopologicalOverlap.Descending
