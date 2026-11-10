module

public import SharpTopologicalOverlap.Spectral.Partite
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Coordinates on a face and its tangent space -/

@[expose] public noncomputable section

open scoped BigOperators

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend coordinates by zero outside an ambient vertex set. -/
def extendCoordinates (S : Finset V) : (S → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun x i := if hi : i ∈ S then x ⟨i, hi⟩ else 0
  map_add' x y := by ext i; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' a x := by ext i; by_cases hi : i ∈ S <;> simp [hi]

omit [Fintype V] in
@[simp] theorem extendCoordinates_apply_mem (S : Finset V) (x : S → ℝ) (i : S) :
    extendCoordinates S x i.1 = x i := by simp [extendCoordinates, i.2]

omit [Fintype V] in
@[simp] theorem extendCoordinates_apply_notMem (S : Finset V) (x : S → ℝ) {i : V}
    (hi : i ∉ S) : extendCoordinates S x i = 0 := by simp [extendCoordinates, hi]

theorem extendCoordinates_sum (S : Finset V) (x : S → ℝ) :
    (∑ i, extendCoordinates S x i) = ∑ i : S, x i := by
  rw [Finset.sum_coe_sort_eq_attach]
  exact (Finset.sum_attach_eq_sum_dite S x).symm

omit [Fintype V] in
theorem extendCoordinates_restrict (S : Finset V) {x : V → ℝ}
    (hx : ∀ i ∉ S, x i = 0) : extendCoordinates S (fun i : S => x i.1) = x := by
  ext i
  by_cases hi : i ∈ S <;> simp [extendCoordinates, hi, hx]

/-- The continuous version of zero extension, used for the derivative chain rule. -/
def extendCoordinatesCLM (S : Finset V) : (S → ℝ) →L[ℝ] (V → ℝ) :=
  (extendCoordinates S).toContinuousLinearMap

@[simp] theorem extendCoordinatesCLM_apply (S : Finset V) (x : S → ℝ) :
    extendCoordinatesCLM S x = extendCoordinates S x := rfl

/-- All ambient directions supported on `S` and of total mass zero. -/
def faceTangentSpace (S : Finset V) : Submodule ℝ (V → ℝ) where
  carrier := {x | (∀ i ∉ S, x i = 0) ∧ (∑ i, x i) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxs⟩ ⟨hy, hys⟩
    exact ⟨fun i hi => by simp [hx i hi, hy i hi], by simp [Finset.sum_add_distrib, hxs, hys]⟩
  smul_mem' := by
    rintro a x ⟨hx, hxs⟩
    refine ⟨fun i hi => by simp [hx i hi], ?_⟩
    change (∑ i, a * x i) = 0
    rw [← Finset.mul_sum, hxs, mul_zero]

/-- Coordinates on `S` identify its ordinary simplex tangent space with the
actual ambient tangent space of the closed face on `S`. -/
def faceTangentEquiv (S : Finset V) :
    zeroSumSpace (V := S) ≃ₗ[ℝ] faceTangentSpace S where
  toFun x := ⟨extendCoordinates S x, by
    refine ⟨fun i hi => extendCoordinates_apply_notMem S x hi, ?_⟩
    rw [extendCoordinates_sum]
    exact x.2⟩
  invFun x := ⟨fun i : S => x.1 i.1, by
    change (∑ i : S, x.1 i.1) = 0
    rw [← extendCoordinates_sum, extendCoordinates_restrict S x.2.1]
    exact x.2.2⟩
  left_inv x := by apply Subtype.ext; ext i; exact extendCoordinates_apply_mem S x i
  right_inv x := by apply Subtype.ext; exact extendCoordinates_restrict S x.2.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (extendCoordinates S) (x : S → ℝ) (y : S → ℝ)
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (extendCoordinates S) a (x : S → ℝ)

omit [DecidableEq V] in
theorem sum_face_coordinates (μ : Simplex V) :
    (∑ i : support μ, μ.weights i.1) = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    (∑ i ∈ support μ, μ.weights i) = ∑ i : V, μ.weights i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_contra h
      exact hi (mem_support.mpr h)
    _ = 1 := sum_coordinates μ

/-- The same probability vector, reindexed on its positive coordinates. -/
def supportPoint (μ : Simplex V) : Simplex (support μ) :=
  coordinateHomeomorph.symm ⟨fun i : support μ => μ.weights i.1,
    fun i => coordinate_nonneg μ i.1, sum_face_coordinates μ⟩

omit [DecidableEq V] in
@[simp] theorem supportPoint_coordinate (μ : Simplex V) (i : support μ) :
    (supportPoint μ).weights i = μ.weights i.1 := by
  exact congrFun (congrArg Subtype.val (coordinateHomeomorph.apply_symm_apply
    ⟨fun i : support μ => μ.weights i.1,
      fun i => coordinate_nonneg μ i.1, sum_face_coordinates μ⟩)) i

omit [DecidableEq V] in
theorem supportPoint_positive (μ : Simplex V) (i : support μ) :
    0 < (supportPoint μ).weights i := by
  rw [supportPoint_coordinate]
  exact mem_support_iff_coordinate_pos.mp i.2

theorem extend_supportPoint (μ : Simplex V) :
    extendCoordinates (support μ) ((supportPoint μ).weights : support μ → ℝ) =
      (μ.weights : V → ℝ) := by
  have hpoint : ((supportPoint μ).weights : support μ → ℝ) =
      fun i : support μ => μ.weights i.1 := funext (supportPoint_coordinate μ)
  rw [hpoint]
  apply extendCoordinates_restrict
  intro i hi
  by_contra h
  exact hi (mem_support.mpr h)

end SharpTopologicalOverlap.Spectral
