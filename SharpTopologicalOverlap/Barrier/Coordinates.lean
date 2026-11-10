module

public import SharpTopologicalOverlap.Spectral.Normalization
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Euclidean coordinates on the open probability simplex

The open simplex is an open subset of the Euclidean zero-sum hyperplane,
translated by the uniform vector. This supplies a boundaryless manifold
without imposing a manifold structure on the closed simplex.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff
open SharpTopologicalOverlap.Spectral

namespace SharpTopologicalOverlap.Barrier

variable {V : Type*} [Fintype V]

/-- The Euclidean zero-sum tangent space. -/
def euclideanZeroSumSpace : Submodule ℝ (EuclideanSpace ℝ V) where
  carrier := {z | ∑ i, z i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro a x hx
    change (∑ i, a * x i) = 0
    rw [← Finset.mul_sum, hx, mul_zero]

/-- The two zero-sum presentations use the same finite coordinates. -/
def zeroSumCoordinateEquiv : euclideanZeroSumSpace (V := V) ≃ₗ[ℝ] zeroSumSpace (V := V) where
  toFun z := ⟨(euclideanCoordinates (V := V)).symm z.1, z.2⟩
  invFun x := ⟨euclideanCoordinates x.1, x.2⟩
  left_inv z := by apply Subtype.ext; exact (euclideanCoordinates (V := V)).apply_symm_apply z.1
  right_inv x := by apply Subtype.ext; exact (euclideanCoordinates (V := V)).symm_apply_apply x.1
  map_add' x y := by apply Subtype.ext; exact map_add _ x.1 y.1
  map_smul' a x := by apply Subtype.ext; exact map_smul _ a x.1

/-- The algebraic coordinate change is automatically continuous in finite dimension. -/
def zeroSumCoordinates : euclideanZeroSumSpace (V := V) ≃L[ℝ] zeroSumSpace (V := V) :=
  zeroSumCoordinateEquiv.toContinuousLinearEquiv

@[simp] theorem zeroSumCoordinates_apply (z : euclideanZeroSumSpace (V := V)) (i : V) :
    (zeroSumCoordinates z).1 i = z.1 i := rfl

/-- Include Euclidean tangent vectors in ordinary finite coordinates. -/
def tangentCoordinates : euclideanZeroSumSpace (V := V) →L[ℝ] (V → ℝ) :=
  (zeroSumSpace (V := V)).subtypeL.comp zeroSumCoordinates.toContinuousLinearMap

@[simp] theorem tangentCoordinates_apply (z : euclideanZeroSumSpace (V := V)) (i : V) :
    tangentCoordinates z i = z.1 i := rfl

theorem sum_tangentCoordinates (z : euclideanZeroSumSpace (V := V)) :
    ∑ i, tangentCoordinates z i = 0 := z.2

variable [Nonempty V]

/-- Translation by the uniform vector in ordinary finite coordinates. -/
def affineCoordinates (z : euclideanZeroSumSpace (V := V)) : V → ℝ :=
  (uniform : Simplex V).weights + tangentCoordinates z

@[simp] theorem affineCoordinates_apply (z : euclideanZeroSumSpace (V := V)) (i : V) :
    affineCoordinates z i = (uniform : Simplex V).weights i + z.1 i := rfl

theorem sum_affineCoordinates (z : euclideanZeroSumSpace (V := V)) :
    ∑ i, affineCoordinates z i = 1 := by
  simp only [affineCoordinates, Pi.add_apply, Finset.sum_add_distrib,
    sum_coordinates, sum_tangentCoordinates, add_zero]

theorem continuous_affineCoordinates :
    Continuous (affineCoordinates (V := V)) := continuous_const.add tangentCoordinates.continuous

/-- The open set of translated tangent coordinates with every coordinate positive. -/
def openSimplexDomain : TopologicalSpace.Opens (euclideanZeroSumSpace (V := V)) :=
  ⟨{z | ∀ i, 0 < affineCoordinates z i}, by
    have h : ∀ i : V, IsOpen {z : euclideanZeroSumSpace (V := V) | 0 < affineCoordinates z i} :=
      fun i => isOpen_lt continuous_const ((continuous_apply i).comp continuous_affineCoordinates)
    simpa only [Set.iInter_ofPred] using isOpen_iInter_of_finite h⟩

@[simp] theorem mem_openSimplexDomain (z : euclideanZeroSumSpace (V := V)) :
    z ∈ openSimplexDomain (V := V) ↔ ∀ i, 0 < affineCoordinates z i := Iff.rfl

theorem zero_mem_openSimplexDomain :
    (0 : euclideanZeroSumSpace (V := V)) ∈ openSimplexDomain (V := V) := by
  intro i
  simp only [affineCoordinates_apply, Submodule.coe_zero, PiLp.zero_apply, add_zero,
    coordinate_uniform]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

instance : Nonempty (openSimplexDomain (V := V)) := ⟨⟨0, zero_mem_openSimplexDomain⟩⟩

/-- Points of the full-support open face of the probability simplex. -/
abbrev PositiveSimplex (V : Type*) [Fintype V] :=
  {μ : Simplex V // ∀ i, 0 < μ.weights i}

omit [Nonempty V] in
theorem isOpen_positiveSimplex : IsOpen {μ : Simplex V | ∀ i, 0 < μ.weights i} := by
  simpa only [Set.iInter_ofPred] using isOpen_iInter_of_finite
    (fun i : V => isOpen_lt continuous_const (continuous_coordinate i))

omit [Nonempty V] in
theorem positive_iff_support_eq_univ (μ : Simplex V) :
    (∀ i, 0 < μ.weights i) ↔ support μ = Finset.univ := by
  constructor
  · intro h
    ext i
    exact iff_of_true (mem_support_iff_coordinate_pos.mpr (h i)) (Finset.mem_univ i)
  · intro h i
    apply mem_support_iff_coordinate_pos.mp
    rw [h]
    exact Finset.mem_univ i

/-- A positive translated coordinate vector as an actual probability simplex point. -/
def toPositiveSimplex (z : openSimplexDomain (V := V)) : PositiveSimplex V := by
  let c : CoordinateSimplex V :=
    ⟨affineCoordinates z.1, ⟨fun i => (z.2 i).le, sum_affineCoordinates z.1⟩⟩
  refine ⟨coordinateHomeomorph.symm c, ?_⟩
  intro i
  have hc := congrArg (fun y : CoordinateSimplex V => y.1 i)
    (coordinateHomeomorph.apply_symm_apply c)
  change (coordinateHomeomorph.symm c).weights i = affineCoordinates z.1 i at hc
  rw [hc]
  exact z.2 i

@[simp] theorem toPositiveSimplex_coordinate (z : openSimplexDomain (V := V)) (i : V) :
    (toPositiveSimplex z).1.weights i = affineCoordinates z.1 i := by
  exact congrArg (fun y : CoordinateSimplex V => y.1 i)
    (coordinateHomeomorph.apply_symm_apply _)

/-- Subtract the uniform vector from a positive simplex point. -/
def fromPositiveSimplex (μ : PositiveSimplex V) : openSimplexDomain (V := V) := by
  let z : euclideanZeroSumSpace (V := V) :=
    ⟨euclideanCoordinates ((μ.1.weights : V → ℝ) - (uniform : Simplex V).weights), by
      change (∑ i, (μ.1.weights i - (uniform : Simplex V).weights i)) = 0
      rw [Finset.sum_sub_distrib, sum_coordinates, sum_coordinates, sub_self]⟩
  refine ⟨z, ?_⟩
  intro i
  change 0 < (uniform : Simplex V).weights i +
    (μ.1.weights i - (uniform : Simplex V).weights i)
  convert μ.2 i using 1; ring

@[simp] theorem fromPositiveSimplex_coordinate (μ : PositiveSimplex V) (i : V) :
    (fromPositiveSimplex μ).1.1 i = μ.1.weights i - (uniform : Simplex V).weights i := rfl

/-- The open coordinate domain and the full-support simplex are homeomorphic. -/
def openSimplexHomeomorph : openSimplexDomain (V := V) ≃ₜ PositiveSimplex V where
  toFun := toPositiveSimplex
  invFun := fromPositiveSimplex
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    rw [fromPositiveSimplex_coordinate, toPositiveSimplex_coordinate, affineCoordinates_apply]
    ring
  right_inv μ := by
    apply Subtype.ext
    apply Convexity.StdSimplex.ext
    ext i
    rw [toPositiveSimplex_coordinate, affineCoordinates_apply, fromPositiveSimplex_coordinate]
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply coordinateHomeomorph.symm.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_affineCoordinates.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply euclideanCoordinates.continuous.comp
    exact ((coordinateHomeomorph.continuous.comp continuous_subtype_val).subtype_val).sub continuous_const

instance : IsManifold 𝓘(ℝ, euclideanZeroSumSpace (V := V)) ∞
    (openSimplexDomain (V := V)) := inferInstance

end SharpTopologicalOverlap.Barrier
