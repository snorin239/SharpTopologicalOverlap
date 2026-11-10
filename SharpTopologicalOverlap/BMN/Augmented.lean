module

public import SharpTopologicalOverlap.BMN.Configuration
public import SharpTopologicalOverlap.BMN.Determinant
public import SharpTopologicalOverlap.Geometry.PlacementAvoidance
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Data.Finset.Sort

/-! # Augmented affine-coordinate matrices -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open scoped BigOperators
open Convexity

attribute [local instance] ConvexSpace.ofModule

/-- Each row consists of a homogenizing coordinate followed by the point. -/
def augmentedMatrix {d : ℕ} (q : Fin (d + 1) → Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i => Fin.cons 1 (q i)

@[simp] theorem augmentedMatrix_zero {d : ℕ} (q : Fin (d + 1) → Fin d → ℝ)
    (i : Fin (d + 1)) : augmentedMatrix q i 0 = 1 := rfl

@[simp] theorem augmentedMatrix_succ {d : ℕ} (q : Fin (d + 1) → Fin d → ℝ)
    (i : Fin (d + 1)) (j : Fin d) : augmentedMatrix q i j.succ = q i j := rfl

theorem augmentedMatrix_one_le_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} (hp : Separated p) (s : Fin (d + 1) → Fin n) :
    ∀ i j, 1 ≤ augmentedMatrix (p ∘ s) i j := by
  intro i j
  cases j using Fin.cases with
  | zero => simp
  | succ j => exact (hp.one_lt (s i) j).le

theorem augmentedMatrix_column_lt_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} (hp : Separated p) (s : Fin (d + 1) → Fin n) :
    ∀ i i' j j', j < j' →
      augmentedMatrix (p ∘ s) i j < augmentedMatrix (p ∘ s) i' j' := by
  intro i i' j j' h
  cases j using Fin.cases with
  | zero =>
    cases j' using Fin.cases with
    | zero => exact (lt_irrefl _ h).elim
    | succ j' => exact hp.one_lt (s i') j'
  | succ j =>
    cases j' using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ h).elim
    | succ j' => exact hp.cross_coordinate_lt (s i) (s i') (by simpa using h)

theorem augmentedMatrix_dominant_identity_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} (hp : Separated p)
    {s : Fin (d + 1) → Fin n} (hs : StrictMono s) :
    DominantPermutation (augmentedMatrix (p ∘ s)) (Equiv.refl _) := by
  apply dominantPermutation_of_lower_gap
  intro j hj l hl
  cases j using Fin.cases with
  | zero => exact (lt_irrefl _ hj).elim
  | succ j =>
    exact hp.gap (s l) (s j.succ) j j (Or.inr ⟨rfl, hs hl⟩)

theorem det_augmentedMatrix_pos_of_separated {d n : ℕ}
    {p : Fin n → Fin d → ℝ} (hp : Separated p)
    {s : Fin (d + 1) → Fin n} (hs : StrictMono s) :
    0 < (augmentedMatrix (p ∘ s)).det := by
  exact det_pos_of_dominant_identity _
    (augmentedMatrix_one_le_of_separated hp s)
    (augmentedMatrix_column_lt_of_separated hp s)
    (augmentedMatrix_dominant_identity_of_separated hp hs)

theorem affineIndependent_of_det_augmentedMatrix_ne_zero {d : ℕ}
    {q : Fin (d + 1) → Fin d → ℝ} (h : (augmentedMatrix q).det ≠ 0) :
    AffineIndependent ℝ q := by
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero h
  apply affineIndependent_iff.mpr
  intro s w hw hs i hi
  have haug : ∑ j ∈ s, w j • augmentedMatrix q j = 0 := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have hcoord := congrFun hs j
      simpa using hcoord
  exact (linearIndependent_iff'.mp hli) s w haug i hi

theorem Separated.affineIndependent_face {d n : ℕ}
    {p : Fin n → Fin d → ℝ} (hp : Separated p) {σ : Finset (Fin n)}
    (hσ : σ.card = d + 1) : AffineIndependent ℝ (fun i : σ => p i) := by
  let e := σ.orderIsoOfFin hσ
  have hsorted : AffineIndependent ℝ (p ∘ σ.orderEmbOfFin hσ) :=
    affineIndependent_of_det_augmentedMatrix_ne_zero
      (ne_of_gt (det_augmentedMatrix_pos_of_separated hp (σ.orderEmbOfFin hσ).strictMono))
  have hind := hsorted.comp_embedding e.symm.toEquiv.toEmbedding
  convert hind using 1
  funext i
  change p i.val = p (e (e.symm i)).val
  simp

theorem det_updateRow_nonneg_of_mem_convexHull {d : ℕ}
    {q : Fin (d + 1) → Fin d → ℝ} {r : Fin d → ℝ}
    (hdet : 0 ≤ (augmentedMatrix q).det)
    (hr : r ∈ convexHull ℝ (Set.range q)) (k : Fin (d + 1)) :
    0 ≤ ((augmentedMatrix q).updateRow k (Fin.cons 1 r)).det := by
  rw [Geometry.convexHull_range_eq_range_affineMapMk] at hr
  obtain ⟨w, rfl⟩ := hr
  have hrow : Fin.cons 1 (StdSimplex.affineMapMk (R := ℝ) q w) =
      ∑ i, w.weights i • augmentedMatrix q i := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply,
        augmentedMatrix_zero, smul_eq_mul, mul_one]
      exact w.total_of_fintype.symm
    · simp only [Fin.cons_succ, StdSimplex.affineMapMk_apply_eq_sum_of_fintype,
        Finset.sum_apply, Pi.smul_apply, augmentedMatrix_succ, smul_eq_mul]
  simp only [StdSimplex.affineMapMk_apply_eq_sum_of_fintype] at hrow ⊢
  rw [hrow, Matrix.det_updateRow_sum]
  exact mul_nonneg (w.weights_nonneg k) hdet

end SharpTopologicalOverlap.BMN
