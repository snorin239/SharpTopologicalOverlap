module

public import SharpTopologicalOverlap.BMN.ConvexPosition
public import SharpTopologicalOverlap.BMN.Types
public import SharpTopologicalOverlap.BMN.Transport
public import SharpTopologicalOverlap.BMN.Normalization
public import SharpTopologicalOverlap.Overlap.Affine
public import Mathlib.Data.Nat.Choose.Bounds

/-! # The BMN upper construction (Theorem 7.1)

The source subsets are counted with their indices. The construction is in
convex position, every source top face is nondegenerate, and the error is
uniform in the query point and the number of source vertices.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

/-- Theorem 7.1, with an explicit binomial error in place of `O_d(n^d)`. -/
theorem exists_configuration {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      ConvexIndependent ℝ p ∧
      (∀ σ : Finset (Fin n), σ.card = d + 1 →
        AffineIndependent ℝ (fun i : σ => p i)) ∧
      ∀ r, (hullCount d p r : ℝ) ≤
        ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
          (2 * d : ℝ) * ((n - 1).choose d : ℝ) := by
  let p := configuration d n
  let e := (euclideanCoordinates (V := Fin d)).toLinearEquiv
  have hp : Separated p := configuration_separated d n
  refine ⟨e ∘ p, convexIndependent_linearEquiv e
    (convexIndependent_of_separated hd hp), ?_, ?_⟩
  · intro σ hσ
    exact affineIndependent_linearEquiv e (hp.affineIndependent_face hσ)
  · intro r
    rw [hullCount_linearEquiv]
    exact hullCount_le_of_separated hp (e.symm r)

theorem choose_pred_le_pow (n d : ℕ) : ((n - 1).choose d : ℝ) ≤ (n : ℝ) ^ d := by
  have hbase : (n - 1) ^ d ≤ n ^ d := by gcongr; exact Nat.sub_le n 1
  exact_mod_cast (Nat.choose_le_pow (n - 1) d).trans hbase

/-- The manuscript form, with the uniform polynomial error constant `2*d`. -/
theorem exists_configuration_polynomial_error {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      ConvexIndependent ℝ p ∧
      (∀ σ : Finset (Fin n), σ.card = d + 1 →
        AffineIndependent ℝ (fun i : σ => p i)) ∧
      ∀ r, (hullCount d p r : ℝ) ≤
        ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) + (2 * d : ℝ) * (n : ℝ) ^ d := by
  obtain ⟨p, hc, hi, hb⟩ := exists_configuration hd n
  refine ⟨p, hc, hi, fun r => (hb r).trans ?_⟩
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (choose_pred_le_pow n d)
      (show (0 : ℝ) ≤ (2 * d : ℝ) by positivity))

/-- The same configuration yields a continuous map on the source skeleton. -/
theorem exists_affine_overlap_bound {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      ConvexIndependent ℝ p ∧
      (∀ σ : Finset (Fin n), σ.card = d + 1 →
        AffineIndependent ℝ (fun i : σ => p i)) ∧
      (overlap (affineSkeletonMap d p) : ℝ) ≤
        ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
          (2 * d : ℝ) * ((n - 1).choose d : ℝ) := by
  obtain ⟨p, hc, hi, hb⟩ := exists_configuration hd n
  exact ⟨p, hc, hi, overlap_affineSkeletonMap_le p hb⟩

/-- The BMN overlap estimate for affine interpolation in every dimension. -/
theorem exists_affineSkeletonMap_overlap_bound (d n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      (overlap (affineSkeletonMap d p) : ℝ) ≤
        ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
          (2 * d : ℝ) * ((n - 1).choose d : ℝ) := by
  let p := configuration d n
  let e := (euclideanCoordinates (V := Fin d)).toLinearEquiv
  refine ⟨e ∘ p, overlap_affineSkeletonMap_le _ fun r => ?_⟩
  rw [hullCount_linearEquiv]
  exact hullCount_le_of_separated (configuration_separated d n) (e.symm r)

/-- A continuous-map upper bound with no remaining geometric inputs. -/
theorem exists_continuous_overlap_bound {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
      (overlap f : ℝ) ≤ ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
        (2 * d : ℝ) * ((n - 1).choose d : ℝ) := by
  obtain ⟨p, _, _, hb⟩ := exists_affine_overlap_bound hd n
  exact ⟨affineSkeletonMap d p, hb⟩

/-- The binomially normalized upper bound, with the manuscript's factorial.
This is the upper-bound input for the later definition of `c_d^top`. -/
theorem eventually_exists_normalized_overlap_lt {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
        (overlap f : ℝ) / (n.choose (d + 1) : ℝ) < overlapThreshold d + ε := by
  have hnum := (tendsto_normalized_bmn_bound d).eventually
    (gt_mem_nhds (show overlapThreshold d < overlapThreshold d + ε by linarith))
  filter_upwards [hnum] with n hn
  obtain ⟨f, hf⟩ := exists_continuous_overlap_bound hd n
  refine ⟨f, (div_le_div_of_nonneg_right hf (Nat.cast_nonneg _)).trans_lt hn⟩

end SharpTopologicalOverlap.BMN
