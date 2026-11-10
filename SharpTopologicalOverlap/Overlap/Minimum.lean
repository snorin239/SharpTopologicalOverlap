module

public import SharpTopologicalOverlap.Overlap.Affine
public import Mathlib.Topology.Order.LiminfLimsup

/-! # Finite minima and the topological and affine overlap constants

The affine minimum ranges over vertex placements and their affine interpolation.
Placements may have coincident vertices; source faces are still counted separately.
The denominator is zero below `d + 1`, where real division makes the normalized
sequences zero. These finitely many initial terms do not affect either constant.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

/-- The least overlap among all continuous maps on the source skeleton. -/
def minimumOverlap (d n : ℕ) : ℕ :=
  sInf (Set.range (fun f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)) => overlap f))

/-- The least overlap among affine interpolations of vertex placements. -/
def affineMinimumOverlap (d n : ℕ) : ℕ :=
  sInf (Set.range (fun p : Fin n → EuclideanSpace ℝ (Fin d) =>
    overlap (affineSkeletonMap d p)))

theorem minimumOverlap_attained (d n : ℕ) :
    ∃ f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
      overlap f = minimumOverlap d n := by
  exact Nat.sInf_mem (s := Set.range
    (fun f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)) => overlap f))
      ⟨_, ⟨ContinuousMap.const _ 0, rfl⟩⟩

theorem affineMinimumOverlap_attained (d n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      overlap (affineSkeletonMap d p) = affineMinimumOverlap d n := by
  exact Nat.sInf_mem (s := Set.range
    (fun p : Fin n → EuclideanSpace ℝ (Fin d) => overlap (affineSkeletonMap d p)))
      ⟨_, ⟨fun _ => 0, rfl⟩⟩

theorem minimumOverlap_le {d n : ℕ}
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    minimumOverlap d n ≤ overlap f :=
  Nat.sInf_le (Set.mem_range_self f)

theorem affineMinimumOverlap_le {d n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin d)) :
    affineMinimumOverlap d n ≤ overlap (affineSkeletonMap d p) :=
  Nat.sInf_le (Set.mem_range_self p)

theorem minimumOverlap_le_affineMinimumOverlap (d n : ℕ) :
    minimumOverlap d n ≤ affineMinimumOverlap d n := by
  obtain ⟨p, hp⟩ := affineMinimumOverlap_attained d n
  rw [← hp]
  exact minimumOverlap_le _

theorem minimumOverlap_le_choose (d n : ℕ) : minimumOverlap d n ≤ n.choose (d + 1) := by
  obtain ⟨f, hf⟩ := minimumOverlap_attained d n
  rw [← hf]
  simpa using overlap_le_choose f

theorem affineMinimumOverlap_le_choose (d n : ℕ) :
    affineMinimumOverlap d n ≤ n.choose (d + 1) := by
  obtain ⟨p, hp⟩ := affineMinimumOverlap_attained d n
  rw [← hp]
  simpa using overlap_le_choose (affineSkeletonMap d p)

/-- The continuous minimum normalized by the number of source top faces. -/
def normalizedMinimumOverlap (d n : ℕ) : ℝ :=
  (minimumOverlap d n : ℝ) / (n.choose (d + 1) : ℝ)

/-- The affine minimum normalized by the number of source top faces. -/
def normalizedAffineMinimumOverlap (d n : ℕ) : ℝ :=
  (affineMinimumOverlap d n : ℝ) / (n.choose (d + 1) : ℝ)

theorem normalizedMinimumOverlap_nonneg (d n : ℕ) : 0 ≤ normalizedMinimumOverlap d n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem normalizedAffineMinimumOverlap_nonneg (d n : ℕ) :
    0 ≤ normalizedAffineMinimumOverlap d n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem normalizedMinimumOverlap_le_one (d n : ℕ) : normalizedMinimumOverlap d n ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast minimumOverlap_le_choose d n

theorem normalizedAffineMinimumOverlap_le_one (d n : ℕ) :
    normalizedAffineMinimumOverlap d n ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast affineMinimumOverlap_le_choose d n

theorem normalizedMinimumOverlap_le_affine (d n : ℕ) :
    normalizedMinimumOverlap d n ≤ normalizedAffineMinimumOverlap d n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast minimumOverlap_le_affineMinimumOverlap d n

/-- The manuscript's constant `c_d^top`, defined by the liminf of finite minima. -/
def topologicalOverlapConstant (d : ℕ) : ℝ :=
  Filter.liminf (normalizedMinimumOverlap d) Filter.atTop

/-- The affine analogue `c_d^aff`, with the same binomial normalization. -/
def affineOverlapConstant (d : ℕ) : ℝ :=
  Filter.liminf (normalizedAffineMinimumOverlap d) Filter.atTop

end SharpTopologicalOverlap
