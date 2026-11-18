import SharpTopologicalOverlap

/-! Reproducible statement and axiom audits for Theorem 1.2.
The sole import is the public project umbrella. -/

noncomputable section

open SharpTopologicalOverlap

namespace Theorem12Verification

/-- The manuscript bound with its entire deletion constant expanded. -/
theorem manuscript_bound {n d : ℕ} (hd : 0 < d)
    (hn : (∑ p ∈ Finset.Icc 1 d,
      (d + 1).choose (p + 1) * (d + 1 - p) * (d / p)) < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - ((∑ p ∈ Finset.Icc 1 d,
      (d + 1).choose (p + 1) * (d + 1 - p) * (d / p) : ℕ) : ℝ)) /
      (d + 1 : ℝ)) ^ (d + 1) ≤ (overlap f : ℝ) :=
  finite_overlap_bound hd hn f

/-- The lower bound is attained by the count at an actual target point. -/
theorem pointwise_bound {n d : ℕ} (hd : 0 < d) (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    ∃ y : EuclideanSpace ℝ (Fin d),
      (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤
        (overlapCount f y : ℝ) := by
  obtain ⟨y, hy⟩ := overlap_attained f
  exact ⟨y, by rw [hy]; exact finite_overlap_bound hd hn f⟩

-- The smallest admissible simplex in dimension one has exactly two vertices.
example (f : C(Skeleton (Fin 2) 1, EuclideanSpace ℝ (Fin 1))) :
    (1 : ℝ) / 4 ≤ (overlap f : ℝ) := by
  have h := finite_overlap_bound (d := 1) (by decide) (by decide) f
  norm_num [deletionBound_one] at h ⊢
  exact h

#print axioms Comparison.canonicalHomologyComparison
#print axioms Sublevel.sublevel_cycle_fills
#print axioms Sublevel.sublevel_homology_vanishes
#print axioms IntersectionData.weightSpace_fills
#print axioms IntersectionData.weightSpace_homology_vanishes
#print axioms finite_overlap_bound
#print axioms manuscript_bound
#print axioms pointwise_bound

end Theorem12Verification
