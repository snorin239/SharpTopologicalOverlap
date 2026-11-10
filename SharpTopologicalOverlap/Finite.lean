module

public import SharpTopologicalOverlap.Finite.Assembly
public import SharpTopologicalOverlap.Comparison.Supported
public import SharpTopologicalOverlap.Sublevel

/-! # Theorem 1.2: the finite topological overlap bound -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

/-- Theorem 1.2 of the reference manuscript. -/
theorem finite_overlap_bound {n d : ℕ} (hd : 2 ≤ d) (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤ (overlap f : ℝ) :=
  finite_overlap_bound_of_providers hd hn f Comparison.canonicalHomologyComparison
    (fun _ _ _ _ G hG hpar j hj => Sublevel.sublevel_homology_vanishes d G hG hpar j hj)

end SharpTopologicalOverlap
