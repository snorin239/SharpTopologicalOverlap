module

public import SharpTopologicalOverlap.Polynomial.Threshold
public import TauCeti.AlgebraicTopology.Singular.Relative

/-! # The sublevel pair in Theorem 5.1 -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Sublevel

open WeightPolynomial

variable {V : Type} [Fintype V] [DecidableEq V]

def strictSublevel (d : ℕ) (G : Finset (Finset V)) : Set (Simplex V) :=
  {μ | weightPolynomial (d + 1) G (μ.weights : V → ℝ) < overlapThreshold d}

def zeroSet (d : ℕ) (G : Finset (Finset V)) : Set (Simplex V) :=
  {μ | weightPolynomial (d + 1) G (μ.weights : V → ℝ) = 0}

omit [Fintype V] [DecidableEq V] in
theorem zeroSet_subset_strictSublevel (d : ℕ) (G : Finset (Finset V)) :
    zeroSet d G ⊆ strictSublevel d G := by
  intro μ hμ
  change _ < _
  rw [show weightPolynomial (d + 1) G (μ.weights : V → ℝ) = 0 from hμ]
  exact overlapThreshold_pos d

def sublevelPair (d : ℕ) (G : Finset (Finset V)) : TopPair.{0} :=
  TopPair.ofInclusion (X := TopCat.of (Simplex V)) (zeroSet_subset_strictSublevel d G)

end SharpTopologicalOverlap.Sublevel
