module

public import SharpTopologicalOverlap.Overlap
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

/-! # Shared definitions for the BMN upper construction -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open scoped BigOperators

/-- The growth function used to separate coordinates. -/
def growth (d : ℕ) (x : ℝ) : ℝ := ((d + 1).factorial : ℝ) * x ^ (d + 1)

/-- Coordinates are ordered first by coordinate, then by source vertex. -/
structure Separated {d n : ℕ} (p : Fin n → Fin d → ℝ) : Prop where
  one_lt : ∀ i j, 1 < p i j
  gap : ∀ (i i' : Fin n) (j j' : Fin d),
    j < j' ∨ (j = j' ∧ i < i') → growth d (p i j) < p i' j'

variable {V E : Type*} [Fintype V] [AddCommGroup E] [Module ℝ E]

/-- Source subsets whose placed convex hull contains a query point. -/
def hullFacesAt (d : ℕ) (p : V → E) (r : E) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powersetCard (d + 1)).filter
    (fun σ => r ∈ convexHull ℝ (p '' (σ : Set V)))

@[simp] theorem mem_hullFacesAt {d : ℕ} {p : V → E} {r : E} {σ : Finset V} :
    σ ∈ hullFacesAt d p r ↔
      σ.card = d + 1 ∧ r ∈ convexHull ℝ (p '' (σ : Set V)) := by
  classical
  simp [hullFacesAt]

/-- The number of placed source faces containing a query point. -/
def hullCount (d : ℕ) (p : V → E) (r : E) : ℕ := (hullFacesAt d p r).card

end SharpTopologicalOverlap.BMN
