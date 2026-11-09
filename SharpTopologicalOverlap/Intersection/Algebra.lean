module

public import SharpTopologicalOverlap.Simplicial
public import Mathlib.Logic.Relation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Acyclic

/-! # Algebraic ingredients of the intersection-cochain construction

The edge identity propagates the cocycle condition from a zero anchor along
edge paths. The cone identity closes a fundamental chain to a cycle, as in
Appendix A, Step 5. Both statements use the actual ordered chain boundary.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Simplicial

variable {V : Type*} [LinearOrder V] {K : AbstractSimplicialComplex V} {k : ℕ}

/-- In characteristic two, two cochains whose sum is a coboundary have the
same coboundary. This is the algebraic content of an intersection edge. -/
theorem coboundary_eq_of_add_eq_coboundary
    {a b : Cochain K (k + 1)} {e : Cochain K k}
    (h : a + b = coboundary e) : coboundary a = coboundary b := by
  have hz : coboundary a + coboundary b = 0 := by
    rw [← coboundary_add, h, coboundary_coboundary]
  funext s
  have hs := congrFun hz s
  change coboundary a s + coboundary b s = 0 at hs
  have htwo : ∀ x : Coeff, x + x = 0 := by decide
  calc
    coboundary a s = coboundary a s + (coboundary b s + coboundary b s) := by
      rw [htwo, add_zero]
    _ = (coboundary a s + coboundary b s) + coboundary b s := (add_assoc _ _ _).symm
    _ = coboundary b s := by rw [hs, zero_add]

/-- The coboundary is constant along a path whose edges satisfy the
intersection-cochain identity. -/
theorem coboundary_eq_of_edgePath {W : Type*} (E : W → W → Prop)
    (a : W → Cochain K (k + 1))
    (hE : ∀ v w, E v w → ∃ e : Cochain K k, a v + a w = coboundary e)
    {v w : W} (hpath : Relation.ReflTransGen E v w) :
    coboundary (a v) = coboundary (a w) := by
  induction hpath with
  | refl => rfl
  | @tail w u _ hwu ih =>
    obtain ⟨e, he⟩ := hE w u hwu
    exact ih.trans (coboundary_eq_of_add_eq_coboundary he)

/-- A zero anchor and the edge identity imply that every cochain joined to
the anchor is a cocycle on the full source complex. -/
theorem isCocycle_of_edgePath_to_zero {W : Type*} (E : W → W → Prop)
    (a : W → Cochain K (k + 1))
    (hE : ∀ v w, E v w → ∃ e : Cochain K k, a v + a w = coboundary e)
    {v anchor : W} (hpath : Relation.ReflTransGen E v anchor)
    (hanchor : a anchor = 0) : IsCocycle (a v) := by
  unfold IsCocycle
  rw [coboundary_eq_of_edgePath E a hE hpath, hanchor, coboundary_zero]

/-- Coning off the boundary of a chain of degree at least two produces a
cycle over `𝔽₂`. The cone is required only on the support of that boundary. -/
theorem boundary_add_cone_boundary_eq_zero {n : ℕ} (c : Chain K (n + 2)) (v : V)
    (hv : ∀ s ∈ (boundary (n + 1) c).support,
      (∀ w ∈ s.1.1, w < v) ∧ insert v s.1.1 ∈ K) :
    boundary (n + 1)
      (c + TauCeti.OrderedSimplicialChain.cone Coeff v (n + 1) (boundary (n + 1) c)) = 0 := by
  rw [map_add, TauCeti.OrderedSimplicialChain.boundary_cone_succ hv,
    boundary_boundary, map_zero]
  simp only [show (-1 : Coeff) = 1 by decide, one_pow, one_smul, zero_add]
  ext s
  change boundary (n + 1) c s + boundary (n + 1) c s = 0
  exact (show ∀ x : Coeff, x + x = 0 by decide) _

end SharpTopologicalOverlap.Simplicial
