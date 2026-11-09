module

public import SharpTopologicalOverlap.Intersection
import Mathlib.Tactic.FinCases

/-! # Vertex cocycles from the actual target edge paths

The facet identity on edges propagates the full-simplex cocycle equation from
the zero vertex at infinity. In particular this proves the degree `d + 1`
equation without extending the map beyond the source `d`-skeleton.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial

variable {W : Type} [LinearOrder W] {T : AbstractSimplicialComplex W}

/-- The ordinary adjacency relation on target vertices. -/
def TargetEdge (T : AbstractSimplicialComplex W) (v w : W) : Prop :=
  v ≠ w ∧ ({v, w} : Finset W) ∈ T

theorem exists_edge_with_facets {v w : W} (hvw : TargetEdge T v w) :
    ∃ τ : Cell T 1,
      (τ.face 0 = AbstractSimplicialComplex.RealizationCell.vertex T v ∧
        τ.face 1 = AbstractSimplicialComplex.RealizationCell.vertex T w) ∨
      (τ.face 0 = AbstractSimplicialComplex.RealizationCell.vertex T w ∧
        τ.face 1 = AbstractSimplicialComplex.RealizationCell.vertex T v) := by
  classical
  let τ : Cell T 1 := ⟨⟨{v, w}, hvw.2⟩, Finset.card_pair hvw.1⟩
  obtain ⟨i, hi⟩ := (τ.exists_face_eq_iff_subset
    (AbstractSimplicialComplex.RealizationCell.vertex T v)).mpr (by simp [τ])
  obtain ⟨j, hj⟩ := (τ.exists_face_eq_iff_subset
    (AbstractSimplicialComplex.RealizationCell.vertex T w)).mpr (by simp [τ])
  have hij : i ≠ j := by
    intro h
    subst j
    have hv := congrArg (fun c : Cell T 0 => c.1.1) (hi.symm.trans hj)
    simp only [AbstractSimplicialComplex.RealizationCell.vertex_val] at hv
    exact hvw.1 (Finset.singleton_injective hv)
  refine ⟨τ, ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr ⟨hj, hi⟩
  · exact (hij rfl).elim

theorem sum_edge_facets {A : Type*} [AddCommMonoid A]
    (a : Cell T 0 → A) {v w : W} (hvw : TargetEdge T v w) :
    ∃ τ : Cell T 1,
      (∑ i : Fin 2, a (τ.face i)) =
        a (AbstractSimplicialComplex.RealizationCell.vertex T v) +
          a (AbstractSimplicialComplex.RealizationCell.vertex T w) := by
  obtain ⟨τ, h | h⟩ := exists_edge_with_facets hvw
  · exact ⟨τ, by simp [Fin.sum_univ_two, h.1, h.2]⟩
  · exact ⟨τ, by simp [Fin.sum_univ_two, h.1, h.2, add_comm]⟩

variable {n d : ℕ}

/-- The actual target edge paths and zero anchor discharge Lemma 3.1(b) from
its already proved facet identity. -/
theorem vertex_cocycles_of_facet_identity (hd : 0 < d)
    (a : IntersectionCochainFamily T n d)
    (hfacet : ∀ p q (hpq : (p + 1) + q = d) (τ : Cell T (p + 1)),
      coboundary (a (p + 1) q hpq τ) =
        ∑ j : Fin (p + 2), a p (q + 1) (by omega) (τ.face j))
    (anchor : W) (hanchor : a 0 d (Nat.zero_add d)
      (AbstractSimplicialComplex.RealizationCell.vertex T anchor) = 0)
    (hpath : ∀ v, Relation.ReflTransGen (TargetEdge T) v anchor) :
    ∀ v : Cell T 0, IsCocycle (a 0 d (Nat.zero_add d) v) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  let av : W → Cochain (⊤ : AbstractSimplicialComplex (Fin n)) (k + 1) :=
    fun v => a 0 (k + 1) (Nat.zero_add _) (AbstractSimplicialComplex.RealizationCell.vertex T v)
  have hedge : ∀ v w, TargetEdge T v w →
      ∃ e : Cochain (⊤ : AbstractSimplicialComplex (Fin n)) k,
        av v + av w = coboundary e := by
    intro v w hvw
    obtain ⟨τ, hsum⟩ := sum_edge_facets (a 0 (k + 1) (Nat.zero_add _)) hvw
    refine ⟨a 1 k (by omega) τ, ?_⟩
    exact hsum.symm.trans (hfacet 0 k (by omega) τ).symm
  intro v
  rw [v.eq_vertex]
  exact isCocycle_of_edgePath_to_zero (TargetEdge T) av hedge
    (hpath (v.vertexEmbedding 0)) hanchor

end SharpTopologicalOverlap
