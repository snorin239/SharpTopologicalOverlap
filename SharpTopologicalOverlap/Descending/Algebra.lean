module

public import SharpTopologicalOverlap.Descending.Incidence
public import SharpTopologicalOverlap.Intersection

/-! # The descending evaluation contradiction

This module isolates the finite algebra of §6.3 from the construction of
the singular fillings and the supported comparison. Its input chains have
the exact complementary source degrees, including degree `d+1` at target
vertices. The final theorem must still construct these inputs.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Descending

open Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}

abbrev SourceChain (n k : ℕ) := Chain (⊤ : AbstractSimplicialComplex (Fin n)) k

/-- Evaluation is also linear in its cochain argument. -/
def evaluateChain {V : Type*} {K : AbstractSimplicialComplex V} {k : ℕ} (c : Chain K k) :
    Cochain K k →ₗ[Coeff] Coeff where
  toFun a := evaluation a c
  map_add' a b := evaluation_add_cochain a b c
  map_smul' r a := by simpa only [smul_eq_mul, RingHom.id_apply] using evaluation_smul_cochain r a c

/-- The chains produced by the descending fillings after applying `ρ`.
This is an explicit input interface, not an existence assertion. -/
structure SimplicialDescent (I : IntersectionData T f) (x : Fin n) where
  z : ∀ p q : ℕ, p + q = d → Cell T p → SourceChain n q
  c : ∀ p q : ℕ, p + q = d → Cell T p → SourceChain n (q + 1)
  top : ∀ τ : Cell T d,
    z d 0 (Nat.add_zero d) τ = I.zeta τ •
      Finsupp.single (AbstractSimplicialComplex.RealizationCell.vertex
        (⊤ : AbstractSimplicialComplex (Fin n)) x) 1
  descend : ∀ p q (h : (p + 1) + q = d) (σ : Cell T p),
    z p (q + 1) (by omega) σ = cofaceSum (c (p + 1) q h) σ
  filling_eval : ∀ p q (h : p + q = d) (τ : Cell T p),
    evaluation (I.cochain p q h τ) (z p q h τ) =
      evaluation (coboundary (I.cochain p q h τ)) (c p q h τ)

namespace SimplicialDescent

variable {I : IntersectionData T f} {x : Fin n} (D : SimplicialDescent I x)

def levelEvaluation (p q : ℕ) (h : p + q = d) : Coeff :=
  ∑ τ : Cell T p, evaluation (I.cochain p q h τ) (D.z p q h τ)

theorem levelEvaluation_step (p q : ℕ) (h : (p + 1) + q = d) :
    D.levelEvaluation (p + 1) q h = D.levelEvaluation p (q + 1) (by omega) := by
  classical
  unfold levelEvaluation
  calc
    (∑ τ : Cell T (p + 1), evaluation (I.cochain (p + 1) q h τ) (D.z (p + 1) q h τ)) =
        ∑ τ : Cell T (p + 1), evaluation (coboundary (I.cochain (p + 1) q h τ))
          (D.c (p + 1) q h τ) := by
      exact Finset.sum_congr rfl (fun τ _ => D.filling_eval _ _ _ τ)
    _ = ∑ τ : Cell T (p + 1), ∑ j : Fin (p + 2),
        evaluation (I.cochain p (q + 1) (by omega) (τ.face j)) (D.c (p + 1) q h τ) := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [I.facet_coboundary p q h τ]
      exact map_sum (evaluateChain (D.c (p + 1) q h τ)) _ _
    _ = ∑ σ : Cell T p, evaluation (I.cochain p (q + 1) (by omega) σ)
        (cofaceSum (D.c (p + 1) q h) σ) :=
      (sum_pairing_coface (fun σ => evaluation (I.cochain p (q + 1) (by omega) σ)) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [D.descend p q h σ]

theorem levelEvaluation_bottom : D.levelEvaluation 0 d (Nat.zero_add d) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v _
  rw [D.filling_eval, I.vertex_cocycle, evaluation_zero_cochain]

theorem levelEvaluation_eq_zero (p q : ℕ) (h : p + q = d) : D.levelEvaluation p q h = 0 := by
  induction p generalizing q with
  | zero =>
    have hq : q = d := by omega
    subst q
    exact D.levelEvaluation_bottom
  | succ p ih =>
    exact (D.levelEvaluation_step p q h).trans (ih (q + 1) (by omega))

theorem levelEvaluation_top : D.levelEvaluation d 0 (Nat.add_zero d) = 1 := by
  classical
  unfold levelEvaluation
  simp_rw [D.top]
  have h := congrFun I.normalization
    (AbstractSimplicialComplex.RealizationCell.vertex
      (⊤ : AbstractSimplicialComplex (Fin n)) x)
  simpa only [map_smul, evaluation_single, one_mul, Finset.sum_apply,
    Pi.smul_apply, oneCochain_apply] using h

include D in
/-- The algebraic contradiction at the end of §6.3. -/
theorem false : False := by
  have hzero := D.levelEvaluation_eq_zero d 0 (Nat.add_zero d)
  rw [D.levelEvaluation_top] at hzero
  exact one_ne_zero hzero

end SimplicialDescent

end SharpTopologicalOverlap.Descending
