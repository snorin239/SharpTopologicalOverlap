module

public import SharpTopologicalOverlap.Simplicial
public import SharpTopologicalOverlap.Skeleton
import Mathlib.Tactic.Linarith

/-! # Strong general position bounds disjoint support families

This is the final argument for Lemma 3.1(e). It only uses strong general
position of the first approximation `g` and a common point in the `g`-images;
the geometric construction separately establishes these hypotheses.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial

variable {V Y : Type*} {d : ℕ}

/-- The strong general-position condition on the images of disjoint original
source faces, called (A2) in Appendix A. -/
def StrongGeneralPosition (g : Skeleton V d → Y) : Prop :=
  ∀ A : Finset (Finset V),
    (∀ σ ∈ A, σ.Nonempty ∧ σ.card ≤ d + 1) →
    (∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ') →
    2 ≤ A.card → (∑ σ ∈ A, (σ.card - 1)) < d * (A.card - 1) →
    ¬∃ y : Y, ∀ σ ∈ A, y ∈ g '' skeletonFace d σ

/-- If `s` disjoint `q`-faces have a common image point and `p + q = d`,
strong general position forces `s * p ≤ d`, including `s = 0, 1`. -/
theorem card_mul_le_of_strongGeneralPosition {g : Skeleton V d → Y}
    (hg : StrongGeneralPosition g) {p q : ℕ} (hpq : p + q = d)
    (A : Finset (Finset V)) (hA : IsUniform (q + 1) A)
    (hdisj : ∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ')
    (hcommon : ∃ y : Y, ∀ σ ∈ A, y ∈ g '' skeletonFace d σ) :
    A.card * p ≤ d := by
  classical
  by_contra hbad
  have hbad' : d < A.card * p := Nat.lt_of_not_ge hbad
  have hp : p ≤ d := by omega
  have hs : 2 ≤ A.card := by
    by_contra hsmall
    have hsmall' : A.card ≤ 1 := by omega
    have hmul := Nat.mul_le_mul_right p hsmall'
    simp only [one_mul] at hmul
    omega
  have hsum : (∑ σ ∈ A, (σ.card - 1)) = A.card * q := by
    apply Finset.sum_const_nat
    intro σ hσ
    rw [hA σ hσ]
    omega
  have hdecomp : A.card * p + A.card * q = A.card * d := by
    rw [← Nat.mul_add, hpq]
  have hpred : (A.card - 1) + 1 = A.card := Nat.sub_add_cancel (by omega)
  have hpredmul : d * (A.card - 1) + d = d * A.card := by
    calc
      d * (A.card - 1) + d = d * ((A.card - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = d * A.card := by rw [hpred]
  have hdim : (∑ σ ∈ A, (σ.card - 1)) < d * (A.card - 1) := by
    rw [hsum]
    nlinarith [Nat.mul_comm d A.card]
  apply hg A ?_ hdisj hs hdim hcommon
  intro σ hσ
  have hcard := hA σ hσ
  exact ⟨Finset.card_pos.mp (by omega), by omega⟩

/-- The arithmetic form of the matching bound in Lemma 3.1(e). -/
theorem card_le_div_of_strongGeneralPosition {g : Skeleton V d → Y}
    (hg : StrongGeneralPosition g) {p q : ℕ} (hpq : p + q = d) (hp : 0 < p)
    (A : Finset (Finset V)) (hA : IsUniform (q + 1) A)
    (hdisj : ∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ')
    (hcommon : ∃ y : Y, ∀ σ ∈ A, y ∈ g '' skeletonFace d σ) :
    A.card ≤ d / p :=
  (Nat.le_div_iff_mul_le hp).mpr
    (card_mul_le_of_strongGeneralPosition hg hpq A hA hdisj hcommon)

end SharpTopologicalOverlap
