module

public import SharpTopologicalOverlap.Intersection.Algebra
public import SharpTopologicalOverlap.Overlap

/-! # The interface of Lemma 3.1

This file records all five conclusions of the intersection-cochain lemma and
their immediate consequences. It does not assert existence of the data: the
geometric construction of Appendix A must supply every field.

The two complementary degrees are explicit, with an equation `p + q = d`.
This avoids natural-number subtraction transports in the facet identity.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}

/-- The source cochains indexed by complementary target and source degrees. -/
abbrev IntersectionCochainFamily (T : AbstractSimplicialComplex W) (n d : ℕ) :=
  ∀ p q : ℕ, p + q = d → Cell T p → Cochain (⊤ : AbstractSimplicialComplex (Fin n)) q

/-- The source `d`-faces containing a supported face of a cochain indexed by
any subface of the target face. These are the families `P_τ` in Section 6. -/
def upwardSupport (a : IntersectionCochainFamily T n d) {p : ℕ} (τ : Cell T p) :
    Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powersetCard (d + 1)).filter fun σ =>
    ∃ (r q : ℕ) (h : r + q = d) (η : Cell T r), η.1.1 ⊆ τ.1.1 ∧
      ∃ σ' ∈ supportFamily (a r q h η), σ' ⊆ σ

omit [Fintype W] [LinearOrder W] in
@[simp] theorem mem_upwardSupport (a : IntersectionCochainFamily T n d)
    {p : ℕ} (τ : Cell T p) (σ : Finset (Fin n)) :
    σ ∈ upwardSupport a τ ↔ σ.card = d + 1 ∧
      ∃ (r q : ℕ) (h : r + q = d) (η : Cell T r), η.1.1 ⊆ τ.1.1 ∧
        ∃ σ' ∈ supportFamily (a r q h η), σ' ⊆ σ := by
  classical
  simp [upwardSupport]

omit [Fintype W] [LinearOrder W] in
theorem upwardSupport_uniform (a : IntersectionCochainFamily T n d)
    {p : ℕ} (τ : Cell T p) : IsUniform (d + 1) (upwardSupport a τ) :=
  fun σ hσ => ((mem_upwardSupport a τ σ).mp hσ).1

omit [Fintype W] [LinearOrder W] in
theorem upwardSupport_mono (a : IntersectionCochainFamily T n d)
    {p r : ℕ} {τ : Cell T p} {η : Cell T r} (hητ : η.1.1 ⊆ τ.1.1) :
    upwardSupport a η ⊆ upwardSupport a τ := by
  intro σ hσ
  obtain ⟨hcard, s, q, h, ξ, hξη, σ', hσ', hsub⟩ := (mem_upwardSupport a η σ).mp hσ
  exact (mem_upwardSupport a τ σ).mpr
    ⟨hcard, s, q, h, ξ, hξη.trans hητ, σ', hσ', hsub⟩

/-- The complete conclusion of Lemma 3.1 for a specified finite target complex.
No proof field here is an existence hypothesis for the geometry: constructing
an instance requires proving all of them. -/
structure IntersectionData (T : AbstractSimplicialComplex W)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) where
  /-- The target has dimension at most `d`; normalization below supplies a `d`-cell. -/
  dimension_le : ∀ p, Cell T p → p ≤ d
  /-- The target fundamental cycle. -/
  zeta : Chain T d
  /-- The unaugmented cycle identity in every applicable successor degree. -/
  cycle : ∀ k (h : d = k + 1), boundary k (h ▸ zeta) = 0
  /-- Source cochains in the complementary degree. -/
  cochain : IntersectionCochainFamily T n d
  /-- Lemma 3.1(a), including every positive target degree. -/
  facet_coboundary : ∀ p q (h : (p + 1) + q = d) (τ : Cell T (p + 1)),
    coboundary (cochain (p + 1) q h τ) =
      ∑ j : Fin (p + 2), cochain p (q + 1) (by omega) (τ.face j)
  /-- Lemma 3.1(b), on the full source simplex, including degree `d + 1`. -/
  vertex_cocycle : ∀ v : Cell T 0,
    IsCocycle (cochain 0 d (Nat.zero_add d) v)
  /-- Lemma 3.1(c). Scalar multiplication includes the coefficients of the cycle. -/
  normalization :
    ∑ τ : Cell T d, zeta τ • cochain d 0 (Nat.add_zero d) τ =
      oneCochain (⊤ : AbstractSimplicialComplex (Fin n))
  /-- Lemma 3.1(d), simultaneously over all supported subfaces. -/
  common_point : ∀ p (τ : Cell T p), ∃ y : EuclideanSpace ℝ (Fin d),
    ∀ σ ∈ upwardSupport cochain τ, y ∈ f '' skeletonFace d σ
  /-- Lemma 3.1(e), in the equivalent bound on every disjoint subfamily. -/
  matching_bound : ∀ p q (h : p + q = d) (τ : Cell T p), 0 < p →
    ∀ A : Finset (Finset (Fin n)), A ⊆ supportFamily (cochain p q h τ) →
      (∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ') → A.card ≤ d / p

namespace IntersectionData

variable {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}
  (I : IntersectionData T f)

/-- The support families used in Section 6 have cardinality bounded by the
overlap of the original continuous map. -/
theorem upwardSupport_card_le_overlap {p : ℕ} (τ : Cell T p) :
    (upwardSupport I.cochain τ).card ≤ overlap f :=
  card_le_overlap_of_exists_common_point f _
    (upwardSupport_uniform I.cochain τ) (I.common_point p τ)

/-- When the source has a vertex, normalization forces a nonzero top-cycle
coefficient. In particular the target dimension is exactly `d`. -/
theorem exists_top_cell (hn : 0 < n) : ∃ τ : Cell T d, I.zeta τ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : ∑ τ : Cell T d, I.zeta τ • I.cochain d 0 (Nat.add_zero d) τ = 0 := by
    apply Finset.sum_eq_zero
    intro τ _
    rw [h τ, zero_smul]
  have hnorm := I.normalization
  rw [hz] at hnorm
  have hval := congrFun hnorm
    (AbstractSimplicialComplex.RealizationCell.vertex
      (⊤ : AbstractSimplicialComplex (Fin n)) ⟨0, hn⟩)
  exact zero_ne_one (by simpa only [Pi.zero_apply, oneCochain_apply] using hval)

end IntersectionData

end SharpTopologicalOverlap
