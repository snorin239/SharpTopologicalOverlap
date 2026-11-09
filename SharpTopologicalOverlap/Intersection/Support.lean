module

public import SharpTopologicalOverlap.Intersection
public import SharpTopologicalOverlap.Intersection.Matching
public import SharpTopologicalOverlap.Geometry.Stability

/-! # Support transfer in the intersection construction

Local incidence with small target cells gives both the common-point property
and the exact disjoint-support bound. The two compactness tolerances are chosen
in the manuscript's order, after the first approximation has been fixed.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}

/-- The subsets of the geometric target associated with its abstract faces. -/
abbrev TargetCells (T : AbstractSimplicialComplex W) (d : ℕ) :=
  ∀ p : ℕ, Cell T p → Set (EuclideanSpace ℝ (Fin d))

/-- Local source supports have an actual incidence with the target cell. -/
def SupportMeets (a : IntersectionCochainFamily T n d)
    (h : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)) (B : TargetCells T d) : Prop :=
  ∀ p q (hpq : p + q = d) (τ : Cell T p), ∀ σ ∈ supportFamily (a p q hpq τ),
    (h '' skeletonFace d σ ∩ B p τ).Nonempty

theorem skeletonFace_mono {V : Type*} {σ τ : Finset V} (hστ : σ ⊆ τ) :
    skeletonFace d σ ⊆ skeletonFace d τ := fun _ hx => hx.trans hστ

omit [Fintype W] [LinearOrder W] in
/-- Incidences for supported subfaces control the whole upward support family
appearing in Lemma 3.1(d). -/
theorem SupportMeets.upwardSupport
    {a : IntersectionCochainFamily T n d}
    {h : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)} {B : TargetCells T d}
    (ha : SupportMeets a h B)
    (hB : ∀ p r (η : Cell T p) (τ : Cell T r), η.1.1 ⊆ τ.1.1 → B p η ⊆ B r τ)
    {p : ℕ} (τ : Cell T p) :
    ∀ σ ∈ upwardSupport a τ, (h '' skeletonFace d σ ∩ B p τ).Nonempty := by
  intro σ hσ
  obtain ⟨_, r, q, hrq, η, hητ, σ', hσ', hσσ'⟩ := (mem_upwardSupport a τ σ).mp hσ
  obtain ⟨y, ⟨x, hx, hxy⟩, hyB⟩ := ha r q hrq η σ' hσ'
  exact ⟨y, ⟨x, skeletonFace_mono hσσ' hx, hxy⟩, hB r p η τ hητ hyB⟩

omit [Fintype W] [LinearOrder W] in
/-- Restrict a support incidence to any subfamily of that support. -/
theorem SupportMeets.subfamily
    {a : IntersectionCochainFamily T n d}
    {h : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)} {B : TargetCells T d}
    (ha : SupportMeets a h B) {p q : ℕ} (hpq : p + q = d) (τ : Cell T p)
    (A : Finset (Finset (Fin n))) (hA : A ⊆ supportFamily (a p q hpq τ)) :
    ∀ σ ∈ A, (h '' skeletonFace d σ ∩ B p τ).Nonempty :=
  fun σ hσ => ha p q hpq τ σ (hA hσ)

omit [Fintype W] [LinearOrder W] in
/-- The compactness tolerances provide both conclusions needed downstream:
common image points for all upward supports, and matching bounds for all
disjoint support subfamilies. The remaining input is genuine local incidence. -/
theorem exists_support_transfer_tolerances
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    ∃ εf : ℝ, 0 < εf ∧ ∀ g : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
      (∀ x, dist (g x) (f x) < εf) → StrongGeneralPosition g →
      ∃ εg : ℝ, 0 < εg ∧
        ∀ (h : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d))
          (B : TargetCells T d),
          (∀ x, dist (h x) (g x) < εg) →
          (∀ p (τ : Cell T p), ∀ y ∈ B p τ, ∀ z ∈ B p τ, dist y z < εg) →
          (∀ p r (η : Cell T p) (τ : Cell T r), η.1.1 ⊆ τ.1.1 → B p η ⊆ B r τ) →
          ∀ a : IntersectionCochainFamily T n d, SupportMeets a h B →
            (∀ p (τ : Cell T p), ∃ y, ∀ σ ∈ upwardSupport a τ,
              y ∈ f '' skeletonFace d σ) ∧
            (∀ p q (hpq : p + q = d) (τ : Cell T p), 0 < p →
              ∀ A : Finset (Finset (Fin n)), A ⊆ supportFamily (a p q hpq τ) →
                (∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ') → A.card ≤ d / p) := by
  obtain ⟨εf, hεf, htransfer⟩ := exists_faceImage_perturbation_tolerance f
  refine ⟨εf, hεf, fun g hgf hg => ?_⟩
  obtain ⟨εg, hεg, hcluster⟩ := exists_faceImage_cluster_tolerance g
  refine ⟨εg, hεg, fun h B hhg hsmall hmono a ha => ⟨?_, ?_⟩⟩
  · intro p τ
    apply htransfer g hgf
    exact hcluster h hhg (upwardSupport a τ) (B p τ) (hsmall p τ)
      (ha.upwardSupport hmono τ)
  · intro p q hpq τ hp A hA hdisj
    apply card_le_div_of_strongGeneralPosition hg hpq hp A
      (fun σ hσ => supportFamily_uniform (a p q hpq τ) σ (hA hσ)) hdisj
    exact hcluster h hhg A (B p τ) (hsmall p τ) (ha.subfamily hpq τ A hA)

end SharpTopologicalOverlap
