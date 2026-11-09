module

public import SharpTopologicalOverlap.Overlap
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Stability of common intersections of finitely many compact images

The compact separation argument preceding Step 1 of Appendix A.  One positive
tolerance works for every subfamily of a fixed finite family of compact sets.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open scoped BigOperators

variable {ι Y : Type*} [Fintype ι] [MetricSpace Y] [Nonempty Y]

/-- A finite family of compact sets has a positive tolerance such that pairwise
close representatives can exist only when the sets have a common point. -/
theorem exists_compact_family_separation (K : ι → Set Y)
    (hK : ∀ i, IsCompact (K i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ι → Y, (∀ i, y i ∈ K i) →
      (∀ i j, dist (y i) (y j) < ε) → ∃ z, ∀ i, z ∈ K i := by
  classical
  by_cases hcommon : ∃ z, ∀ i, z ∈ K i
  · exact ⟨1, zero_lt_one, fun _ _ _ => hcommon⟩
  by_cases hprod : ∃ y : ι → Y, ∀ i, y i ∈ K i
  swap
  · exact ⟨1, zero_lt_one, fun y hy _ => (hprod ⟨y, hy⟩).elim⟩
  have hι : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    exact hcommon ⟨Classical.arbitrary Y, fun i => isEmptyElim i⟩
  let F : (ι → Y) → ℝ := fun y => ∑ i, ∑ j, dist (y i) (y j)
  have hFnonneg (y : ι → Y) : 0 ≤ F y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  have hFpos (y : ι → Y) (hy : ∀ i, y i ∈ K i) : 0 < F y := by
    apply lt_of_le_of_ne (hFnonneg y)
    intro hzero
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
        Finset.sum_nonneg fun j _ => dist_nonneg)).mp hzero.symm
    let i₀ : ι := Classical.choice hι
    apply hcommon
    refine ⟨y i₀, fun i => ?_⟩
    have hrow := hrows i₀ (Finset.mem_univ _)
    have hpair := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) => dist_nonneg)).mp hrow
    have heq : y i₀ = y i := dist_eq_zero.mp (hpair i (Finset.mem_univ _))
    exact heq ▸ hy i
  have hFcont : Continuous F := by dsimp [F]; fun_prop
  have hcompact : IsCompact (Set.univ.pi K) := isCompact_univ_pi hK
  have hprod' : (Set.univ.pi K).Nonempty := by
    obtain ⟨y, hy⟩ := hprod
    exact ⟨y, fun i _ => hy i⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hcompact.exists_isMinOn hprod' hFcont.continuousOn
  have hy₀' : ∀ i, y₀ i ∈ K i := by simpa [Set.pi] using hy₀
  have hpos := hFpos y₀ hy₀'
  let N : ℝ := Fintype.card ι
  let ε := F y₀ / (N ^ 2 + 1)
  have hden : 0 < N ^ 2 + 1 := by positivity
  refine ⟨ε, div_pos hpos hden, fun y hy hclose => ?_⟩
  have hy' : y ∈ Set.univ.pi K := by simpa [Set.pi] using hy
  have hbound : F y ≤ N ^ 2 * ε := by
    calc
      F y ≤ ∑ _i : ι, ∑ _j : ι, ε :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hclose i j).le
      _ = N ^ 2 * ε := by simp [N, pow_two, mul_assoc]
  have hstrict : N ^ 2 * ε < F y₀ := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  exact (not_lt_of_ge (hmin hy') (hbound.trans_lt hstrict)).elim

/-- The tolerance can be chosen simultaneously for every subfamily, including
the empty subfamily. -/
theorem exists_compact_subfamily_separation (K : ι → Set Y)
    (hK : ∀ i, IsCompact (K i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : Finset ι) (y : S → Y),
      (∀ i : S, y i ∈ K i) → (∀ i j, dist (y i) (y j) < ε) →
      ∃ z, ∀ i ∈ S, z ∈ K i := by
  classical
  have hex (S : Finset ι) := exists_compact_family_separation
    (fun i : S => K i) (fun i => hK i)
  choose ε hε hsep using hex
  let values : Finset ℝ := Finset.univ.image ε
  have hvalues : values.Nonempty := Finset.univ_nonempty.image ε
  refine ⟨values.min' hvalues, ?_, fun S y hy hclose => ?_⟩
  · exact (Finset.lt_min'_iff _ _).mpr (by simpa [values] using hε)
  · have hle : values.min' hvalues ≤ ε S :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩)
    obtain ⟨z, hz⟩ := hsep S y hy (fun i j => (hclose i j).trans_le hle)
    exact ⟨z, fun i hi => hz ⟨i, hi⟩⟩

/-- The single tolerance `ε(f)` from Appendix A, for the original closed source
faces of a map on the skeleton. -/
theorem exists_faceImage_separation {V : Type*} [Fintype V] {d : ℕ}
    (f : C(Skeleton V d, Y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (A : Finset (Finset V)) (y : A → Y),
      (∀ σ : A, y σ ∈ f '' skeletonFace d σ) →
      (∀ σ τ, dist (y σ) (y τ) < ε) →
      ∃ z, ∀ σ ∈ A, z ∈ f '' skeletonFace d σ :=
  exists_compact_subfamily_separation (fun σ => f '' skeletonFace d σ)
    (isCompact_faceImage f)

/-- Sufficiently small uniform perturbations preserve common intersections of
original face images in the direction needed in Appendix A, property (A1). -/
theorem exists_faceImage_perturbation_tolerance {V : Type*} [Fintype V] {d : ℕ}
    (f : C(Skeleton V d, Y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Skeleton V d → Y,
      (∀ x, dist (g x) (f x) < ε) → ∀ A : Finset (Finset V),
      (∃ z, ∀ σ ∈ A, z ∈ g '' skeletonFace d σ) →
      ∃ z, ∀ σ ∈ A, z ∈ f '' skeletonFace d σ := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := exists_faceImage_separation f
  refine ⟨δ / 2, half_pos hδ, fun g hnear A hcommon => ?_⟩
  obtain ⟨z, hz⟩ := hcommon
  choose x hx hxz using fun σ : A => hz σ σ.prop
  apply hsep A (fun σ => f (x σ)) (fun σ => ⟨x σ, hx σ, rfl⟩)
  intro σ τ
  calc
    dist (f (x σ)) (f (x τ)) ≤ dist (f (x σ)) z + dist z (f (x τ)) :=
      dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
      apply add_lt_add
      · simpa only [← hxz σ, dist_comm] using hnear (x σ)
      · simpa only [← hxz τ] using hnear (x τ)
    _ = δ := add_halves δ

/-- The second perturbation estimate in Appendix A: if all perturbed face
images meet one sufficiently small target set, their original images have a
common point. The target set need not itself be a simplex. -/
theorem exists_faceImage_cluster_tolerance {V : Type*} [Fintype V] {d : ℕ}
    (f : C(Skeleton V d, Y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Skeleton V d → Y,
      (∀ x, dist (g x) (f x) < ε) → ∀ (A : Finset (Finset V)) (B : Set Y),
      (∀ y ∈ B, ∀ z ∈ B, dist y z < ε) →
      (∀ σ ∈ A, (g '' skeletonFace d σ ∩ B).Nonempty) →
      ∃ z, ∀ σ ∈ A, z ∈ f '' skeletonFace d σ := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := exists_faceImage_separation f
  refine ⟨δ / 3, by positivity, fun g hnear A B hsmall hmeet => ?_⟩
  choose y hy using fun σ : A => hmeet σ σ.prop
  choose x hx hxy using fun σ : A => (hy σ).1
  apply hsep A (fun σ => f (x σ)) (fun σ => ⟨x σ, hx σ, rfl⟩)
  intro σ τ
  calc
    dist (f (x σ)) (f (x τ)) ≤
        dist (f (x σ)) (y σ) + dist (y σ) (y τ) + dist (y τ) (f (x τ)) :=
      dist_triangle4 _ _ _ _
    _ < δ / 3 + δ / 3 + δ / 3 := by
      apply add_lt_add
      · apply add_lt_add
        · simpa only [← hxy σ, dist_comm] using hnear (x σ)
        · exact hsmall _ (hy σ).2 _ (hy τ).2
      · simpa only [← hxy τ] using hnear (x τ)
    _ = δ := by ring

/-- Tolerances can be chosen in the order used in the construction: first for
`f`, then for a continuous first approximation `g`, and finally for an arbitrary
second approximation `h`. A family meeting a small target set has a common
`g`-image point and therefore a common `f`-image point. -/
theorem exists_faceImage_two_stage_tolerances {V : Type*} [Fintype V] {d : ℕ}
    (f : C(Skeleton V d, Y)) :
    ∃ εf : ℝ, 0 < εf ∧ ∀ g : C(Skeleton V d, Y),
      (∀ x, dist (g x) (f x) < εf) →
      ∃ εg : ℝ, 0 < εg ∧ ∀ h : Skeleton V d → Y,
        (∀ x, dist (h x) (g x) < εg) → ∀ (A : Finset (Finset V)) (B : Set Y),
        (∀ y ∈ B, ∀ z ∈ B, dist y z < εg) →
        (∀ σ ∈ A, (h '' skeletonFace d σ ∩ B).Nonempty) →
        ∃ z, ∀ σ ∈ A, z ∈ f '' skeletonFace d σ := by
  obtain ⟨εf, hεf, htransfer⟩ := exists_faceImage_perturbation_tolerance f
  refine ⟨εf, hεf, fun g hnear => ?_⟩
  obtain ⟨εg, hεg, hcluster⟩ := exists_faceImage_cluster_tolerance g
  exact ⟨εg, hεg, fun h hnear' A B hsmall hmeet =>
    htransfer g hnear A (hcluster h hnear' A B hsmall hmeet)⟩

end SharpTopologicalOverlap
