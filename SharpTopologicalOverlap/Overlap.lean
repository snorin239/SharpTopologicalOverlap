module

public import SharpTopologicalOverlap.Skeleton
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.ContinuousMap.Basic

/-! # Overlap of a map on the realized skeleton

Overlap counts source faces, so coincident images are counted separately.
The maximum exists because the integer-valued count is bounded by a binomial
coefficient; no maximum principle on the target space is needed.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

variable {V Y : Type*} [Fintype V] [TopologicalSpace Y] {d : ℕ}

theorem isCompact_faceImage (f : C(Skeleton V d, Y)) (σ : Finset V) :
    IsCompact (f '' skeletonFace d σ) :=
  (isCompact_skeletonFace d σ).image f.continuous

/-- The source `d`-faces whose closed images contain a query point. -/
def facesAt (f : C(Skeleton V d, Y)) (y : Y) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powersetCard (d + 1)).filter
    (fun σ => y ∈ f '' skeletonFace d σ)

@[simp] theorem mem_facesAt (f : C(Skeleton V d, Y)) (y : Y) (σ : Finset V) :
    σ ∈ facesAt f y ↔ σ.card = d + 1 ∧ y ∈ f '' skeletonFace d σ := by
  classical
  simp [facesAt]

/-- The number of closed source `d`-face images containing a query point. -/
def overlapCount (f : C(Skeleton V d, Y)) (y : Y) : ℕ := (facesAt f y).card

theorem overlapCount_le_choose (f : C(Skeleton V d, Y)) (y : Y) :
    overlapCount f y ≤ (Fintype.card V).choose (d + 1) := by
  classical
  have h := Finset.card_le_card
    (Finset.filter_subset (fun σ => y ∈ f '' skeletonFace d σ)
      (Finset.univ.powersetCard (d + 1)))
  simpa [overlapCount, facesAt] using h

theorem bddAbove_range_overlapCount (f : C(Skeleton V d, Y)) :
    BddAbove (Set.range (overlapCount f)) := by
  refine ⟨(Fintype.card V).choose (d + 1), ?_⟩
  rintro _ ⟨y, rfl⟩
  exact overlapCount_le_choose f y

theorem finite_range_overlapCount (f : C(Skeleton V d, Y)) :
    (Set.range (overlapCount f)).Finite := by
  apply (Set.finite_le_nat ((Fintype.card V).choose (d + 1))).subset
  rintro _ ⟨y, rfl⟩
  exact overlapCount_le_choose f y

/-- The largest number of source `d`-faces with a common point in their closed images. -/
def overlap (f : C(Skeleton V d, Y)) : ℕ := sSup (Set.range (overlapCount f))

theorem overlapCount_le_overlap (f : C(Skeleton V d, Y)) (y : Y) :
    overlapCount f y ≤ overlap f :=
  le_csSup (bddAbove_range_overlapCount f) (Set.mem_range_self y)

theorem overlap_attained [Nonempty Y] (f : C(Skeleton V d, Y)) :
    ∃ y, overlapCount f y = overlap f :=
  Nat.sSup_mem (Set.range_nonempty _) (bddAbove_range_overlapCount f)

theorem overlap_le_choose [Nonempty Y] (f : C(Skeleton V d, Y)) :
    overlap f ≤ (Fintype.card V).choose (d + 1) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y, rfl⟩
  exact overlapCount_le_choose f y

/-- Any uniform family with one common image point has size at most the overlap. -/
theorem card_le_overlap_of_common_point (f : C(Skeleton V d, Y))
    (A : Finset (Finset V)) (hA : ∀ σ ∈ A, σ.card = d + 1)
    (y : Y) (hy : ∀ σ ∈ A, y ∈ f '' skeletonFace d σ) :
    A.card ≤ overlap f := by
  apply (Finset.card_le_card (show A ⊆ facesAt f y from ?_)).trans
    (overlapCount_le_overlap f y)
  intro σ hσ
  exact (mem_facesAt f y σ).mpr ⟨hA σ hσ, hy σ hσ⟩

theorem card_le_overlap_of_exists_common_point (f : C(Skeleton V d, Y))
    (A : Finset (Finset V)) (hA : ∀ σ ∈ A, σ.card = d + 1)
    (hcommon : ∃ y : Y, ∀ σ ∈ A, y ∈ f '' skeletonFace d σ) :
    A.card ≤ overlap f := by
  obtain ⟨y, hy⟩ := hcommon
  exact card_le_overlap_of_common_point f A hA y hy

end SharpTopologicalOverlap
