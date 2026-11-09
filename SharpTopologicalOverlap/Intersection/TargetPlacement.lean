module

public import SharpTopologicalOverlap.Geometry.TargetGeometry
public import SharpTopologicalOverlap.Geometry.SourceApproximation
public import SharpTopologicalOverlap.Intersection.LocalParity
public import SharpTopologicalOverlap.Intersection.Support
public import SharpTopologicalOverlap.Geometry.GenericPlacements

/-! # Applying the generic placement theorem to the actual target patch -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open AbstractSimplicialComplex Set
open SharpTopologicalOverlap.Simplicial
open TargetGeometry

variable {d : ℕ}

/-- The globally monotone geometric target carriers, including outer faces. -/
def barycentricTargetCells
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (M : BarycentricModel (sphere d)) : TargetCells M.complex d :=
  fun _ τ => targetCells D M τ.1.1

theorem barycentricTargetCells_mono
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (M : BarycentricModel (sphere d))
    (p r : ℕ) (η : Cell M.complex p) (τ : Cell M.complex r) (h : η.1.1 ⊆ τ.1.1) :
    barycentricTargetCells D M p η ⊆ barycentricTargetCells D M r τ :=
  targetCells_mono D M h

/-- All actual nonempty fine target faces in the distinguished simplex. -/
abbrev PatchFace (M : BarycentricModel (sphere d)) :=
  {σ : TauCeti.SetLike.Face M.complex // InPatch M σ.1}

instance patchFaceFintype (M : BarycentricModel (sphere d)) : Fintype (PatchFace M) :=
  Fintype.ofFinite _

def patchCell (M : BarycentricModel (sphere d)) (σ : PatchFace M) :
    Cell M.complex (σ.1.1.card - 1) :=
  ⟨σ.1, (Nat.sub_add_cancel (Finset.card_pos.mpr
    (M.complex.isRelLowerSet_faces.prop_of_mem σ.1.2))).symm⟩

/-- The actual Euclidean simplex associated with each target patch face. -/
def targetSimplexFamily (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (M : BarycentricModel (sphere d)) (σ : PatchFace M) :
    Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (σ.1.1.card - 1) :=
  ⟨position D M ∘ (patchCell M σ).vertexEmbedding,
    placed_cell_affineIndependent (position D M) (patchCell M σ)
      (patch_cell_affineIndependent D M σ.1 σ.2)⟩

theorem targetSimplexFamily_range
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (M : BarycentricModel (sphere d)) (σ : PatchFace M) :
    Set.range (targetSimplexFamily D M σ).points =
      position D M '' (σ.1.1 : Set M.Vertex) :=
  range_placed_vertices (position D M) (patchCell M σ)

/-- Generic placement against every actual target patch face discharges the
geometric G3/G4 hypotheses on each complementary source/target cell pair. -/
theorem localIndicator_coboundary_of_generic
    {n j : ℕ} (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (N : BarycentricModel (sphere d))
    (y : (barycentricModel (skeletonComplex (Fin n) d) j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement
      (barycentricModel (skeletonComplex (Fin n) d) j).faceFamily (targetSimplexFamily D N) y)
    {p q : ℕ} (hpq : (p + 1) + q = d)
    (u : Cell (barycentricModel (skeletonComplex (Fin n) d) j).complex (q + 1))
    (τ : Cell N.complex (p + 1)) (hτ : InPatch N τ.1.1) :
    coboundary (localIndicator y (convexHull ℝ (position D N '' (τ.1.1 : Set N.Vertex)))) u =
      ∑ i : Fin (p + 2),
        localIndicator y (convexHull ℝ (position D N '' ((τ.face i).1.1 : Set N.Vertex))) u := by
  classical
  let M := barycentricModel (skeletonComplex (Fin n) d) j
  have hAface {A : Finset M.Vertex} (hA : A ⊆ u.1.1) (hne : A.Nonempty) : A ∈ M.faceFamily :=
    M.mem_faceFamily A |>.mpr (M.complex.isRelLowerSet_faces.mem_of_le u.1.2 hA hne)
  have hBface {B : Finset N.Vertex} (hB : B ⊆ τ.1.1) (hne : B.Nonempty) : B ∈ N.complex :=
    N.complex.isRelLowerSet_faces.mem_of_le τ.1.2 hB hne
  have hyu := placed_cell_affineIndependent y u
    (hy.independent u.1.1 ((M.mem_faceFamily u.1.1).mpr u.1.2))
  have hzτ := placed_cell_affineIndependent (position D N) τ
    (patch_cell_affineIndependent D N τ.1 hτ)
  apply localIndicator_coboundary u τ y (position D N) hyu hzτ (by
    rw [finrank_euclideanSpace_fin]
    omega)
  · intro A B hA hB hcard
    by_cases hAne : A.Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp hAne]
    by_cases hBne : B.Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp hBne]
    let β : PatchFace N := ⟨⟨B, hBface hB hBne⟩, hτ.mono hB⟩
    have hdim : A.card - 1 + (B.card - 1) < d := by
      rw [finrank_euclideanSpace_fin] at hcard
      have := hAne.card_pos
      have := hBne.card_pos
      omega
    have h := hy.avoidance A (hAface hA hAne) β (by
      change A.card - 1 + (B.card - 1) < d
      exact hdim)
    simpa only [targetSimplexFamily_range] using h
  · intro A B hA hB hcard
    have hAne : A.Nonempty := by
      apply Finset.card_pos.mp
      have hBcard := Finset.card_le_card hB
      rw [τ.2] at hBcard
      rw [finrank_euclideanSpace_fin] at hcard
      omega
    have hBne : B.Nonempty := by
      apply Finset.card_pos.mp
      have hAcard := Finset.card_le_card hA
      rw [u.2] at hAcard
      rw [finrank_euclideanSpace_fin] at hcard
      omega
    let β : PatchFace N := ⟨⟨B, hBface hB hBne⟩, hτ.mono hB⟩
    have h := hy.affineDirections_span (hAface hA hAne) β (by
      change d ≤ A.card - 1 + (B.card - 1)
      rw [finrank_euclideanSpace_fin] at hcard
      have := hAne.card_pos
      have := hBne.card_pos
      omega)
    simpa only [targetSimplexFamily_range] using h

end SharpTopologicalOverlap.Geometry
