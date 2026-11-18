module

public import SharpTopologicalOverlap.Intersection.LocalConstruction
public import SharpTopologicalOverlap.Intersection.Normalization
public import SharpTopologicalOverlap.Geometry.EnclosingSimplex
public import SharpTopologicalOverlap.Geometry.TargetGeometry.Mesh

/-! # Existence of the intersection cochains: Lemma 3.1

All complexes, refinements, placements, chains and local intersection counts
are constructed from the given continuous map. The five properties are proved
on the actual ordered chain modules and the full source cochain complex.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open SharpTopologicalOverlap.Simplicial SharpTopologicalOverlap.Geometry
  AbstractSimplicialComplex Set

variable {n d : ℕ}

/-- The finite target, its genuine dimension, and all five properties of
Lemma 3.1, with a vertex type constructed by the proof. -/
structure IntersectionWitness
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) where
  Vertex : Type
  vertexFintype : Fintype Vertex
  vertexLinearOrder : LinearOrder Vertex
  complex : AbstractSimplicialComplex Vertex
  data : letI := vertexFintype
         letI := vertexLinearOrder
         IntersectionData complex f
  topCell : Cell complex d

attribute [instance] IntersectionWitness.vertexFintype IntersectionWitness.vertexLinearOrder

/-- Lemma 3.1: every continuous map in the stated dimension and size range
has a finite `d`-dimensional target cycle and all five intersection-cochain
properties. No geometric construction is left as a premise. -/
theorem exists_intersectionData (hd : 0 < d) (hn : d + 1 ≤ n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))) :
    Nonempty (IntersectionWitness f) := by
  classical
  obtain ⟨εf, hεf, htransfer⟩ := exists_faceImage_perturbation_tolerance f
  obtain ⟨j, yg, hgc, hgnear, _hgFine, hgOriginal⟩ :=
    exists_first_source_approximation f f.continuous hεf
  let M := sourceBarycentricModel n d j
  let g : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)) :=
    ⟨barycentricSourceMap M yg, hgc⟩
  have hgf : ∀ x, dist (g x) (f x) < εf := by
    intro x
    change dist (barycentricSourceMap M yg x) (f x) < εf
    rw [dist_eq_norm]
    exact hgnear x
  have hgStrong : StrongGeneralPosition g :=
    (sourceStrongGeneralPosition_iff _).mp hgOriginal
  obtain ⟨εg, hεg, hcluster⟩ := exists_faceImage_cluster_tolerance g
  obtain ⟨D, hD⟩ := exists_enclosing_simplex_cthickening (isCompact_range g.continuous) εg
  obtain ⟨r, hmesh⟩ := TargetGeometry.exists_targetCells_mesh_lt D hεg
  let N := TargetCycle.model d r
  obtain ⟨yh, hyGeneric, _hhc, hhnear⟩ :=
    exists_second_source_approximation j yg (targetSimplexFamily D N) hεg
  let h := barycentricSourceMap M yh
  have hhg : ∀ x, dist (h x) (g x) < εg := by
    intro x
    change dist (barycentricSourceMap M yh x) (barycentricSourceMap M yg x) < εg
    rw [dist_eq_norm]
    exact hhnear x
  have hinside : Set.range h ⊆ interior (convexHull ℝ (Set.range D.points)) :=
    range_subset_of_near_cthickening g h hhnear hD
  let B := barycentricTargetCells D N
  let a := barycentricCochainFamily j yh B
  have ha : SupportMeets a h B := barycentricCochainFamily_supportMeets j yh B
  have hmono : ∀ p t (η : Cell N.complex p) (τ : Cell N.complex t),
      η.1.1 ⊆ τ.1.1 → B p η ⊆ B t τ := barycentricTargetCells_mono D N
  have hsmall : ∀ p (τ : Cell N.complex p),
      ∀ x ∈ B p τ, ∀ y ∈ B p τ, dist x y < εg := by
    intro p τ x hx y hy
    exact hmesh τ.1.1 τ.1.2 x hx y hy
  have hcommon : ∀ p (τ : Cell N.complex p), ∃ z,
      ∀ σ ∈ upwardSupport a τ, z ∈ f '' skeletonFace d σ := by
    intro p τ
    apply htransfer g hgf
    exact hcluster h hhg (upwardSupport a τ) (B p τ) (hsmall p τ)
      (ha.upwardSupport hmono τ)
  have hmatching : ∀ p q (hpq : p + q = d) (τ : Cell N.complex p), 0 < p →
      ∀ A : Finset (Finset (Fin n)), A ⊆ supportFamily (a p q hpq τ) →
        (∀ σ ∈ A, ∀ σ' ∈ A, σ ≠ σ' → Disjoint σ σ') → A.card ≤ d / p := by
    intro p q hpq τ hp A hA hdis
    apply card_le_div_of_strongGeneralPosition hgStrong hpq hp A
      (fun σ hσ => supportFamily_uniform (a p q hpq τ) σ (hA hσ)) hdis
    exact hcluster h hhg A (B p τ) (hsmall p τ) (ha.subfamily hpq τ A hA)
  let I : IntersectionData N.complex f := {
    dimension_le := TargetCycle.refined_dimension_le d r
    zeta := TargetCycle.refinedCycle d r
    cycle := by
      intro k hdk
      cases hdk
      exact TargetCycle.boundary_refinedCycle k r
    cochain := a
    facet_coboundary := barycentric_family_facet_coboundary j r D yh hyGeneric hinside
    vertex_cocycle := barycentric_family_vertex_cocycle hd
      j r D yh hyGeneric hinside
    normalization := barycentric_family_normalization j r D yh hyGeneric hinside
    common_point := hcommon
    matching_bound := hmatching }
  have hnpos : 0 < n := by omega
  obtain ⟨τ, _hτ⟩ := I.exists_top_cell hnpos
  exact ⟨{
    Vertex := N.Vertex
    vertexFintype := N.vertexFintype
    vertexLinearOrder := N.vertexLinearOrder
    complex := N.complex
    data := I
    topCell := τ }⟩

end SharpTopologicalOverlap
