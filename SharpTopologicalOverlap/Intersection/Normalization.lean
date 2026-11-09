module

public import SharpTopologicalOverlap.Geometry.TargetCoverage
public import SharpTopologicalOverlap.Geometry.TargetGeometry.Boundary
public import SharpTopologicalOverlap.Intersection.TargetPlacement
public import SharpTopologicalOverlap.Intersection.BarycentricCochains

/-! # Normalization of the actual intersection cochains

Generic avoidance puts every source vertex image in exactly one actual
top target cell. Outer carriers miss the enclosing simplex's interior.
The constructed target cycle has coefficient one on all top cells, so
the sum of the degree-zero intersection cochains is the constant one.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open AbstractSimplicialComplex Set
open SharpTopologicalOverlap.Simplicial
open TargetGeometry

variable {n d j : ℕ}

/-- Generic placement places each fine source vertex image lying in the
enclosing interior in exactly one top target carrier, including all outer
cells in the uniqueness statement. -/
theorem unique_top_incidence_of_generic_vertex
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d) (r : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d r)) y)
    (v : (sourceBarycentricModel n d j).Vertex)
    (hv : y v ∈ interior (convexHull ℝ (Set.range D.points))) :
    ∃! τ : Cell (TargetCycle.model d r).complex d,
      y v ∈ targetCells D (TargetCycle.model d r) τ.1.1 := by
  classical
  let M := sourceBarycentricModel n d j
  let N := TargetCycle.model d r
  have hsource : ({v} : Finset M.Vertex) ∈ M.faceFamily :=
    (M.mem_faceFamily _).mpr (M.complex.singleton_mem v)
  have hlower : ∀ ρ : TauCeti.SetLike.Face N.complex,
      ρ.1.card ≤ d → InPatch N ρ.1 → y v ∉ targetCells D N ρ.1 := by
    intro ρ hcard hp hmem
    let β : PatchFace N := ⟨ρ, hp⟩
    have hpos : 0 < ρ.1.card := Finset.card_pos.mpr
      (N.complex.isRelLowerSet_faces.prop_of_mem ρ.2)
    have hdim : ({v} : Finset M.Vertex).card - 1 + β.1.1.card - 1 < d := by
      simp only [Finset.card_singleton, Nat.sub_self, Nat.zero_add]
      change ρ.1.card - 1 < d
      omega
    have havoid := hy.avoidance {v} hsource β (by
      simp only [Finset.card_singleton, Nat.sub_self, Nat.zero_add]
      change ρ.1.card - 1 < d
      omega)
    rw [targetSimplexFamily_range] at havoid
    apply Set.disjoint_left.mp havoid
    · exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, rfl⟩
    · simpa only [targetCells_eq_hull_of_inPatch D N hp] using hmem
  obtain ⟨τ, hτ, huniq⟩ := TargetCoverage.existsUnique_top_targetCells D r (y v)
    (interior_subset hv) hlower
  refine ⟨τ, hτ.2, fun σ hσ => ?_⟩
  have hσpatch : InPatch N σ.1.1 := by
    by_contra hnot
    exact Set.disjoint_left.mp (targetCells_disjoint_interior_of_not_inPatch D N σ.1 hnot) hσ hv
  exact huniq σ ⟨hσpatch, hσ⟩

/-- The same unique incidence for the images of the original coordinate
source vertices, using the actual source refinement map. -/
theorem unique_original_vertex_top_incidence
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d) (r : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d r)) y)
    (hinside : Set.range (barycentricSourceMap (sourceBarycentricModel n d j) y) ⊆
      interior (convexHull ℝ (Set.range D.points))) :
    ∀ v : Fin n, ∃! τ : Cell (TargetCycle.model d r).complex d,
      barycentricSourceMap (sourceBarycentricModel n d j) y
        (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
          (skeletonComplex (Fin n) d) v)) ∈
            barycentricTargetCells D (TargetCycle.model d r) d τ := by
  intro v
  let q := originalVertex (skeletonComplex (Fin n) d) j v
  have hq : y q ∈ interior (convexHull ℝ (Set.range D.points)) := by
    rw [← barycentricSourceMap_original_vertex j y v]
    exact hinside ⟨_, rfl⟩
  have h := unique_top_incidence_of_generic_vertex D r y hy q hq
  simpa only [barycentricSourceMap_original_vertex, barycentricTargetCells] using h

/-- Lemma 3.1(c) for the actual target sphere cycle and actual barycentric
intersection cochains constructed from the generic source placement. -/
theorem barycentric_family_normalization
    (j r : ℕ) (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d r)) y)
    (hinside : Set.range (barycentricSourceMap (sourceBarycentricModel n d j) y) ⊆
      interior (convexHull ℝ (Set.range D.points))) :
    ∑ τ : Cell (TargetCycle.model d r).complex d,
      TargetCycle.refinedCycle d r τ •
        barycentricCochainFamily j y (barycentricTargetCells D (TargetCycle.model d r))
          d 0 (Nat.add_zero d) τ =
      oneCochain (⊤ : AbstractSimplicialComplex (Fin n)) :=
  barycentricCochainFamily_target_normalization j r y _
    (unique_original_vertex_top_incidence D r y hy hinside)

end SharpTopologicalOverlap.Geometry
