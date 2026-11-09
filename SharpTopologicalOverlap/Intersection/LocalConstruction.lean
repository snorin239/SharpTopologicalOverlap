module

public import SharpTopologicalOverlap.Intersection.BarycentricCochains
public import SharpTopologicalOverlap.Intersection.TargetPlacement
public import SharpTopologicalOverlap.Geometry.TargetGeometry.Boundary

/-! # The actual local intersection identity on every target cell

Generic placement gives parity on the distinguished target patch. The filtered
carriers of outer target cells and all their subfaces lie outside the interior
of the enclosing simplex, where the constructed source map takes values.
Their indicators vanish. This proves the identity on the entire target sphere
and propagates the full-simplex vertex cocycle equation from infinity.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open SharpTopologicalOverlap.Simplicial SharpTopologicalOverlap.Geometry
open AbstractSimplicialComplex Set

variable {n d : ℕ}

private theorem fineInterpolation_range_subset
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d)) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hsource : Set.range (barycentricSourceMap M y) ⊆ C) :
    Set.range (Geometry.interpolate M.complex y) ⊆ C := by
  rintro z ⟨x, rfl⟩
  apply hsource
  refine ⟨skeletonRealizationHomeomorph d (M.homeomorph x), ?_⟩
  simp only [barycentricSourceMap, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact M.interpolation_map y x

/-- The fine indicator identity on all target cells, including the outer
cells where each term vanishes by the genuine enclosing-simplex geometry. -/
theorem barycentric_local_facet_identity (j jt : ℕ)
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d jt)) y)
    (hinside : Set.range (barycentricSourceMap (sourceBarycentricModel n d j) y) ⊆
      interior (convexHull ℝ (Set.range D.points))) :
    ∀ p q (_hpq : (p + 1) + q = d) (τ : Cell (TargetCycle.model d jt).complex (p + 1)),
      coboundary (localIndicator y (barycentricTargetCells D (TargetCycle.model d jt) (p + 1) τ) :
        Cochain (sourceBarycentricModel n d j).complex q) =
          ∑ i : Fin (p + 2),
            (localIndicator y (barycentricTargetCells D (TargetCycle.model d jt) p (τ.face i)) :
              Cochain (sourceBarycentricModel n d j).complex (q + 1)) := by
  intro p q hpq τ
  let N := TargetCycle.model d jt
  let M := sourceBarycentricModel n d j
  by_cases hτ : TargetGeometry.InPatch N τ.1.1
  · have hBτ : barycentricTargetCells D N (p + 1) τ =
        convexHull ℝ (TargetGeometry.position D N '' (τ.1.1 : Set N.Vertex)) :=
      TargetGeometry.targetCells_eq_hull_of_inPatch D N hτ
    have hBface (i : Fin (p + 2)) : barycentricTargetCells D N p (τ.face i) =
        convexHull ℝ (TargetGeometry.position D N '' ((τ.face i).1.1 : Set N.Vertex)) :=
      TargetGeometry.targetCells_eq_hull_of_inPatch D N (hτ.mono (τ.face_val_subset i))
    funext u
    rw [hBτ]
    rw [localIndicator_coboundary_of_generic D N y hy hpq u τ hτ]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hBface i]
  · have hraw := fineInterpolation_range_subset M y hinside
    have hmiss : Disjoint (interior (convexHull ℝ (Set.range D.points)))
        (barycentricTargetCells D N (p + 1) τ) :=
      (TargetGeometry.targetCells_disjoint_interior_of_not_inPatch D N τ.1 hτ).symm
    have hzero : (localIndicator y (barycentricTargetCells D N (p + 1) τ) :
        Cochain M.complex q) = 0 :=
      localIndicator_eq_zero_of_range_subset y _ _ hraw hmiss
    have hfacezero (i : Fin (p + 2)) :
        (localIndicator y (barycentricTargetCells D N p (τ.face i)) :
          Cochain M.complex (q + 1)) = 0 :=
      localIndicator_eq_zero_of_range_subset y _ _ hraw
        (hmiss.mono Set.Subset.rfl
          (barycentricTargetCells_mono D N p (p + 1) (τ.face i) τ (τ.face_val_subset i)))
    rw [hzero, coboundary_zero]
    symm
    exact Finset.sum_eq_zero (fun i _ => hfacezero i)

/-- Lemma 3.1(a) for the actual constructed barycentric cochain family. -/
theorem barycentric_family_facet_coboundary (j jt : ℕ)
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d jt)) y)
    (hinside : Set.range (barycentricSourceMap (sourceBarycentricModel n d j) y) ⊆
      interior (convexHull ℝ (Set.range D.points))) :
    ∀ p q (hpq : (p + 1) + q = d) (τ : Cell (TargetCycle.model d jt).complex (p + 1)),
      coboundary (barycentricCochainFamily j y (barycentricTargetCells D (TargetCycle.model d jt))
        (p + 1) q hpq τ) =
          ∑ i : Fin (p + 2),
            barycentricCochainFamily j y (barycentricTargetCells D (TargetCycle.model d jt))
              p (q + 1) (by omega) (τ.face i) :=
  barycentricCochainFamily_facet_coboundary j y _
    (barycentric_local_facet_identity j jt D y hy hinside)

/-- The zero cochain at the actual target vertex at infinity. -/
theorem barycentric_family_anchor_zero (j jt : ℕ)
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d)) :
    barycentricCochainFamily j y (barycentricTargetCells D (TargetCycle.model d jt))
      0 d (Nat.zero_add d)
        (RealizationCell.vertex (TargetCycle.model d jt).complex (TargetCycle.refinedInfinity d jt)) = 0 := by
  apply barycentricCochainFamily_eq_zero_of_empty
  simpa only [barycentricTargetCells, RealizationCell.vertex_val] using
    TargetGeometry.targetCells_refinedInfinity_eq_empty D jt

/-- Lemma 3.1(b), including the full source degree `d + 1`, follows from
the actual target paths and the zero anchor. -/
theorem barycentric_family_vertex_cocycle (hd : 0 < d) (j jt : ℕ)
    (D : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) d)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (hy : GenericPlacement (sourceBarycentricModel n d j).faceFamily
      (targetSimplexFamily D (TargetCycle.model d jt)) y)
    (hinside : Set.range (barycentricSourceMap (sourceBarycentricModel n d j) y) ⊆
      interior (convexHull ℝ (Set.range D.points))) :
    ∀ v : Cell (TargetCycle.model d jt).complex 0,
      IsCocycle (barycentricCochainFamily j y (barycentricTargetCells D (TargetCycle.model d jt))
        0 d (Nat.zero_add d) v) :=
  vertex_cocycles_of_facet_identity hd _
    (barycentric_family_facet_coboundary j jt D y hy hinside)
    (TargetCycle.refinedInfinity d jt) (barycentric_family_anchor_zero j jt D y)
    (TargetCycle.refined_path_to_infinity (Nat.succ_le_of_lt hd) jt)

end SharpTopologicalOverlap
