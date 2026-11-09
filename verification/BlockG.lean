module

import SharpTopologicalOverlap.Geometry.BarycentricApproximation
import SharpTopologicalOverlap.Geometry.BarycentricBridge
import SharpTopologicalOverlap.Geometry.BarycentricGeometry
import SharpTopologicalOverlap.Geometry.BarycentricModel
import SharpTopologicalOverlap.Geometry.ConstraintParity
import SharpTopologicalOverlap.Geometry.EnclosingSimplex
import SharpTopologicalOverlap.Geometry.FaceInterpolation
import SharpTopologicalOverlap.Geometry.GeneralPosition
import SharpTopologicalOverlap.Geometry.GenericPlacements
import SharpTopologicalOverlap.Geometry.Intersections
import SharpTopologicalOverlap.Geometry.PlacementAvoidance
import SharpTopologicalOverlap.Geometry.Placements
import SharpTopologicalOverlap.Geometry.Segments
import SharpTopologicalOverlap.Geometry.SimplexParity
import SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates
import SharpTopologicalOverlap.Geometry.SimplexParity.Line
import SharpTopologicalOverlap.Geometry.SourceApproximation
import SharpTopologicalOverlap.Geometry.Stability
import SharpTopologicalOverlap.Geometry.StrongGeneralPosition
import SharpTopologicalOverlap.Geometry.Subdivision
import SharpTopologicalOverlap.Geometry.TargetCoverage
import SharpTopologicalOverlap.Geometry.TargetCycle
import SharpTopologicalOverlap.Geometry.TargetGeometry
import SharpTopologicalOverlap.Geometry.TargetGeometry.Boundary
import SharpTopologicalOverlap.Geometry.TargetGeometry.Mesh
import SharpTopologicalOverlap.Geometry.TransversePlacements
import SharpTopologicalOverlap.Intersection
import SharpTopologicalOverlap.Intersection.Algebra
import SharpTopologicalOverlap.Intersection.BarycentricCochains
import SharpTopologicalOverlap.Intersection.Construction
import SharpTopologicalOverlap.Intersection.Existence
import SharpTopologicalOverlap.Intersection.Indicators
import SharpTopologicalOverlap.Intersection.LocalConstruction
import SharpTopologicalOverlap.Intersection.LocalParity
import SharpTopologicalOverlap.Intersection.Matching
import SharpTopologicalOverlap.Intersection.Normalization
import SharpTopologicalOverlap.Intersection.Refinement
import SharpTopologicalOverlap.Intersection.Support
import SharpTopologicalOverlap.Intersection.TargetPlacement
import SharpTopologicalOverlap.Intersection.VertexCocycles

/-! Independent declaration and edge-case audit for the partial implementation
of block G. This module is checked separately and is not a root import. -/

open SharpTopologicalOverlap SharpTopologicalOverlap.Geometry

-- Empty indexing types and empty compact sets are accepted by separation.
example : ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin 0 → ℝ,
    (∀ i, y i ∈ (∅ : Set ℝ)) → (∀ i j, dist (y i) (y j) < ε) →
      ∃ z : ℝ, ∀ _i : Fin 0, z ∈ (∅ : Set ℝ) :=
  exists_compact_family_separation (fun _ : Fin 0 => (∅ : Set ℝ))
    (fun _ => isCompact_empty)

example : ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin 1 → ℝ,
    (∀ i, y i ∈ (∅ : Set ℝ)) → (∀ i j, dist (y i) (y j) < ε) →
      ∃ z : ℝ, ∀ _i : Fin 1, z ∈ (∅ : Set ℝ) :=
  exists_compact_family_separation (fun _ : Fin 1 => (∅ : Set ℝ))
    (fun _ => isCompact_empty)

-- Degenerate closed segments are deliberately included.
example : ∃ a ∈ ({0} : Set ℝ), ∃ b ∈ ({0} : Set ℝ),
    ({0} : Set ℝ) = segment ℝ a b :=
  exists_eq_segment_of_isCompact_convex_collinear isCompact_singleton
    (convex_singleton 0) (Set.singleton_nonempty 0) (collinear_singleton ℝ 0)

-- Strong general position in dimension zero has an impossible strict
-- dimension inequality. The matching theorem does not divide by zero.
example (g : Skeleton (Fin 1) 0 → ℝ) : StrongGeneralPosition g := by
  intro A _ _ _ hdim
  simp only [zero_mul, not_lt_zero] at hdim

example (g : Skeleton (Fin 1) 0 → ℝ) (hg : StrongGeneralPosition g) :
    (∅ : Finset (Finset (Fin 1))).card * 0 ≤ 0 := by
  exact card_mul_le_of_strongGeneralPosition hg (p := 0) (q := 0) rfl ∅
    (by simp [Simplicial.IsUniform]) (by simp) ⟨0, by simp⟩

-- Affine independence in dimension zero is required only on sets of size one.
example (y : Fin 2 → EuclideanSpace ℝ (Fin 0)) :
    ∃ z : Fin 2 → EuclideanSpace ℝ (Fin 0), (∀ i, ‖z i - y i‖ < (1 : ℝ)) ∧
      ∀ s : Finset (Fin 2), s.card ≤ 1 → AffineIndependent ℝ (fun i : s => z i) := by
  exact exists_generalPosition y zero_lt_one

-- A singleton source face satisfies G4 against the full target direction,
-- including in ambient dimension zero.
example (d : ℕ) (y : Fin 1 → EuclideanSpace ℝ (Fin d)) :
    ∃ z : Fin 1 → EuclideanSpace ℝ (Fin d), (∀ q, ‖z q - y q‖ < (1 : ℝ)) ∧
      (∀ q ∉ (Finset.univ : Finset (Fin 1)), z q = y q) ∧
      SpanningDirectionsOn (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) Finset.univ z := by
  exact exists_near_spanningDirectionsOn ⊤ Finset.univ (by simp) (by simp)
    y zero_lt_one

-- Axioms for all public theorem declarations in the audited source modules.

-- SharpTopologicalOverlap/Geometry/BarycentricApproximation.lean
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.coordinateMap_single
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_vertexPoint_val
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_coordinates_centroid
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_faceCardBound
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_dist_le_of_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_mesh
#print axioms SharpTopologicalOverlap.Geometry.barycentricModel_faceCardBound
#print axioms SharpTopologicalOverlap.Geometry.barycentricModel_mesh
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.continuous_interpolation
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.interpolation_map
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.interpolation_vertexPoint
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.norm_interpolation_sub_le
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.interpolation_linearMap
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.interpolation_mem_convexHull
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.continuous_facePoint
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.facePoint_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.interpolation_facePoint
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.linearMap_facePoint
#print axioms SharpTopologicalOverlap.Geometry.exists_barycentric_interpolation_approx
#print axioms SharpTopologicalOverlap.Geometry.exists_barycentric_vertex_image_mesh_lt
#print axioms SharpTopologicalOverlap.Geometry.exists_barycentric_hull_image_mesh_lt

-- SharpTopologicalOverlap/Geometry/BarycentricBridge.lean
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.affineMapMk_sourceVertices_eq_map
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.permutationFace_antitone
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.permutationFace_card
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.permutationFace_injective
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.affine_child_vertex_eq_subBarycenter
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.subBarycenter_weights_eq_faceBarycenter
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.affine_child_vertex_weights_eq_faceBarycenter
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.permutationPoint_val
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.barycentricRealization_permutationPoint
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.exists_permutation_of_mem_support_subdivision
#print axioms SharpTopologicalOverlap.Geometry.BarycentricBridge.fundamentalChain_one_child_represented

-- SharpTopologicalOverlap/Geometry/BarycentricGeometry.lean
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.support_subset_of_vertices
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.faceInclusion_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.cell_affineIndependent
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.card_le_of_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.full_face_mem_of_card
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.exists_max_face
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.exists_unique_parent_facet

-- SharpTopologicalOverlap/Geometry/BarycentricModel.lean
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_lt_of_card_lt
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.vertexPoint_val
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.linearMap_eq_vertexPoint
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.homeomorph_val_sum
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.active_vertex_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.homeomorph_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_vertexPoint_support_subset
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.exists_originalFace_carrier
#print axioms SharpTopologicalOverlap.Geometry.barycentricModel_zero
#print axioms SharpTopologicalOverlap.Geometry.barycentricModel_succ

-- SharpTopologicalOverlap/Geometry/ConstraintParity.lean
#print axioms SharpTopologicalOverlap.Geometry.mem_activeConstraints
#print axioms SharpTopologicalOverlap.Geometry.feasibleParameters_both_sides
#print axioms SharpTopologicalOverlap.Geometry.exists_distinct_feasibleParameter
#print axioms SharpTopologicalOverlap.Geometry.exists_active_of_isLeast
#print axioms SharpTopologicalOverlap.Geometry.exists_active_of_isGreatest
#print axioms SharpTopologicalOverlap.Geometry.feasibleParameters_eq_Icc
#print axioms SharpTopologicalOverlap.Geometry.activeParameter_eq_endpoint
#print axioms SharpTopologicalOverlap.Geometry.finite_affine_constraints_endpoints
#print axioms SharpTopologicalOverlap.Geometry.card_activeConstraints_eq_two
#print axioms SharpTopologicalOverlap.Geometry.activeConstraints_card_mod_two
#print axioms SharpTopologicalOverlap.Geometry.activeConstraints_eq_empty_of_empty
#print axioms SharpTopologicalOverlap.Geometry.card_activeConstraints_eq_zero_or_two
#print axioms SharpTopologicalOverlap.Geometry.sum_activeConstraint_indicators_eq_zero

-- SharpTopologicalOverlap/Geometry/EnclosingSimplex.lean
#print axioms SharpTopologicalOverlap.Geometry.exists_enclosing_affineBasis
#print axioms SharpTopologicalOverlap.Geometry.exists_enclosing_simplex
#print axioms SharpTopologicalOverlap.Geometry.exists_enclosing_simplex_cthickening

-- SharpTopologicalOverlap/Geometry/FaceInterpolation.lean
#print axioms SharpTopologicalOverlap.Geometry.interpolate_faceInclusion
#print axioms SharpTopologicalOverlap.Geometry.image_interpolate_faceInclusion
#print axioms SharpTopologicalOverlap.Geometry.hull_subset_original_face_image

-- SharpTopologicalOverlap/Geometry/GeneralPosition.lean
#print axioms SharpTopologicalOverlap.Geometry.dense_compl_affineSubspace
#print axioms SharpTopologicalOverlap.Geometry.dense_disjoint_affineSubspace_translations
#print axioms SharpTopologicalOverlap.Geometry.exists_small_disjoint_affineSubspace_translations
#print axioms SharpTopologicalOverlap.Geometry.exists_near_avoiding_affineSpans
#print axioms SharpTopologicalOverlap.Geometry.exists_generalPositionOn
#print axioms SharpTopologicalOverlap.Geometry.exists_generalPosition
#print axioms SharpTopologicalOverlap.Geometry.isOpen_generalPosition
#print axioms SharpTopologicalOverlap.Geometry.dense_generalPosition

-- SharpTopologicalOverlap/Geometry/GenericPlacements.lean
#print axioms SharpTopologicalOverlap.Geometry.GenericPlacement.source_injective
#print axioms SharpTopologicalOverlap.Geometry.GenericPlacement.affineDirections_span
#print axioms SharpTopologicalOverlap.Geometry.isOpen_independentOnFamily
#print axioms SharpTopologicalOverlap.Geometry.dense_independentOnFamily
#print axioms SharpTopologicalOverlap.Geometry.open_dense_avoidanceOn
#print axioms SharpTopologicalOverlap.Geometry.open_dense_spanningOn
#print axioms SharpTopologicalOverlap.Geometry.open_dense_genericPlacement
#print axioms SharpTopologicalOverlap.Geometry.exists_genericPlacement

-- SharpTopologicalOverlap/Geometry/Intersections.lean
#print axioms SharpTopologicalOverlap.Geometry.disjoint_of_sup_eq_top_of_finrank_add
#print axioms SharpTopologicalOverlap.Geometry.affineSpan_inter_eq_singleton
#print axioms SharpTopologicalOverlap.Geometry.convexHull_inter_subsingleton
#print axioms SharpTopologicalOverlap.Geometry.mem_intrinsicInterior_of_notMem_opposite_faces
#print axioms SharpTopologicalOverlap.Geometry.inter_subset_intrinsicInterior_inter

-- SharpTopologicalOverlap/Geometry/PlacementAvoidance.lean
#print axioms SharpTopologicalOverlap.Geometry.convexHull_range_eq_range_affineMapMk
#print axioms SharpTopologicalOverlap.Geometry.isOpen_hull_avoidance
#print axioms SharpTopologicalOverlap.Geometry.exists_near_hull_avoidance
#print axioms SharpTopologicalOverlap.Geometry.open_dense_hull_avoidance

-- SharpTopologicalOverlap/Geometry/Placements.lean
#print axioms SharpTopologicalOverlap.Geometry.interpolate_eq_sum
#print axioms SharpTopologicalOverlap.Geometry.continuous_interpolate
#print axioms SharpTopologicalOverlap.Geometry.interpolate_vertex
#print axioms SharpTopologicalOverlap.Geometry.interpolate_sub
#print axioms SharpTopologicalOverlap.Geometry.norm_interpolate_sub_le
#print axioms SharpTopologicalOverlap.Geometry.interpolate_mem_convexHull
#print axioms SharpTopologicalOverlap.Geometry.continuous_edgewiseInterpolate
#print axioms SharpTopologicalOverlap.Geometry.edgewiseInterpolate_map
#print axioms SharpTopologicalOverlap.Geometry.norm_edgewiseInterpolate_sub_le
#print axioms SharpTopologicalOverlap.Geometry.edgewise_active_vertex_entries_subset
#print axioms SharpTopologicalOverlap.Geometry.edgewiseInterpolate_mem_convexHull
#print axioms SharpTopologicalOverlap.Geometry.norm_edgewisePoint_sub_le
#print axioms SharpTopologicalOverlap.Geometry.exists_edgewiseInterpolate_approx

-- SharpTopologicalOverlap/Geometry/Segments.lean
#print axioms SharpTopologicalOverlap.Geometry.finrank_direction_inf_eq_one
#print axioms SharpTopologicalOverlap.Geometry.exists_eq_segment_of_isCompact_convex_collinear
#print axioms SharpTopologicalOverlap.Geometry.exists_eq_segment_of_isCompact_convex_subset_affineLine
#print axioms SharpTopologicalOverlap.Geometry.simplex_finrank_direction_inf_eq_one
#print axioms SharpTopologicalOverlap.Geometry.simplex_convexHull_inter_eq_segment
#print axioms SharpTopologicalOverlap.Geometry.exists_nonzero_strict_finite_affine_constraints

-- SharpTopologicalOverlap/Geometry/SimplexParity.lean
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.LowerFaceAvoidance.symm
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.FaceSpanning.symm
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.eq_of_two_zero_source_coordinates
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.false_of_zero_source_target_coordinates
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.source_coord_slope_ne_zero
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.facet_intersection_parity
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.erased_vertex_image_eq_range_succAbove
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.facet_intersection_parity_succAbove
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.source_facet_count_eq_target_facet_count

-- SharpTopologicalOverlap/Geometry/SimplexParity/Coordinates.lean
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.exists_coordinates
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.sum_coord
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.affineCombination_coord
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.coord_nonneg_of_mem_hull
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.coord_zero_of_mem_face_span
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.sum_face_coord
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.sum_face_coord_smul
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_face_span_iff
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_face_hull_iff
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_hull_iff
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_erased_face_hull_iff
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_erased_face_span_iff
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates.mem_double_erased_face_hull

-- SharpTopologicalOverlap/Geometry/SimplexParity/Line.lean
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.exists_line
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Line.point_mem
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Line.point_surjective
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Line.isClosedEmbedding_point
#print axioms SharpTopologicalOverlap.Geometry.SimplexParity.Line.coord_point

-- SharpTopologicalOverlap/Geometry/SourceApproximation.lean
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.mem_faceFamily
#print axioms SharpTopologicalOverlap.Geometry.continuous_barycentricSourceMap
#print axioms SharpTopologicalOverlap.Geometry.barycentricSourceMap_facePoint
#print axioms SharpTopologicalOverlap.Geometry.fine_hull_subset_sourceFace_image
#print axioms SharpTopologicalOverlap.Geometry.sourceStrongGeneralPosition_iff
#print axioms SharpTopologicalOverlap.Geometry.StrongGeneralPositionOn.no_common_hulls_indexed
#print axioms SharpTopologicalOverlap.Geometry.sourceStrong_of_modelStrong
#print axioms SharpTopologicalOverlap.Geometry.exists_first_source_approximation
#print axioms SharpTopologicalOverlap.Geometry.exists_second_source_approximation
#print axioms SharpTopologicalOverlap.Geometry.range_subset_of_near_cthickening

-- SharpTopologicalOverlap/Geometry/Stability.lean
#print axioms SharpTopologicalOverlap.exists_compact_family_separation
#print axioms SharpTopologicalOverlap.exists_compact_subfamily_separation
#print axioms SharpTopologicalOverlap.exists_faceImage_separation
#print axioms SharpTopologicalOverlap.exists_faceImage_perturbation_tolerance
#print axioms SharpTopologicalOverlap.exists_faceImage_cluster_tolerance
#print axioms SharpTopologicalOverlap.exists_faceImage_two_stage_tolerances

-- SharpTopologicalOverlap/Geometry/StrongGeneralPosition.lean
#print axioms SharpTopologicalOverlap.Geometry.dense_independent_affineSubspace_translations
#print axioms SharpTopologicalOverlap.Geometry.exists_small_independent_affineSubspace_translations
#print axioms SharpTopologicalOverlap.Geometry.translateDisjointFamily_on
#print axioms SharpTopologicalOverlap.Geometry.exists_perturb_disjoint_family_affineSpans
#print axioms SharpTopologicalOverlap.Geometry.isOpen_no_common_hulls
#print axioms SharpTopologicalOverlap.Geometry.mem_strongFamilies
#print axioms SharpTopologicalOverlap.Geometry.StrongGeneralPositionOn.no_common_hulls
#print axioms SharpTopologicalOverlap.Geometry.isOpen_admissibleStrongFamily
#print axioms SharpTopologicalOverlap.Geometry.dense_admissibleStrongFamily
#print axioms SharpTopologicalOverlap.Geometry.isOpen_strongGeneralPositionOn
#print axioms SharpTopologicalOverlap.Geometry.dense_strongGeneralPositionOn
#print axioms SharpTopologicalOverlap.Geometry.exists_strongGeneralPositionOn

-- SharpTopologicalOverlap/Geometry/Subdivision.lean
#print axioms SharpTopologicalOverlap.Geometry.subdivide_eq_pow
#print axioms SharpTopologicalOverlap.Geometry.subdivide_zero
#print axioms SharpTopologicalOverlap.Geometry.subdivide_succ
#print axioms SharpTopologicalOverlap.Geometry.boundary_subdivide
#print axioms SharpTopologicalOverlap.Geometry.subdivide_degree_zero
#print axioms SharpTopologicalOverlap.Geometry.affineMapMk_mem_closedFace
#print axioms SharpTopologicalOverlap.Geometry.subdivision_carried
#print axioms SharpTopologicalOverlap.Geometry.subdivide_carried
#print axioms SharpTopologicalOverlap.Geometry.subdivide_vertex_dist_le
#print axioms SharpTopologicalOverlap.Geometry.subdivide_dist_le
#print axioms SharpTopologicalOverlap.Geometry.exists_subdivide_dist_lt
#print axioms SharpTopologicalOverlap.Geometry.reduceModTwo_apply
#print axioms SharpTopologicalOverlap.Geometry.reduceModTwo_single
#print axioms SharpTopologicalOverlap.Geometry.reduceModTwo_surjective
#print axioms SharpTopologicalOverlap.Geometry.support_reduceModTwo_subset
#print axioms SharpTopologicalOverlap.Geometry.affineBoundary_single
#print axioms SharpTopologicalOverlap.Geometry.affineBoundary_reduceModTwo
#print axioms SharpTopologicalOverlap.Geometry.affineBoundary_affineBoundary_reduced
#print axioms SharpTopologicalOverlap.Geometry.affineBoundary_affineBoundary
#print axioms SharpTopologicalOverlap.Geometry.sourceVertices_face
#print axioms SharpTopologicalOverlap.Geometry.fundamentalChain_zero
#print axioms SharpTopologicalOverlap.Geometry.boundary_fundamentalChain
#print axioms SharpTopologicalOverlap.Geometry.fundamentalChain_degree_zero
#print axioms SharpTopologicalOverlap.Geometry.fundamentalChain_carried
#print axioms SharpTopologicalOverlap.Geometry.fundamentalChain_dist_le
#print axioms SharpTopologicalOverlap.Geometry.exists_fundamentalChain_dist_lt

-- SharpTopologicalOverlap/Geometry/TargetCoverage.lean
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.lift_hull_point
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.physical_mem_support_hull
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.lift_top_hull_point
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.sphere_face_card_bound
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.existsUnique_top_patch_cell
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.existsUnique_top_targetCells
#print axioms SharpTopologicalOverlap.Geometry.TargetCoverage.existsUnique_top_targetCells_of_cell_avoidance

-- SharpTopologicalOverlap/Geometry/TargetCycle.lean
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.include_facet
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.facet_injective
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.include_cycle
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.boundary_cycle
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.dimension_le
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.exists_facet
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.cycle_apply_facet
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.cycle_apply
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.edge_of_ne
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.path_to_infinity
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdivisionMap_single
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdividedCell_carried
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdividedBoundary_cone_admissible
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdivisionMap_boundary_single
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.boundary_subdivisionMap
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdividedCell_apply_of_carried
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdivisionMap_top_one
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.singletonVertex_val
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_path_of_nested
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_path_of_edge
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_lift_path
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.step_paths_to_anchor
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.subdivisionMap_support
#print axioms SharpTopologicalOverlap.Geometry.BarycentricModel.singletonVertex_point
#print axioms SharpTopologicalOverlap.Geometry.boundary_iteratedSubdivision
#print axioms SharpTopologicalOverlap.Geometry.originalVertex_point
#print axioms SharpTopologicalOverlap.Geometry.iteratedSubdivision_vertex
#print axioms SharpTopologicalOverlap.Geometry.iteratedSubdivision_carried
#print axioms SharpTopologicalOverlap.Geometry.iteratedSubdivision_facePoint_carried
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.sphere_faceCardBound
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.refined_dimension_le
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.refinedCycle_apply
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.boundary_refinedCycle
#print axioms SharpTopologicalOverlap.Geometry.TargetCycle.refined_path_to_infinity

-- SharpTopologicalOverlap/Geometry/TargetGeometry.lean
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.affineMap_eq_sum
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.position_eq_sum
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.InPatch.mono
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.last_eq_zero_of_support_subset_patch
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.sum_castSucc_eq_one
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.affineMap_injective_on_patch_vectors
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.position_mem_target_hull
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patch_cell_affineIndependent
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.continuous_targetMap
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patch_mem_sphere
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchPoint_castSucc
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchPoint_last
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchPoint_support_subset
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.affineMap_patchPoint
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.mem_patchVertices
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchVertices_subset
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchVertices_mono
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.patchVertices_eq_self
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_mono
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_eq_hull_of_inPatch
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_subset_full_hull
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.isCompact_targetCells

-- SharpTopologicalOverlap/Geometry/TargetGeometry/Boundary.lean
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.affineMap_mem_target_face
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_subset_target_face_of_not_inPatch
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.target_face_disjoint_interior
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_disjoint_interior_of_not_inPatch
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.refinedInfinity_point
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.targetCells_refinedInfinity_eq_empty

-- SharpTopologicalOverlap/Geometry/TargetGeometry/Mesh.lean
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.sphere_face_card_le
#print axioms SharpTopologicalOverlap.Geometry.TargetGeometry.exists_targetCells_mesh_lt

-- SharpTopologicalOverlap/Geometry/TransversePlacements.lean
#print axioms SharpTopologicalOverlap.Geometry.exists_near_spanning_modulo
#print axioms SharpTopologicalOverlap.Geometry.exists_near_spanningDirections
#print axioms SharpTopologicalOverlap.Geometry.dense_spanningDirections
#print axioms SharpTopologicalOverlap.Geometry.isOpen_finite_family_span_top
#print axioms SharpTopologicalOverlap.Geometry.isOpen_finite_family_span_sup
#print axioms SharpTopologicalOverlap.Geometry.isOpen_spanningDirections
#print axioms SharpTopologicalOverlap.Geometry.vectorSpan_range_fin_succ
#print axioms SharpTopologicalOverlap.Geometry.exists_near_spanningDirectionsOn
#print axioms SharpTopologicalOverlap.Geometry.isOpen_spanningDirectionsOn
#print axioms SharpTopologicalOverlap.Geometry.dense_spanningDirectionsOn

-- SharpTopologicalOverlap/Intersection.lean
#print axioms SharpTopologicalOverlap.mem_upwardSupport
#print axioms SharpTopologicalOverlap.upwardSupport_uniform
#print axioms SharpTopologicalOverlap.upwardSupport_mono
#print axioms SharpTopologicalOverlap.IntersectionData.upwardSupport_card_le_overlap
#print axioms SharpTopologicalOverlap.IntersectionData.exists_top_cell

-- SharpTopologicalOverlap/Intersection/Algebra.lean
#print axioms SharpTopologicalOverlap.Simplicial.coboundary_eq_of_add_eq_coboundary
#print axioms SharpTopologicalOverlap.Simplicial.coboundary_eq_of_edgePath
#print axioms SharpTopologicalOverlap.Simplicial.isCocycle_of_edgePath_to_zero
#print axioms SharpTopologicalOverlap.Simplicial.boundary_add_cone_boundary_eq_zero

-- SharpTopologicalOverlap/Intersection/BarycentricCochains.lean
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_eq_zero_of_empty
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_supportMeets
#print axioms SharpTopologicalOverlap.barycentricSourceMap_original_vertex
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_vertex
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_vertex_map
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_facet_coboundary
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_normalization
#print axioms SharpTopologicalOverlap.barycentricCochainFamily_target_normalization

-- SharpTopologicalOverlap/Intersection/Construction.lean
#print axioms SharpTopologicalOverlap.Geometry.affineEvaluation_single
#print axioms SharpTopologicalOverlap.Geometry.affineEvaluation_coboundary
#print axioms SharpTopologicalOverlap.Geometry.coboundary_intersectionCochain
#print axioms SharpTopologicalOverlap.Geometry.coboundary_intersectionCochain_of_local_identity
#print axioms SharpTopologicalOverlap.Geometry.exists_supported_child_of_intersectionCochain_ne_zero
#print axioms SharpTopologicalOverlap.Geometry.intersectionCochain_degree_zero
#print axioms SharpTopologicalOverlap.Geometry.sum_intersectionCochain_degree_zero
#print axioms SharpTopologicalOverlap.Geometry.sum_intersectionCochain_degree_zero_of_unique
#print axioms SharpTopologicalOverlap.Geometry.facet_coboundary_intersectionCochainFamily

-- SharpTopologicalOverlap/Intersection/Existence.lean
#print axioms SharpTopologicalOverlap.exists_intersectionData

-- SharpTopologicalOverlap/Intersection/Indicators.lean
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_ne_zero
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_empty
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_vertex
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_eq_zero_of_range_disjoint
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_eq_zero_of_range_subset
#print axioms SharpTopologicalOverlap.Geometry.refinedIndicator_support_incidence

-- SharpTopologicalOverlap/Intersection/LocalConstruction.lean
#print axioms SharpTopologicalOverlap.barycentric_local_facet_identity
#print axioms SharpTopologicalOverlap.barycentric_family_facet_coboundary
#print axioms SharpTopologicalOverlap.barycentric_family_anchor_zero
#print axioms SharpTopologicalOverlap.barycentric_family_vertex_cocycle

-- SharpTopologicalOverlap/Intersection/LocalParity.lean
#print axioms SharpTopologicalOverlap.Geometry.placed_cell_affineIndependent
#print axioms SharpTopologicalOverlap.Geometry.range_placed_vertices
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_coboundary

-- SharpTopologicalOverlap/Intersection/Matching.lean
#print axioms SharpTopologicalOverlap.card_mul_le_of_strongGeneralPosition
#print axioms SharpTopologicalOverlap.card_le_div_of_strongGeneralPosition

-- SharpTopologicalOverlap/Intersection/Normalization.lean
#print axioms SharpTopologicalOverlap.Geometry.unique_top_incidence_of_generic_vertex
#print axioms SharpTopologicalOverlap.Geometry.unique_original_vertex_top_incidence
#print axioms SharpTopologicalOverlap.Geometry.barycentric_family_normalization

-- SharpTopologicalOverlap/Intersection/Refinement.lean
#print axioms SharpTopologicalOverlap.Simplicial.evaluation_pullbackCochain
#print axioms SharpTopologicalOverlap.Simplicial.coboundary_pullbackCochain
#print axioms SharpTopologicalOverlap.Simplicial.exists_supported_cell_of_pullbackCochain_ne_zero
#print axioms SharpTopologicalOverlap.Simplicial.skeletonCellEquiv_vertices
#print axioms SharpTopologicalOverlap.Simplicial.skeletonCellEquiv_face
#print axioms SharpTopologicalOverlap.Simplicial.coboundary_extendSkeletonCochain

-- SharpTopologicalOverlap/Intersection/Support.lean
#print axioms SharpTopologicalOverlap.skeletonFace_mono
#print axioms SharpTopologicalOverlap.SupportMeets.upwardSupport
#print axioms SharpTopologicalOverlap.SupportMeets.subfamily
#print axioms SharpTopologicalOverlap.exists_support_transfer_tolerances

-- SharpTopologicalOverlap/Intersection/TargetPlacement.lean
#print axioms SharpTopologicalOverlap.Geometry.barycentricTargetCells_mono
#print axioms SharpTopologicalOverlap.Geometry.targetSimplexFamily_range
#print axioms SharpTopologicalOverlap.Geometry.localIndicator_coboundary_of_generic

-- SharpTopologicalOverlap/Intersection/VertexCocycles.lean
#print axioms SharpTopologicalOverlap.exists_edge_with_facets
#print axioms SharpTopologicalOverlap.sum_edge_facets
#print axioms SharpTopologicalOverlap.vertex_cocycles_of_facet_identity
