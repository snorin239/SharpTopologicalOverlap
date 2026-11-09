# Block G: intersection cochains

Block G is complete. The endpoint `exists_intersectionData` proves
Lemma 3.1 (`lem:intersection`) with all five properties, following Appendix A
of the reference manuscript. The construction includes the needed
subdivision results and Lemmas A.1 and A.2. The manuscript is preserved.

## Proof order and dependencies

1. Prove one compactness tolerance for all families of original closed source
   faces. Derive the perturbation and small-target-cell transfer rules.
2. Construct indexed, face-compatible subdivisions, fundamental chains,
   boundary compatibility, and shrinking mesh. Preserve source indices when
   different image simplices coincide.
3. Prove the four generic-placement conditions, including their simultaneous
   approximation statement, and continuous affine interpolation. Construct
   `g` in strong general position before choosing its tolerance and the target
   triangulation; construct `h` afterwards.
4. Prove complementary point uniqueness and exclusion of proper faces. Prove
   the segment endpoint identity in total dimension `d + 1`, including that
   each endpoint belongs to exactly one facet.
5. Sum the intersection counts over fundamental chains. Cone the target
   boundary, construct the cycle, and prove normalization, the facet identity,
   vertex cocycles, common-point control, and the disjoint-support bound.
6. Construct `IntersectionData` for every map in Lemma 3.1, then expose its
   bounded-dimension interface to the later blocks.

## Parallel ownership

| Workstream | Initial owner | Files and concrete output |
| --- | --- | --- |
| Compactness and transfer | Stability subagent | `Geometry/Stability.lean`: finite compact-family tolerance, source-face specialization, perturbation transfer |
| Subdivision | Geometry subagent | `Geometry/Subdivision.lean`: adapt checked TauCeti affine subdivision results, boundary and carrier/mesh interfaces; identify geometric compatibility gaps |
| Cochain interface and algebra | Algebra subagent | `Intersection.lean`, `Intersection/Algebra.lean`, `Intersection/Matching.lean`, `Intersection/Construction.lean`: degree-safe five-property interface, cocycle propagation, cone-cycle identity, matching bound from strong general position, and local contributions summed on the actual fundamental chains |
| Complementary intersections and integration | Primary agent | `Geometry/Intersections.lean`, root imports, status and verification: transverse point uniqueness and open-face consequences, integration and independent review |

Agents are reassigned to remaining proofs or independent checks when their
current tasks finish. Shared files have a single owner. In particular the
primary agent owns the root import file and status documentation.

## Representations and reuse

Use the existing coordinate skeleton, `skeletonFace`, full-simplex cochains,
and `ZMod 2`. Keep degrees additive where possible: an intersection cochain
at a target `p`-cell has source degree `q` with `p + q = d`. This avoids
repeated casts through truncated natural subtraction. A cochain at a target
vertex must satisfy its cocycle equation on the full source simplex in degree
`d + 1`, even though `f` is only defined on the `d`-skeleton.

The construction reuses the pinned abstract subdivision homeomorphism,
transverse affine-subspace intersections, intrinsic simplex interiors,
and the ordered-chain cone identities. Source and target geometry use the
same actual abstract barycentric indices throughout.

### Checked common subdivisions and chains

`Geometry/BarycentricModel.lean` constructs the actual iterated abstract
subdivisions, their composed realization homeomorphisms and coordinate
linear maps. `Geometry/BarycentricApproximation.lean` proves shrinking
mesh and continuous interpolation on those indices. Actual coordinate
cells are nondegenerate by `Geometry/BarycentricGeometry.lean`.

`Geometry/TargetCycle.lean` builds the simplicial subdivision chain map
directly: subdivide each boundary and cone it to the full-face barycenter.
The model's vertex order puts proper subfaces before that apex. The cone
identities prove `boundary_subdivisionMap`; `iteratedSubdivision` then
supplies the actual source chain map at every depth.
`iteratedSubdivision_carried` and
`iteratedSubdivision_facePoint_carried` preserve the original closed-face
carrier for all supported child vertices and all their weighted points.
`iteratedSubdivision_vertex` and `originalVertex_point` preserve original
degree-zero generators and their realization points exactly.

The target starts from the boundary of a `(d + 1)`-simplex, with one
distinguished facet representing the enclosing simplex and the remaining
facets forming the cone on its boundary. `refinedCycle` is its actual
subdivided fundamental cycle. `boundary_refinedCycle`,
`refined_dimension_le`, and `refinedCycle_apply` prove closedness, dimension
at most `d`, and coefficient one on every top cell at every depth.
`refined_path_to_infinity` supplies the actual edge paths to the zero anchor.

The earlier affine-chain subdivision and one-step permutation bridge remain
available in `Geometry/Subdivision.lean` and `Geometry/BarycentricBridge.lean`.
The final existence construction uses the direct abstract chain map above.

### Checked placements, geometry, and cochain fields

Lemma A.2 is proved in `Geometry/GenericPlacements.lean`:
`open_dense_genericPlacement` and `exists_genericPlacement` combine all
four conditions on actual finite source and target families.
`Geometry/SourceApproximation.lean` applies these results to construct the
first approximation in strong general position and the second approximation
against the chosen target triangulation. The order is `f`, `g`, the tolerance
of `g`, the enclosing target simplex, its fine triangulation, then `h`.

`Geometry/EnclosingSimplex.lean` encloses the required closed metric
neighborhood in the interior of an actual full `d`-simplex.
`Geometry/TargetGeometry.lean` and its `Boundary` and `Mesh` modules provide
the physical target carriers. On every abstract face the carrier is the hull
of its vertices lying in the distinguished patch. This makes the carriers
monotone on all subfaces; outer carriers lie in a proper face of the enclosing
simplex and miss its interior. The carriers have arbitrarily small mesh.

The `Geometry/SimplexParity` modules verify the geometric hypotheses of
the line-constraint results in `Geometry/ConstraintParity.lean`, proving
the complementary point and segment facet-count identities, including empty
intersections and unique incident facets. `Intersection/TargetPlacement.lean`
applies them to the actual generic placements. In
`Intersection/LocalConstruction.lean`, the outer-cell terms vanish by the
proved boundary geometry, yielding the local identity on the whole target.

`Intersection/BarycentricCochains.lean` sums the genuine local indicators
through `iteratedSubdivision` and extends the resulting cochains from the
skeleton to the full simplex in degrees at most `d`. It proves actual
`SupportMeets` incidence, the degree-zero vertex formula, and the transfer
of the facet identity. The normalization is discharged by actual target
coverage and unique top-cell incidence in `Intersection/Normalization.lean`.
The zero anchor and the actual edge paths prove the full-source degree
`d + 1` vertex cocycle equation. Compactness transfer and the strong
general-position matching bound give properties (d) and (e).

### Final assembly

`Intersection/Existence.lean` assembles these constructed objects into
`exists_intersectionData`, with only `2 ≤ d`, `d + 1 ≤ n`, and the original
continuous map as inputs. The output includes a finite target, all five
`IntersectionData` fields, and an actual top cell, making the target
dimension exactly `d`. The existence module has built without warnings,
its direct Lean check produced no output, and the full root `lake build`
passed. The independent final audit covered 40 modules and 335 theorem
reports, including `exists_intersectionData`; every report listed exactly
`propext`, `Classical.choice`, and `Quot.sound`. The audit probe exited
successfully without warnings.

## Acceptance checks

- Check each new module with `lake env lean <file>` and run `lake build`.
- Audit important endpoints transitively with `#print axioms`.
- Inspect empty families, zero-dimensional simplices, cone vertices, and the
  `d + 1` source degree in the vertex cocycle equation.
- Mark a geometric result conditional when its placement, subdivision, or
  endpoint hypotheses have not yet been constructed.
- Update `FORMALIZATION.md` with proved declarations and precise remaining
  dependencies. Block G is complete only when `exists_intersectionData` is
  proved from the actual map and size/dimension hypotheses.
