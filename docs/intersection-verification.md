# Independent verification of block G

**Block G is complete.** Lemma 3.1 is proved by
[`exists_intersectionData`](../SharpTopologicalOverlap/Intersection/Existence.lean).
Its only hypotheses are `2 ≤ d`, `d + 1 ≤ n`, and an arbitrary continuous map
`f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))`.

The result constructs an `IntersectionWitness f`: a finite ordered target
complex, an actual target cycle, all five intersection-cochain properties,
and a target `d`-cell. Together with the dimension upper bound, the last field
establishes that the target dimension is exactly `d`. No placement,
triangulation, parity identity, or normalization assumption remains
as an input to the existence theorem.

## The five conclusions

| Paper conclusion | Checked implementation |
| --- | --- |
| (a) Facet coboundary identity | `SimplexParity.facet_intersection_parity` proves actual geometric parity under G2–G4. `localIndicator_coboundary_of_generic` applies it to actual fine cells; `barycentric_family_facet_coboundary` pulls the identity back along the actual source subdivision chain map. |
| (b) Vertex cocycles | `barycentric_family_vertex_cocycle` uses the proved facet identities, actual target edge paths to infinity, the proved zero anchor, and coboundary squared zero on the full source simplex. |
| (c) Normalization | `barycentric_family_normalization` uses actual coverage and unique top patch cells, the unchanged original source vertices in degree zero, and `refinedCycle_apply = 1` on every actual target top cell. |
| (d) Common point | The actual cochain support meets the corresponding target carrier. The carriers are globally monotone and have small diameter. The proved compact-family tolerances transfer these incidences through `h → g → f` simultaneously for every upward support family. |
| (e) Disjoint-support bound | The same compactness transfer gives a common point in the original-face images under the constructed strong-general-position map `g`. `card_le_div_of_strongGeneralPosition` yields the exact natural-division bound `A.card ≤ d / p` for `0 < p`. |

## Constructed geometry and algebra

The proof uses one coherent iterated barycentric model for the source and one
for the target. Each model has an actual finite abstract complex, its canonical
realization homeomorphism, shared vertex positions, original-face carriers,
and shrinking mesh. The source chain subdivision is on these same indices,
commutes with boundary, preserves original degree-zero vertices, and retains
each original face carrier. Thus the final construction does not depend on an
unproved identification between separate subdivision representations.

`exists_first_source_approximation` constructs the continuous first map `g`,
uniformly close to `f`, with strong general position on the original source
faces. After choosing its compactness tolerance, the proof constructs an
enclosing simplex `D` and an actual sufficiently fine target subdivision.
`exists_second_source_approximation` then constructs `h` on the same source
subdivision, with all four conditions of Lemma A.2 simultaneously. Its range
lies in the interior of `D` by the proved closed-neighborhood bound.

The geometric parity theorem parametrizes the actual common affine line of
two simplices. Ambient continuous barycentric coordinates identify their hull
intersection with finitely many affine inequalities. Compactness follows from
the proper line parametrization. G3 proves uniqueness of an active coordinate;
G4 proves its nonzero slope. The scalar endpoint theorem then gives zero or
two incident facets, and the actual facet-indicator sum is zero modulo two.
These scalar hypotheses are discharged inside the geometric theorem.

The target is the actual subdivided boundary sphere. Its cycle, coefficient
one on every top cell, dimension bound, and edge paths to the refined infinity
vertex are proved. Physical target carriers use the convex hull of the inside
vertices of each cell. They are monotone on all subfaces. Every outer carrier
lies in one proper face of `D`, so it misses the source image in `int D`; the
infinity carrier is empty. `TargetCoverage.existsUnique_top_targetCells` proves
actual coverage and uniqueness at points avoiding lower-dimensional patch
hulls. Generic placement supplies that avoidance at source vertex images.

## Boundary and dimension checks

- Compact separation includes empty indexing types, empty compact sets, and
  empty subfamilies. The Euclidean target is nonempty in every dimension.
- Open simplices use intrinsic interior, including the vertex in dimension
  zero. G2 in dimension zero requires independence only on singleton sets.
- The geometric parity argument concerns two positive-dimensional simplices
  with dimensions summing to `d + 1`, exactly the range needed for the positive
  target-degree facet identity. Empty hull intersections contribute zero.
- Matching handles families of cardinality zero and one before invoking the
  strict G1 inequality. Division is used only after proving `0 < p`.
- The vertex-cocycle equation is on the full source simplex in degree `d + 1`.
  It is obtained algebraically from target paths, without evaluating `f` on an
  unavailable source `(d + 1)`-simplex. At `n = d + 1`, that cochain equation
  has an empty family of source test faces, as it should.
- Target/source cochain degrees satisfy `p + q = d`; facet identities decrease
  the target degree and increase the source degree. Normalization uses the
  actual `ZMod 2` cycle coefficients.
- `upwardSupport` includes all supported subfaces and all original source
  `d`-faces containing them, matching the simultaneous family in Lemma 3.1(d).
- Exact target dimension follows from the constructed top cell. Source
  nonemptiness used for this deduction follows from the stated size and
  dimension hypotheses.

## Reproducible kernel and source audits

The independent probe is [`verification/BlockG.lean`](../verification/BlockG.lean).
It imports all 40 block-G modules directly, preserves deliberate boundary-case
specializations, and prints the transitive axioms of every public theorem.
The complete output is
[`verification/BlockG-axioms.txt`](../verification/BlockG-axioms.txt).

All **335 theorem audits**, including `exists_intersectionData`, passed.
Every dependency list contains exactly `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, project axiom, or native-evaluation trust axiom
appears. A source scan of every project `.lean` file found no `sorry`, `admit`,
`axiom`, `unsafe`, or `implemented_by` token.

Regenerate and run the audit from the repository root:

```powershell
lake build
./verification/refresh_block_g_audit.ps1
lake env lean verification/BlockG.lean
```

The generator reads actual namespace scopes and skips comments. The probe
requires checked project module objects; it introduces no project assumptions.
All new modules were individually checked and built during implementation.
The final integrated `lake build` passed with 8983 jobs and no warnings or
errors. A direct `lake env lean SharpTopologicalOverlap/Intersection/Existence.lean`
check also passed with empty output. The complete independent audit probe
passed without warnings or errors.
