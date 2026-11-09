module

public import SharpTopologicalOverlap.Geometry.SimplexParity.Coordinates
public import SharpTopologicalOverlap.Geometry.SimplexParity.Line
public import SharpTopologicalOverlap.Geometry.Intersections
public import SharpTopologicalOverlap.Geometry.ConstraintParity

/-! # Geometric facet parity for transverse simplex intersections

Lower-face avoidance and spanning face directions are the explicit G3 and G4
hypotheses. Barycentric coordinates on the common affine line connect them to
the scalar constraint-parity theorem.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.SimplexParity

open Set Module
open scoped BigOperators
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {p q : ℕ}

abbrev vertexHull {ι : Type*} (v : ι → E) (A : Finset ι) : Set E :=
  convexHull ℝ (v '' (A : Set ι))

/-- G3 on the relevant lower source and target faces. -/
def LowerFaceAvoidance (s : Affine.Simplex ℝ E (p + 1))
    (t : Affine.Simplex ℝ E (q + 1)) : Prop :=
  ∀ (A : Finset (Fin (p + 2))) (B : Finset (Fin (q + 2))),
    A.card + B.card ≤ finrank ℝ E + 1 →
      Disjoint (vertexHull s.points A) (vertexHull t.points B)

/-- G4 on all source and target face pairs at or above complementary dimension. -/
def FaceSpanning (s : Affine.Simplex ℝ E (p + 1))
    (t : Affine.Simplex ℝ E (q + 1)) : Prop :=
  ∀ (A : Finset (Fin (p + 2))) (B : Finset (Fin (q + 2))),
    finrank ℝ E + 2 ≤ A.card + B.card →
      (affineSpan ℝ (s.points '' (A : Set (Fin (p + 2))))).direction ⊔
        (affineSpan ℝ (t.points '' (B : Set (Fin (q + 2))))).direction = ⊤

omit [FiniteDimensional ℝ E] in
theorem LowerFaceAvoidance.symm {s : Affine.Simplex ℝ E (p + 1)}
    {t : Affine.Simplex ℝ E (q + 1)} (h : LowerFaceAvoidance s t) :
    LowerFaceAvoidance t s := by
  intro A B hdim
  exact (h B A (by omega)).symm

omit [FiniteDimensional ℝ E] in
theorem FaceSpanning.symm {s : Affine.Simplex ℝ E (p + 1)}
    {t : Affine.Simplex ℝ E (q + 1)} (h : FaceSpanning s t) : FaceSpanning t s := by
  intro A B hdim
  simpa only [sup_comm] using h B A (by omega)

variable (s : Affine.Simplex ℝ E (p + 1)) (t : Affine.Simplex ℝ E (q + 1))
  (hdim : (p + 1) + (q + 1) = finrank ℝ E + 1)

include hdim

omit [FiniteDimensional ℝ E] in
theorem eq_of_two_zero_source_coordinates (havoid : LowerFaceAvoidance s t)
    (c : Coordinates s.points) {x : E}
    (hxs : x ∈ convexHull ℝ (range s.points)) (hxt : x ∈ convexHull ℝ (range t.points))
    {i j : Fin (p + 2)} (hi : c.coord i x = 0) (hj : c.coord j x = 0) : i = j := by
  by_contra hij
  have hsmall : ((Finset.univ.erase i).erase j).card +
      (Finset.univ : Finset (Fin (q + 2))).card ≤ finrank ℝ E + 1 := by
    have hjmem : j ∈ (Finset.univ : Finset (Fin (p + 2))).erase i := by
      simp [Ne.symm hij]
    rw [Finset.card_erase_of_mem hjmem]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] at *
    omega
  exact Set.disjoint_left.mp (havoid _ _ hsmall)
    (c.mem_double_erased_face_hull hxs hi hj) (by simpa only [vertexHull,
      Finset.coe_univ, Set.image_univ] using hxt)

omit [FiniteDimensional ℝ E] in
theorem false_of_zero_source_target_coordinates (havoid : LowerFaceAvoidance s t)
    (c : Coordinates s.points) (e : Coordinates t.points) {x : E}
    (hxs : x ∈ convexHull ℝ (range s.points)) (hxt : x ∈ convexHull ℝ (range t.points))
    (i : Fin (p + 2)) (j : Fin (q + 2)) (hi : c.coord i x = 0) (hj : e.coord j x = 0) :
    False := by
  have hsmall : (Finset.univ.erase i).card + (Finset.univ.erase j).card ≤
      finrank ℝ E + 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  exact Set.disjoint_left.mp (havoid _ _ hsmall)
    ((c.mem_erased_face_hull_iff hxs i).mpr hi) ((e.mem_erased_face_hull_iff hxt j).mpr hj)

theorem source_coord_slope_ne_zero (hspan : FaceSpanning s t)
    (c : Coordinates s.points)
    (l : Line ((affineSpan ℝ (range s.points)) ⊓ (affineSpan ℝ (range t.points))))
    (u : ℝ) (i : Fin (p + 2)) (hi : c.coord i (l.point u) = 0) :
    (c.coord i).contLinear l.vector ≠ 0 := by
  intro hzero
  let F := affineSpan ℝ (s.points '' (↑(Finset.univ.erase i) : Set (Fin (p + 2))))
  let T := affineSpan ℝ (range t.points)
  have hxS : l.point u ∈ affineSpan ℝ (range s.points) := (l.point_mem u).1
  have hyS : l.point (u + 1) ∈ affineSpan ℝ (range s.points) := (l.point_mem _).1
  have hiy : c.coord i (l.point (u + 1)) = 0 := by
    rw [l.coord_point, hzero, mul_zero, add_zero]
    rw [l.coord_point, hzero, mul_zero, add_zero] at hi
    exact hi
  have hxF : l.point u ∈ F := (c.mem_erased_face_span_iff hxS i).mpr hi
  have hyF : l.point (u + 1) ∈ F := (c.mem_erased_face_span_iff hyS i).mpr hiy
  have hdiff : l.point (u + 1) - l.point u = l.vector := by
    simp only [Line.point, add_smul, one_smul]
    abel
  have hvF : l.vector ∈ F.direction := by
    rw [← hdiff]
    exact F.vsub_mem_direction hyF hxF
  have hvT : l.vector ∈ T.direction :=
    ((AffineSubspace.direction_inf _ _) l.vector_mem).2
  have hspanFT : F.direction ⊔ T.direction = ⊤ := by
    have hcard : finrank ℝ E + 2 ≤ (Finset.univ.erase i).card +
        (Finset.univ : Finset (Fin (q + 2))).card := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      omega
    simpa only [F, T, Finset.coe_univ, Set.image_univ] using hspan _ _ hcard
  have hFdim : finrank ℝ F.direction = p := by
    rw [show F = affineSpan ℝ (s.points '' (↑(Finset.univ.erase i) : Set (Fin (p + 2)))) from rfl,
      direction_affineSpan, ← Finset.coe_image]
    exact s.independent.finrank_vectorSpan_image_finset (by simp)
  have hTdim : finrank ℝ T.direction = q + 1 := by
    rw [show T = affineSpan ℝ (range t.points) from rfl, direction_affineSpan]
    exact t.independent.finrank_vectorSpan (by simp)
  have hdis := disjoint_of_sup_eq_top_of_finrank_add F.direction T.direction hspanFT
    (by rw [hFdim, hTdim]; omega)
  exact l.vector_ne (Submodule.disjoint_def.mp hdis _ hvF hvT)

set_option maxHeartbeats 800000 in
/-- The geometric local parity identity: source-facet and target-facet
intersection counts sum to zero modulo two under G2--G4. The simplex bundles
supply G2; the two hypotheses state G3 and G4 on their actual vertex subsets. -/
theorem facet_intersection_parity (havoid : LowerFaceAvoidance s t)
    (hspan : FaceSpanning s t) :
    (∑ i : Fin (p + 2), if (vertexHull s.points (Finset.univ.erase i) ∩
        convexHull ℝ (range t.points)).Nonempty then (1 : ZMod 2) else 0) +
      (∑ j : Fin (q + 2), if (convexHull ℝ (range s.points) ∩
        vertexHull t.points (Finset.univ.erase j)).Nonempty then (1 : ZMod 2) else 0) = 0 := by
  classical
  have hfull : (affineSpan ℝ (range s.points)).direction ⊔
      (affineSpan ℝ (range t.points)).direction = ⊤ := by
    have hcard : finrank ℝ E + 2 ≤
        (Finset.univ : Finset (Fin (p + 2))).card +
          (Finset.univ : Finset (Fin (q + 2))).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    simpa only [Finset.coe_univ, Set.image_univ] using hspan _ _ hcard
  have hcommon := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
    ⟨s.points 0, s.mem_affineSpan_range 0⟩ ⟨t.points 0, t.mem_affineSpan_range 0⟩ hfull
  have hrank := simplex_finrank_direction_inf_eq_one s t hdim hfull
  obtain ⟨l⟩ := exists_line ((affineSpan ℝ (range s.points)) ⊓
    (affineSpan ℝ (range t.points))) hcommon hrank
  obtain ⟨c⟩ := exists_coordinates s.independent
  obtain ⟨e⟩ := exists_coordinates t.independent
  let I := Fin (p + 2) ⊕ Fin (q + 2)
  let f : I → E →ᴬ[ℝ] ℝ := Sum.elim c.coord e.coord
  let a : I → ℝ := fun i => f i l.base
  let b : I → ℝ := fun i => (f i).contLinear l.vector
  have heval (i : I) (u : ℝ) : a i + u * b i = f i (l.point u) :=
    (l.coord_point (f i) u).symm
  have hfeas (u : ℝ) : u ∈ feasibleParameters a b ↔
      l.point u ∈ convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points) := by
    constructor
    · intro hu
      refine ⟨(c.mem_hull_iff (l.point_mem u).1).mpr (fun i => ?_),
        (e.mem_hull_iff (l.point_mem u).2).mpr (fun j => ?_)⟩
      · exact (heval (Sum.inl i) u) ▸ hu (Sum.inl i)
      · exact (heval (Sum.inr j) u) ▸ hu (Sum.inr j)
    · intro hx i
      rw [heval]
      cases i with
      | inl i => exact c.coord_nonneg_of_mem_hull hx.1 i
      | inr j => exact e.coord_nonneg_of_mem_hull hx.2 j
  have hcompact : IsCompact (feasibleParameters a b) := by
    have heq : feasibleParameters a b = l.point ⁻¹'
        (convexHull ℝ (range s.points) ∩ convexHull ℝ (range t.points)) :=
      Set.ext hfeas
    rw [heq]
    exact l.isClosedEmbedding_point.isCompact_preimage
      (((Set.finite_range s.points).isCompact_convexHull ℝ).inter
        ((Set.finite_range t.points).isCompact_convexHull ℝ))
  have hunique : ∀ u ∈ feasibleParameters a b, ∀ i j : I,
      a i + u * b i = 0 → a j + u * b j = 0 → i = j := by
    intro u hu i j hi hj
    have hx := (hfeas u).mp hu
    rw [heval] at hi hj
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact congrArg Sum.inl
          (eq_of_two_zero_source_coordinates s t hdim havoid c hx.1 hx.2 hi hj)
      | inr j =>
        exact (false_of_zero_source_target_coordinates s t hdim havoid c e
          hx.1 hx.2 i j hi hj).elim
    | inr i =>
      cases j with
      | inl j =>
        exact (false_of_zero_source_target_coordinates s t hdim havoid c e
          hx.1 hx.2 j i hj hi).elim
      | inr j =>
        exact congrArg Sum.inr
          (eq_of_two_zero_source_coordinates t s (by omega) havoid.symm e hx.2 hx.1 hi hj)
  have hslope : ∀ u ∈ feasibleParameters a b, ∀ i : I,
      a i + u * b i = 0 → b i ≠ 0 := by
    intro u _ i hi
    rw [heval] at hi
    cases i with
    | inl i => exact source_coord_slope_ne_zero s t hdim hspan c l u i hi
    | inr j => exact source_coord_slope_ne_zero t s (by omega) hspan.symm e l.swapInf u j hi
  have hleft (i : Fin (p + 2)) :
      (∃ u ∈ feasibleParameters a b, a (Sum.inl i) + u * b (Sum.inl i) = 0) ↔
        (vertexHull s.points (Finset.univ.erase i) ∩ convexHull ℝ (range t.points)).Nonempty := by
    constructor
    · rintro ⟨u, hu, hi⟩
      have hx := (hfeas u).mp hu
      refine ⟨l.point u, (c.mem_erased_face_hull_iff hx.1 i).mpr ?_, hx.2⟩
      exact (heval (Sum.inl i) u) ▸ hi
    · rintro ⟨x, hxs, hxt⟩
      have hxfull : x ∈ convexHull ℝ (range s.points) :=
        convexHull_mono (Set.image_subset_range _ _) hxs
      obtain ⟨u, hu⟩ := l.point_surjective (show x ∈
        (affineSpan ℝ (range s.points)) ⊓ (affineSpan ℝ (range t.points)) from
          ⟨convexHull_subset_affineSpan _ hxfull, convexHull_subset_affineSpan _ hxt⟩)
      refine ⟨u, (hfeas u).mpr (by rw [hu]; exact ⟨hxfull, hxt⟩), ?_⟩
      rw [heval, hu]
      exact (c.mem_erased_face_hull_iff hxfull i).mp hxs
  have hright (j : Fin (q + 2)) :
      (∃ u ∈ feasibleParameters a b, a (Sum.inr j) + u * b (Sum.inr j) = 0) ↔
        (convexHull ℝ (range s.points) ∩ vertexHull t.points (Finset.univ.erase j)).Nonempty := by
    constructor
    · rintro ⟨u, hu, hj⟩
      have hx := (hfeas u).mp hu
      refine ⟨l.point u, hx.1, (e.mem_erased_face_hull_iff hx.2 j).mpr ?_⟩
      exact (heval (Sum.inr j) u) ▸ hj
    · rintro ⟨x, hxs, hxt⟩
      have hxfull : x ∈ convexHull ℝ (range t.points) :=
        convexHull_mono (Set.image_subset_range _ _) hxt
      obtain ⟨u, hu⟩ := l.point_surjective (show x ∈
        (affineSpan ℝ (range s.points)) ⊓ (affineSpan ℝ (range t.points)) from
          ⟨convexHull_subset_affineSpan _ hxs, convexHull_subset_affineSpan _ hxfull⟩)
      refine ⟨u, (hfeas u).mpr (by rw [hu]; exact ⟨hxs, hxfull⟩), ?_⟩
      rw [heval, hu]
      exact (e.mem_erased_face_hull_iff hxfull j).mp hxt
  have hparity := sum_activeConstraint_indicators_eq_zero a b hcompact hunique hslope
  rw [Fintype.sum_sum_type] at hparity
  simpa only [hleft, hright] using hparity

omit hdim in
theorem erased_vertex_image_eq_range_succAbove {α : Type*} {n : ℕ}
    (v : Fin (n + 1) → α) (i : Fin (n + 1)) :
    v '' (↑(Finset.univ.erase i) : Set (Fin (n + 1))) = range (v ∘ i.succAbove) := by
  rw [Set.range_comp, Fin.range_succAbove]
  congr 1
  ext j
  simp

/-- The same parity identity with the ordered deletion maps used by the affine
chain boundary. -/
theorem facet_intersection_parity_succAbove (havoid : LowerFaceAvoidance s t)
    (hspan : FaceSpanning s t) :
    (∑ i : Fin (p + 2), if (convexHull ℝ (range (s.points ∘ i.succAbove)) ∩
        convexHull ℝ (range t.points)).Nonempty then (1 : ZMod 2) else 0) +
      (∑ j : Fin (q + 2), if (convexHull ℝ (range s.points) ∩
        convexHull ℝ (range (t.points ∘ j.succAbove))).Nonempty then (1 : ZMod 2) else 0) = 0 := by
  simpa only [vertexHull, erased_vertex_image_eq_range_succAbove] using
    facet_intersection_parity s t hdim havoid hspan

/-- The local boundary-duality equation consumed by intersection cochains. -/
theorem source_facet_count_eq_target_facet_count (havoid : LowerFaceAvoidance s t)
    (hspan : FaceSpanning s t) :
    (∑ i : Fin (p + 2), if (convexHull ℝ (range (s.points ∘ i.succAbove)) ∩
        convexHull ℝ (range t.points)).Nonempty then (1 : ZMod 2) else 0) =
      (∑ j : Fin (q + 2), if (convexHull ℝ (range s.points) ∩
        convexHull ℝ (range (t.points ∘ j.succAbove))).Nonempty then (1 : ZMod 2) else 0) := by
  have h := facet_intersection_parity_succAbove s t hdim havoid hspan
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  simpa only [hneg] using eq_neg_of_add_eq_zero_left h

end SharpTopologicalOverlap.Geometry.SimplexParity
