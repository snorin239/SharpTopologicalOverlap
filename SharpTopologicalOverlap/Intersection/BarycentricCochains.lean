module

public import SharpTopologicalOverlap.Intersection.Indicators
public import SharpTopologicalOverlap.Intersection.Support
public import SharpTopologicalOverlap.Geometry.SourceApproximation
public import SharpTopologicalOverlap.Geometry.TargetCycle

/-! # Intersection cochains on the actual barycentric refinement

These cochains sum genuine hull-intersection indicators using the proved
chain map on the same subdivision as the continuous source interpolation.
Their support incidence and vertex formula are unconditional. The facet
identity follows from local intersection parity on the actual fine cells.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open SharpTopologicalOverlap.Simplicial SharpTopologicalOverlap.Geometry AbstractSimplicialComplex

attribute [local instance] Classical.propDecidable

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}

/-- The actual source refinement used by both chains and interpolation. -/
abbrev sourceBarycentricModel (n d j : ℕ) := barycentricModel (skeletonComplex (Fin n) d) j

/-- Actual local intersection counts, summed over refined source faces. -/
def barycentricCochainFamily (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) : IntersectionCochainFamily T n d :=
  fun p q hpq τ => refinedIndicator (by omega : q ≤ d)
    (iteratedSubdivision (skeletonComplex (Fin n) d) j q) y (B p τ)

omit [Fintype W] [LinearOrder W] in
/-- Empty target cells give zero cochains, including the vertex at infinity. -/
theorem barycentricCochainFamily_eq_zero_of_empty (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) {p q : ℕ} (hpq : p + q = d) (τ : Cell T p)
    (hB : B p τ = ∅) : barycentricCochainFamily j y B p q hpq τ = 0 := by
  funext s
  simp [barycentricCochainFamily, refinedIndicator, hB, extendSkeletonCochain,
    pullbackCochain]

omit [Fintype W] [LinearOrder W] in
/-- Every nonzero source cochain value has an actual source/target incidence. -/
theorem barycentricCochainFamily_supportMeets (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) :
    SupportMeets (barycentricCochainFamily j y B)
      (barycentricSourceMap (sourceBarycentricModel n d j) y) B := by
  classical
  intro p q hpq τ σ hσ
  let a := barycentricCochainFamily j y B p q hpq τ
  have hcard := supportFamily_uniform a σ hσ
  let s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) q :=
    (fullCellEquiv (Fin n) q).symm ⟨σ, hcard⟩
  have hs : a s ≠ 0 := (mem_supportFamily a s).mp hσ
  change pullbackCochain (iteratedSubdivision (skeletonComplex (Fin n) d) j q)
    (localIndicator y (B p τ)) (skeletonCellEquiv (by omega : q ≤ d) s) ≠ 0 at hs
  obtain ⟨u, hu, hi⟩ := exists_supported_cell_of_pullbackCochain_ne_zero _ _ _ hs
  obtain ⟨z, hz, hzB⟩ := (localIndicator_ne_zero y (B p τ) u).mp hi
  refine ⟨z, fine_hull_subset_sourceFace_image (sourceBarycentricModel n d j) y
    u.1 σ ?_ hz, hzB⟩
  exact iteratedSubdivision_carried (skeletonComplex (Fin n) d) j q
    (skeletonCellEquiv (by omega : q ≤ d) s) hu

/-- The source map at an original coordinate vertex is exactly its placed
copy in the actual subdivision. -/
theorem barycentricSourceMap_original_vertex (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d)) (v : Fin n) :
    barycentricSourceMap (sourceBarycentricModel n d j) y
      (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
        (skeletonComplex (Fin n) d) v)) =
      y (originalVertex (skeletonComplex (Fin n) d) j v) := by
  simp only [barycentricSourceMap, Function.comp_apply, Homeomorph.symm_apply_apply]
  rw [← originalVertex_point (skeletonComplex (Fin n) d) j v]
  exact (sourceBarycentricModel n d j).interpolation_vertexPoint y _

omit [Fintype W] [LinearOrder W] in
/-- The degree-zero cochain is the indicator of membership of the original
vertex image in the target top cell. -/
@[simp] theorem barycentricCochainFamily_vertex (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) (τ : Cell T d) (v : Fin n) :
    barycentricCochainFamily j y B d 0 (Nat.add_zero d) τ
      (RealizationCell.vertex (⊤ : AbstractSimplicialComplex (Fin n)) v) =
        if y (originalVertex (skeletonComplex (Fin n) d) j v) ∈ B d τ then 1 else 0 := by
  classical
  have hsk : skeletonCellEquiv (Nat.zero_le d)
      (RealizationCell.vertex (⊤ : AbstractSimplicialComplex (Fin n)) v) =
        RealizationCell.vertex (skeletonComplex (Fin n) d) v := by
    apply cell_vertices_injective
    simp
  simp only [barycentricCochainFamily, refinedIndicator, extendSkeletonCochain,
    Function.comp_apply, pullbackCochain, hsk, iteratedSubdivision_vertex,
    evaluation_single, one_mul, localIndicator_vertex]

omit [Fintype W] [LinearOrder W] in
/-- The same formula stated directly using the constructed continuous source map. -/
theorem barycentricCochainFamily_vertex_map (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) (τ : Cell T d) (v : Fin n) :
    barycentricCochainFamily j y B d 0 (Nat.add_zero d) τ
      (RealizationCell.vertex (⊤ : AbstractSimplicialComplex (Fin n)) v) =
        if barycentricSourceMap (sourceBarycentricModel n d j) y
          (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
            (skeletonComplex (Fin n) d) v)) ∈ B d τ then 1 else 0 := by
  rw [barycentricCochainFamily_vertex, barycentricSourceMap_original_vertex]

private theorem evaluation_sum_cochain {Q ι : Type*} [Fintype ι]
    {L : AbstractSimplicialComplex Q} {k : ℕ} (a : ι → Cochain L k) (c : Chain L k) :
    evaluation (∑ i, a i) c = ∑ i, evaluation (a i) c := by
  simp only [evaluation, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

omit [Fintype W] in
/-- The actual fine-cell parity identity gives Lemma 3.1(a) after applying
the proved source chain map and extending to the full simplex. -/
theorem barycentricCochainFamily_facet_coboundary (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d)
    (hlocal : ∀ p q (_hpq : (p + 1) + q = d) (τ : Cell T (p + 1)),
      coboundary (localIndicator y (B (p + 1) τ) :
        Cochain (sourceBarycentricModel n d j).complex q) =
          ∑ i : Fin (p + 2), (localIndicator y (B p (τ.face i)) :
            Cochain (sourceBarycentricModel n d j).complex (q + 1))) :
    ∀ p q (hpq : (p + 1) + q = d) (τ : Cell T (p + 1)),
      coboundary (barycentricCochainFamily j y B (p + 1) q hpq τ) =
        ∑ i : Fin (p + 2),
          barycentricCochainFamily j y B p (q + 1) (by omega) (τ.face i) := by
  intro p q hpq τ
  unfold barycentricCochainFamily refinedIndicator
  rw [coboundary_extendSkeletonCochain (by omega : q + 1 ≤ d),
    coboundary_pullbackCochain _ _
      (boundary_iteratedSubdivision (skeletonComplex (Fin n) d) j q), hlocal p q hpq τ]
  funext s
  simp only [extendSkeletonCochain, Function.comp_apply, pullbackCochain,
    evaluation_sum_cochain, Finset.sum_apply]

omit [LinearOrder W] in
/-- Unique top-cell incidence and the actual target cycle coefficients give
the normalization in Lemma 3.1(c). -/
theorem barycentricCochainFamily_normalization (j : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells T d) (ζ : Chain T d) (hζ : ∀ τ : Cell T d, ζ τ = 1)
    (hunique : ∀ v : Fin n, ∃! τ : Cell T d,
      barycentricSourceMap (sourceBarycentricModel n d j) y
        (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
          (skeletonComplex (Fin n) d) v)) ∈ B d τ) :
    ∑ τ : Cell T d, ζ τ • barycentricCochainFamily j y B d 0 (Nat.add_zero d) τ =
      oneCochain (⊤ : AbstractSimplicialComplex (Fin n)) := by
  classical
  funext s
  rw [s.eq_vertex]
  obtain ⟨τ, hτ, hother⟩ := hunique (s.vertexEmbedding 0)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    barycentricCochainFamily_vertex_map, oneCochain_apply]
  rw [Finset.sum_eq_single τ]
  · simp only [hζ τ, ite_eq_left hτ, one_mul]
  · intro η _ hητ
    have hnot : barycentricSourceMap (sourceBarycentricModel n d j) y
        (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
          (skeletonComplex (Fin n) d) (s.vertexEmbedding 0))) ∉ B d η :=
        fun h => hητ (hother η h)
    simp only [ite_eq_right hnot, mul_zero]
  · simp

/-- The normalization specialized to the actual refined target sphere and
its explicitly constructed fundamental cycle. -/
theorem barycentricCochainFamily_target_normalization (j r : ℕ)
    (y : (sourceBarycentricModel n d j).Vertex → EuclideanSpace ℝ (Fin d))
    (B : TargetCells (TargetCycle.model d r).complex d)
    (hunique : ∀ v : Fin n, ∃! τ : Cell (TargetCycle.model d r).complex d,
      barycentricSourceMap (sourceBarycentricModel n d j) y
        (skeletonRealizationHomeomorph d (AbstractSimplicialComplex.vertex
          (skeletonComplex (Fin n) d) v)) ∈ B d τ) :
    ∑ τ : Cell (TargetCycle.model d r).complex d,
      TargetCycle.refinedCycle d r τ • barycentricCochainFamily j y B d 0 (Nat.add_zero d) τ =
        oneCochain (⊤ : AbstractSimplicialComplex (Fin n)) :=
  barycentricCochainFamily_normalization j y B (TargetCycle.refinedCycle d r)
    (TargetCycle.refinedCycle_apply d r) hunique

end SharpTopologicalOverlap
