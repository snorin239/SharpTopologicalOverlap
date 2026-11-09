module

public import SharpTopologicalOverlap.Geometry.Subdivision
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph

/-! # A common barycentric subdivision for chains and realizations

The one-step permutation children in the affine-chain construction are indexed
by actual cells of the abstract barycentric subdivision, with exactly the same
face barycenters. This does not yet identify iterated fundamental-chain support
with an entire triangulation or prove the converse maximal-chain indexing.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.BarycentricBridge

open Convexity

attribute [local instance] Classical.decEq

variable {V : Type*} [LinearOrder V] {K : AbstractSimplicialComplex V} {k : ℕ}

theorem affineMapMk_sourceVertices_eq_map (s : Simplicial.Cell K k)
    (w : Simplex (Fin (k + 1))) :
    StdSimplex.affineMapMk (R := ℝ) (sourceVertices s) w = w.map s.vertexEmbedding := by
  have h : StdSimplex.affineMapMk (R := ℝ) (sourceVertices s) =
      StdSimplex.affineMap (R := ℝ) s.vertexEmbedding := by
    apply StdSimplex.affineMap_ext
    intro i
    simp [sourceVertices, vertex]
  exact congrArg (fun f => f w) h

def permutationFace (s : Simplicial.Cell K k) (π : Equiv.Perm (Fin (k + 1)))
    (i : Fin (k + 1)) : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex :=
  ⟨((Finset.Ici i).map π.toEmbedding).map s.vertexEmbedding,
    K.isRelLowerSet_faces.mem_of_le s.1.2 (by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      exact s.vertexEmbedding_mem j)
      ((Finset.nonempty_Ici.map (f := π.toEmbedding)).map (f := s.vertexEmbedding))⟩

theorem permutationFace_antitone (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) : Antitone (permutationFace s π) := by
  intro i j hij
  change ((Finset.Ici j).map π.toEmbedding).map s.vertexEmbedding ⊆
    ((Finset.Ici i).map π.toEmbedding).map s.vertexEmbedding
  exact Finset.map_subset_map.mpr
    (Finset.map_subset_map.mpr (Finset.Ici_subset_Ici.mpr hij))

@[simp] theorem permutationFace_card (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    (permutationFace s π i).1.card = k + 1 - i := by
  simp [permutationFace, Fin.card_Ici]

theorem permutationFace_injective (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) : Function.Injective (permutationFace s π) := by
  intro i j hij
  have hc := congrArg
    (fun σ : TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex => σ.1.card) hij
  simp only [permutationFace_card] at hc
  apply Fin.ext
  omega

/-- Each permutation child is genuinely indexed by a cell of the abstract
barycentric subdivision, and not merely by an unrelated affine tuple. -/
def permutationCell (s : Simplicial.Cell K k) (π : Equiv.Perm (Fin (k + 1))) :
    Simplicial.Cell
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex) k := by
  classical
  refine ⟨⟨Finset.univ.image (permutationFace s π), ?_⟩, ?_⟩
  · apply TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mpr
    refine ⟨Finset.univ_nonempty.image _, ?_⟩
    intro σ hσ τ hτ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hτ
    rcases le_total i j with hij | hji
    · exact Or.inr (permutationFace_antitone s π hij)
    · exact Or.inl (permutationFace_antitone s π hji)
  · rw [Finset.card_image_of_injective _ (permutationFace_injective s π)]
    simp

theorem affine_child_vertex_eq_subBarycenter (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    StdSimplex.affineMapMk (R := ℝ) (sourceVertices s)
        (TauCeti.BarycentricSubdivision.vertex π i) =
      StdSimplex.subBarycenter (permutationFace s π i).1
        ((Finset.nonempty_Ici.map (f := π.toEmbedding)).map (f := s.vertexEmbedding)) := by
  rw [affineMapMk_sourceVertices_eq_map, TauCeti.BarycentricSubdivision.vertex_def,
    StdSimplex.map_subBarycenter]
  rfl

omit [LinearOrder V] in
theorem subBarycenter_weights_eq_faceBarycenter (σ : TauCeti.SetLike.Face K) :
    (StdSimplex.subBarycenter (K := ℝ) σ.1
      (K.isRelLowerSet_faces.prop_of_mem σ.2)).weights =
        AbstractSimplicialComplex.faceBarycenter K σ := by
  ext v
  simp [StdSimplex.weights_subBarycenter,
    AbstractSimplicialComplex.faceBarycenter_apply, Finsupp.single_apply]

theorem affine_child_vertex_weights_eq_faceBarycenter (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    (StdSimplex.affineMapMk (R := ℝ) (sourceVertices s)
        (TauCeti.BarycentricSubdivision.vertex π i)).weights =
      AbstractSimplicialComplex.faceBarycenter K (permutationFace s π i) := by
  rw [affine_child_vertex_eq_subBarycenter, subBarycenter_weights_eq_faceBarycenter]

/-- A weighted point of the abstract permutation cell. -/
def permutationPoint (s : Simplicial.Cell K k) (π : Equiv.Perm (Fin (k + 1)))
    (w : Simplex (Fin (k + 1))) :
    (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).Realization := by
  classical
  let μ := w.map (permutationFace s π)
  refine ⟨μ.weights, ?_⟩
  apply AbstractSimplicialComplex.mem_realization_iff.mpr
  refine ⟨(permutationCell s π).1.1, (permutationCell s π).1.2, ?_⟩
  suffices hm : μ.weights ∈ convexHull ℝ
      ((fun v => Finsupp.single v (1 : ℝ)) ''
        ((permutationCell s π).1.1 :
          Set (TauCeti.SetLike.Face K.toPreAbstractSimplicialComplex))) by
    simpa only [Finset.coe_image] using hm
  apply AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
  refine ⟨μ.nonneg, μ.total, ?_⟩
  intro σ hσ
  have hne : (w.weights.mapDomain (permutationFace s π)) σ ≠ 0 :=
    Finsupp.mem_support_iff.mp hσ
  obtain ⟨i, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hne
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem permutationPoint_val (s : Simplicial.Cell K k)
    (π : Equiv.Perm (Fin (k + 1))) (w : Simplex (Fin (k + 1))) :
    (permutationPoint s π w).1 = (w.map (permutationFace s π)).weights := rfl

/-- The abstract realization and the affine-chain construction parametrize
each permutation child by exactly the same weighted points. -/
theorem barycentricRealization_permutationPoint
    (s : Simplicial.Cell K k) (π : Equiv.Perm (Fin (k + 1)))
    (w : Simplex (Fin (k + 1))) :
    (AbstractSimplicialComplex.barycentricSubdivisionRealizationMap K
      (permutationPoint s π w)).1 =
        (StdSimplex.affineMapMk (R := ℝ)
          (StdSimplex.affineMapMk (R := ℝ) (sourceVertices s) ∘
            TauCeti.BarycentricSubdivision.vertex π) w).weights := by
  classical
  rw [AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_val,
    permutationPoint_val,
    AbstractSimplicialComplex.barycentricSubdivisionLinearMap_eq_linearCombination]
  change Finsupp.linearCombination ℝ (AbstractSimplicialComplex.faceBarycenter K)
    (w.weights.mapDomain (permutationFace s π)) = _
  rw [Finsupp.linearCombination_mapDomain]
  have hv : AbstractSimplicialComplex.faceBarycenter K ∘ permutationFace s π =
      fun i => (StdSimplex.affineMapMk (R := ℝ) (sourceVertices s)
        (TauCeti.BarycentricSubdivision.vertex π i)).weights := by
    funext i
    exact (affine_child_vertex_weights_eq_faceBarycenter s π i).symm
  rw [hv, Finsupp.linearCombination_apply]
  ext v
  simp only [Finsupp.sum, StdSimplex.weights_affineMapMk_apply, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, Function.comp_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi, zero_mul]

/-- Every supported one-step integral child comes from a permutation.
This implication allows cancellations and does not assert the converse. -/
theorem exists_permutation_of_mem_support_subdivision
    (s : Simplicial.Cell K k) (r : ℤ) {u : AffineCell V k}
    (hu : u ∈ (TauCeti.AffineChain.subdivision (Simplex V) k
      (Finsupp.single (sourceVertices s) r)).support) :
    ∃ π : Equiv.Perm (Fin (k + 1)),
      u = StdSimplex.affineMapMk (R := ℝ) (sourceVertices s) ∘
        TauCeti.BarycentricSubdivision.vertex π := by
  classical
  rw [TauCeti.AffineChain.subdivision_single] at hu
  obtain ⟨π, _, hu⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hu)
  exact ⟨π, Finset.mem_singleton.mp (Finsupp.support_single_subset hu)⟩

/-- Every nonzero one-step fundamental-chain child is represented by a cell
of the same abstract barycentric subdivision. Reduction may discard children. -/
theorem fundamentalChain_one_child_represented
    (s : Simplicial.Cell K k) {u : AffineCell V k}
    (hu : u ∈ (fundamentalChain 1 s).support) :
    ∃ π : Equiv.Perm (Fin (k + 1)), ∀ w : Simplex (Fin (k + 1)),
      (AbstractSimplicialComplex.barycentricSubdivisionRealizationMap K
        (permutationPoint s π w)).1 = (StdSimplex.affineMapMk (R := ℝ) u w).weights := by
  have hu' := support_reduceModTwo_subset
    (subdivide 1 k (Finsupp.single (sourceVertices s) 1)) hu
  have hu'' : u ∈ (TauCeti.AffineChain.subdivision (Simplex V) k
      (Finsupp.single (sourceVertices s) 1)).support := by
    simpa [subdivide] using hu'
  obtain ⟨π, rfl⟩ := exists_permutation_of_mem_support_subdivision s 1 hu''
  exact ⟨π, barycentricRealization_permutationPoint s π⟩

end SharpTopologicalOverlap.Geometry.BarycentricBridge
