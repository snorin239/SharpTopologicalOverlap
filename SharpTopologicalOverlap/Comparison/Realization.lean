module

public import SharpTopologicalOverlap.Comparison
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-! # Comparison on the actual realized complex

The coordinate realization is identified with TauCeti's weak realization.
The affine chain map is corestricted to this actual space before considering
the homology comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Convexity
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V]

attribute [local instance] Classical.decEq

/-- Coordinate-preserving equivalence for an arbitrary abstract complex. -/
def realizedComplexEquiv (K : AbstractSimplicialComplex V) :
    K.Realization ≃ realizedComplex K.toPreAbstractSimplicialComplex where
  toFun x := ⟨⟨x.1, AbstractSimplicialComplex.Realization.nonneg _ x,
    AbstractSimplicialComplex.Realization.sum_eq_one _ x⟩,
    AbstractSimplicialComplex.support_mem _ x⟩
  invFun μ := ⟨μ.1.weights, by
    apply AbstractSimplicialComplex.mem_realization_iff.mpr
    refine ⟨support μ.1, μ.2, ?_⟩
    rw [Finset.coe_image]
    exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
      ⟨μ.1.nonneg, μ.1.total, Finset.Subset.refl _⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Convexity.StdSimplex.ext rfl)

omit [LinearOrder V] in
theorem continuous_realizedComplexEquiv [Finite V] (K : AbstractSimplicialComplex V) :
    Continuous (realizedComplexEquiv K) := by
  apply Continuous.subtype_mk
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  exact AbstractSimplicialComplex.continuous_realization_coe _

/-- TauCeti's realization and the fixed coordinate subspace have the same topology. -/
def realizedComplexHomeomorph [Finite V] (K : AbstractSimplicialComplex V) :
    K.Realization ≃ₜ realizedComplex K.toPreAbstractSimplicialComplex :=
  (realizedComplexEquiv K).toHomeomorphOfContinuousClosed
    (continuous_realizedComplexEquiv K) (continuous_realizedComplexEquiv K).isClosedMap

omit [LinearOrder V] in
@[simp] theorem realizedComplexHomeomorph_weights [Finite V]
    (K : AbstractSimplicialComplex V) (x : K.Realization) :
    (realizedComplexHomeomorph K x).1.weights = x.1 := rfl

variable {K : AbstractSimplicialComplex V} {k : ℕ}

/-- The same affine generator, now in the actual coordinate realization of `K`. -/
def affineSimplexIn (s : Cell K k) :
    (TopCat.toSSet.obj (TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex))) _⦋k⦌ :=
  ((TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex)).toSSetObjEquiv _).symm
    ⟨fun μ => ⟨(TopCat.of (Simplex V)).toSSetObjEquiv _ (affineSimplex s) μ,
      affineSimplex_mem_realizedComplex _ s s.1.2 μ⟩,
      (map_continuous ((TopCat.of (Simplex V)).toSSetObjEquiv _ (affineSimplex s))).subtype_mk _⟩

@[simp] theorem affineSimplexIn_inclusion (s : Cell K k) :
    (TopCat.toSSet.map (Singular.inclusion (realizedComplex K.toPreAbstractSimplicialComplex))).app _
      (affineSimplexIn s) = affineSimplex s := by
  apply ((TopCat.of (Simplex V)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  rfl

@[simp] theorem affineSimplexIn_face (s : Cell K (k + 1)) (j : Fin (k + 2)) :
    (TopCat.toSSet.obj (TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex))).δ j
      (affineSimplexIn s) = affineSimplexIn (s.face j) := by
  apply ((TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  apply Subtype.ext
  change (μ.map j.succAbove).map s.vertexEmbedding = μ.map (s.face j).vertexEmbedding
  rw [← StdSimplex.map_comp, AbstractSimplicialComplex.RealizationCell.vertexEmbedding_face]

/-- The linear affine comparison into singular chains of the actual realization. -/
def affineChainMapIn (K : AbstractSimplicialComplex V) (k : ℕ) :
    Chain K k →ₗ[Coeff] Singular.Chain
      (TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex)) k :=
  Finsupp.linearCombination Coeff (fun s => TauCeti.simplexChain (affineSimplexIn s) 1)

@[simp] theorem affineChainMapIn_single (s : Cell K k) (r : Coeff) :
    affineChainMapIn K k (Finsupp.single s r) = TauCeti.simplexChain (affineSimplexIn s) r := by
  rw [affineChainMapIn, Finsupp.linearCombination_single]
  exact (TauCeti.simplexChain_eq_smul _ r).symm

theorem affineChainMapIn_inclusion (c : Chain K k) :
    Singular.pushforward (Singular.inclusion (realizedComplex K.toPreAbstractSimplicialComplex)) k
      (affineChainMapIn K k c) = affineChainMap k c := by
  have he :
      (Singular.pushforward (Singular.inclusion (realizedComplex K.toPreAbstractSimplicialComplex)) k).comp
        (affineChainMapIn K k) = affineChainMap (K := K) k := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, affineChainMapIn_single,
      affineChainMap_single, Singular.pushforward, TauCeti.singularChains_map_f_simplexChain]
    exact congrArg (fun σ => TauCeti.simplexChain σ (1 : Coeff)) (affineSimplexIn_inclusion s)
  exact LinearMap.congr_fun he c

theorem boundary_affineChainMapIn (c : Chain K (k + 1)) :
    Singular.boundary k (affineChainMapIn K (k + 1) c) = affineChainMapIn K k (boundary k c) := by
  apply Singular.inclusion_injective (X := TopCat.of (Simplex V)) (k := k)
    (realizedComplex K.toPreAbstractSimplicialComplex)
  rw [← Singular.boundary_pushforward, affineChainMapIn_inclusion,
    affineChainMapIn_inclusion]
  exact singularBoundary_affineChainMap c

end SharpTopologicalOverlap.Comparison
