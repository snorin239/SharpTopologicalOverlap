module

import all TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

public import SharpTopologicalOverlap.Comparison.Cellular
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality

/-! # Naturality of the affine cellular classes -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Convexity Topology Topology.RelCWComplex
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V W : Type} [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
  {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W} {n : ℕ}

local instance : CWComplex (Set.univ : Set K.Realization) :=
  AbstractSimplicialComplex.realizationCWComplex K
local instance : CWComplex (Set.univ : Set L.Realization) :=
  AbstractSimplicialComplex.realizationCWComplex L

/-- The actual skeletal pair map induced by a simplicial map. -/
abbrev simplicialSkeletalPairMap
    (f : PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) (n : ℕ) :
    TauCeti.skeletonPair (Set.univ : Set K.Realization) n ⟶
      TauCeti.skeletonPair (Set.univ : Set L.Realization) n :=
  TauCeti.skeletonPairMap (Set.univ : Set K.Realization) (Set.univ : Set L.Realization)
    f.isCellular_realizationMap n

theorem affineSkeletalSimplex_map
    (f : PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) (s : Cell K n)
    (hf : StrictMonoOn f (↑s.1.1 : Set V)) :
    (TopPair.toSSetPair.map (simplicialSkeletalPairMap f n)).right.app _
      (affineSkeletalSimplex s) = affineSkeletalSimplex (s.map f hf.injOn) := by
  apply ((TauCeti.skeletonObj (Set.univ : Set L.Realization) (n + 1)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  simp only [simplicialSkeletalPairMap, TopPair.toSSetPair_map_right,
    TauCeti.skeletonPairMap_fst, affineSkeletalSimplex, Equiv.apply_symm_apply]
  erw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [ContinuousMap.comp_apply]
  change (TauCeti.skeletonMap (Set.univ : Set K.Realization) (Set.univ : Set L.Realization)
    f.isCellular_realizationMap (n + 1)).hom.toFun (affineSkeletalMap s μ) =
      affineSkeletalMap (s.map f hf.injOn) μ
  rw [TauCeti.skeletonMap_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (f.realizationMap (affineRealizationMap s μ)).1 =
    (affineRealizationMap (s.map f hf.injOn) μ).1
  rw [PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
    affineRealizationMap_weights, affineRealizationMap_weights,
    StdSimplex.weights_map, StdSimplex.weights_map, ← Finsupp.mapDomain_comp,
    AbstractSimplicialComplex.RealizationCell.vertexEmbedding_map s f hf]

/-- Naturality before passing from relative cycles to homology. -/
theorem skeletalAffineChain_naturality
    (f : PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) (s : Cell K n)
    (hf : StrictMonoOn f (↑s.1.1 : Set V)) :
    skeletalAffineChain s ≫
      (SSetPair.chainComplexMap (TopPair.toSSetPair.map (simplicialSkeletalPairMap f n))
        (ModuleCat.of Coeff Coeff)).f n = skeletalAffineChain (s.map f hf.injOn) := by
  let φ := TopPair.toSSetPair.map (simplicialSkeletalPairMap f n)
  have hπ := congrArg (fun g => g.f n)
    (SSetPair.chainComplexπ_naturality (ModuleCat.of Coeff Coeff) φ)
  simp only [HomologicalComplex.comp_f] at hπ
  unfold skeletalAffineChain
  rw [Category.assoc, ← hπ, ← Category.assoc, SSet.ι_chainComplexMap_f]
  exact congrArg (fun σ =>
    (skeletalSingularPair L n).right.ιChainComplex (R := ModuleCat.of Coeff Coeff) σ ≫
      ((skeletalSingularPair L n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n)
    (affineSkeletalSimplex_map f s hf)

/-- The relative affine class is natural for the actual cellular map. -/
theorem skeletalAffineClass_naturality
    (f : PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) (s : Cell K n)
    (hf : StrictMonoOn f (↑s.1.1 : Set V)) :
    skeletalAffineClass s ≫
      TauCeti.cellularChainGroupMap (Set.univ : Set K.Realization)
        (Set.univ : Set L.Realization) f.isCellular_realizationMap
          (ModuleCat.of Coeff Coeff) n = skeletalAffineClass (s.map f hf.injOn) := by
  rw [TauCeti.cellularChainGroupMap_def]
  change skeletalAffineClass s ≫
    SSetPair.homologyMap (TopPair.toSSetPair.map (simplicialSkeletalPairMap f n))
      (ModuleCat.of Coeff Coeff) n = _
  rw [skeletalAffineClass, SSetPair.homologyMap, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  unfold skeletalAffineClass
  congr 1
  apply (cancel_mono (((skeletalSingularPair L n).chainComplex (ModuleCat.of Coeff Coeff)).iCycles n)).mp
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact skeletalAffineChain_naturality f s hf

end SharpTopologicalOverlap.Comparison
