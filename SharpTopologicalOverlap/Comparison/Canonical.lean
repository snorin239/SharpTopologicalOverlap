module

import all TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
import all TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
import all TauCeti.AlgebraicTopology.Cellular.Chains
import all TauCeti.AlgebraicTopology.Singular.Relative

public import SharpTopologicalOverlap.Comparison.CellularBasis
public import SharpTopologicalOverlap.Comparison.Induction

/-! # The homology map of the canonical affine comparison

The cellular generator identification is transported through the checked
cellular--singular comparison. All maps below retain their actual affine
generators.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Convexity Topology Topology.RelCWComplex
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V] [Fintype V]
  {K : AbstractSimplicialComplex V} {n : ℕ}

local instance : CWComplex (Set.univ : Set K.Realization) :=
  AbstractSimplicialComplex.realizationCWComplex K

/-- The affine chain map corestricted to the actual coordinate realization. -/
def affineChainComplexMapIn (K : AbstractSimplicialComplex V) :
    TauCeti.orderedSimplicialChainComplex K Coeff ⟶
      (TauCeti.singularChains Coeff).obj
        (TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex)) :=
  ChainComplex.ofHom (fun n =>
    eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
      ModuleCat.ofHom (affineChainMapIn K n)) fun n => by
    simp only [TauCeti.orderedSimplicialChainComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact boundary_affineChainMapIn c

theorem affineChainComplexMapIn_f (K : AbstractSimplicialComplex V) (n : ℕ) :
    (affineChainComplexMapIn K).f n =
      eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
        ModuleCat.ofHom (affineChainMapIn K n) := rfl

theorem affineChainComplexMapIn_apply (K : AbstractSimplicialComplex V) (n : ℕ)
    (c : Chain K n) : (affineChainComplexMapIn K).f n
      ((eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n).symm) c) =
        affineChainMapIn K n c := by
  rw [affineChainComplexMapIn_f, ← ModuleCat.comp_apply, ← Category.assoc]
  simp only [eqToHom_trans, eqToHom_refl]
  erw [Category.id_comp]
  rfl

omit [Fintype V] in
theorem orderedComplex_boundary_apply (K : AbstractSimplicialComplex V) (n : ℕ)
    (c : Chain K (n + 1)) :
    (eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n))
      ((TauCeti.orderedSimplicialChainComplex K Coeff).d (n + 1) n
        ((eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff (n + 1)).symm) c)) =
          boundary n c := by
  simp only [TauCeti.orderedSimplicialChainComplex_d, ModuleCat.comp_apply]
  rfl

abbrev coordinatesToRealization (K : AbstractSimplicialComplex V) :
    TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex) ⟶ TopCat.of K.Realization :=
  (TopCat.isoOfHomeo (realizedComplexHomeomorph K)).inv

def affineRealizationChains (K : AbstractSimplicialComplex V) (n : ℕ) :
    Chain K n →ₗ[Coeff] Singular.Chain (TopCat.of K.Realization) n :=
  (Singular.pushforward (coordinatesToRealization K) n).comp (affineChainMapIn K n)

/-- The same canonical map with TauCeti's weak realization as target. -/
def affineRealizationComplexMap (K : AbstractSimplicialComplex V) :
    TauCeti.orderedSimplicialChainComplex K Coeff ⟶
      (TauCeti.singularChains Coeff).obj (TopCat.of K.Realization) :=
  affineChainComplexMapIn K ≫ (TauCeti.singularChains Coeff).map (coordinatesToRealization K)

def affineRealizationSimplex (s : Cell K n) :
    (TopCat.toSSet.obj (TopCat.of K.Realization)) _⦋n⦌ :=
  ((TopCat.of K.Realization).toSSetObjEquiv _).symm (affineRealizationMap s)

@[simp] theorem affineRealizationChains_single (s : Cell K n) (r : Coeff) :
    affineRealizationChains K n (Finsupp.single s r) =
      TauCeti.simplexChain (affineRealizationSimplex s) r := by
  rw [affineRealizationChains, LinearMap.comp_apply, affineChainMapIn_single]
  change ((TauCeti.singularChains Coeff).map (coordinatesToRealization K)).f n
    (TauCeti.simplexChain (affineSimplexIn s) r) = _
  rw [TauCeti.singularChains_map_f_simplexChain]
  congr 1

theorem affineRealizationComplexMap_f (K : AbstractSimplicialComplex V) (n : ℕ) :
    (affineRealizationComplexMap K).f n =
      eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
        ModuleCat.ofHom (affineRealizationChains K n) := by
  rfl

/-- Affine chains in the skeleton of their degree. -/
def affineSkeletalChains (K : AbstractSimplicialComplex V) (n : ℕ) :
    Chain K n →ₗ[Coeff]
      Singular.Chain (TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 1)) n :=
  Finsupp.linearCombination Coeff (fun s => TauCeti.simplexChain (affineSkeletalSimplex s) 1)

@[simp] theorem affineSkeletalChains_single (s : Cell K n) (r : Coeff) :
    affineSkeletalChains K n (Finsupp.single s r) =
      TauCeti.simplexChain (affineSkeletalSimplex s) r := by
  rw [affineSkeletalChains, Finsupp.linearCombination_single]
  exact (TauCeti.simplexChain_eq_smul _ r).symm

abbrev skeletalInclusion (K : AbstractSimplicialComplex V) (j : ℕ) :
    TauCeti.skeletonObj (Set.univ : Set K.Realization) j ⟶ TopCat.of K.Realization :=
  TopCat.ofHom (ContinuousMap.subtypeVal _)

@[simp] theorem pushforward_affineSkeletalSimplex (s : Cell K n) :
    (TopCat.toSSet.map (skeletalInclusion K (n + 1))).app _ (affineSkeletalSimplex s) =
      affineRealizationSimplex s := by
  apply ((TopCat.of K.Realization).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  rfl

theorem pushforward_affineSkeletalChains (c : Chain K n) :
    Singular.pushforward (skeletalInclusion K (n + 1)) n (affineSkeletalChains K n c) =
      affineRealizationChains K n c := by
  have he : (Singular.pushforward (skeletalInclusion K (n + 1)) n).comp
      (affineSkeletalChains K n) = affineRealizationChains K n := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, affineSkeletalChains_single,
      affineRealizationChains_single]
    exact (TauCeti.singularChains_map_f_simplexChain _ _ _).trans
      (congrArg (fun σ => TauCeti.simplexChain σ (1 : Coeff)) (pushforward_affineSkeletalSimplex s))
  exact LinearMap.congr_fun he c

theorem boundary_affineSkeletalChains (c : Chain K (n + 1)) :
    Singular.boundary n (affineSkeletalChains K (n + 1) c) =
      Singular.pushforward (TauCeti.skeletonPair (Set.univ : Set K.Realization) (n + 1)).map n
        (affineSkeletalChains K n (boundary n c)) := by
  have he : (Singular.boundary n).comp (affineSkeletalChains K (n + 1)) =
      (Singular.pushforward (TauCeti.skeletonPair (Set.univ : Set K.Realization) (n + 1)).map n).comp
        ((affineSkeletalChains K n).comp (boundary n)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change Singular.boundary n (affineSkeletalChains K (n + 1) (Finsupp.single s 1)) =
      Singular.pushforward (TauCeti.skeletonPair (Set.univ : Set K.Realization) (n + 1)).map n
        (affineSkeletalChains K n (boundary n (Finsupp.single s 1)))
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, affineSkeletalChains_single,
      Singular.boundary, TauCeti.singularChains_d_simplexChain, boundary_single,
      map_sum, affineSkeletalChains_single]
    simp only [← Int.cast_smul_eq_zsmul Coeff, Int.cast_pow, Int.cast_neg, Int.cast_one,
      show (-1 : Coeff) = 1 by decide, one_pow, one_smul]
    apply Finset.sum_congr rfl
    intro j _
    exact (congrArg (fun σ => TauCeti.simplexChain σ (1 : Coeff))
      (affineSkeletalSimplex_face s j)).trans
        (TauCeti.singularChains_map_f_simplexChain _ _ _).symm
  exact LinearMap.congr_fun he c

/-- The degree map in categorical form, including the ordered-complex transport. -/
def affineSkeletalDegreeMap (K : AbstractSimplicialComplex V) (n : ℕ) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).X n ⟶
      ((skeletalSingularPair K n).right.chainComplex (ModuleCat.of Coeff Coeff)).X n :=
  eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
    ModuleCat.ofHom (affineSkeletalChains K n)

theorem affineSkeletal_relative_cycle (K : AbstractSimplicialComplex V) (n : ℕ) :
    (ModuleCat.ofHom (affineSkeletalChains K n) ≫
      ((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n) ≫
        ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).d n
          ((ComplexShape.down ℕ).next n) = 0 := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).d n
    ((ComplexShape.down ℕ).next n)
      (((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n
        (affineSkeletalChains K n (Finsupp.single s 1))) = 0
  rw [affineSkeletalChains_single]
  exact ConcreteCategory.congr_hom (skeletalAffineChain_cycle s) 1

/-- The relative class of an arbitrary degree-`n` affine chain. -/
def affineSkeletalClassMap (K : AbstractSimplicialComplex V) (n : ℕ) :
    ModuleCat.of Coeff (Chain K n) ⟶
      TauCeti.cellularChainGroup (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff) n :=
  ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).liftCycles
    (ModuleCat.ofHom (affineSkeletalChains K n) ≫
      ((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n)
    ((ComplexShape.down ℕ).next n) rfl (affineSkeletal_relative_cycle K n) ≫
      ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).homologyπ n

theorem affineSkeletalClassMap_single (s : Cell K n) :
    ModuleCat.ofHom (Finsupp.lsingle s : Coeff →ₗ[Coeff] Chain K n) ≫
      affineSkeletalClassMap K n = skeletalAffineClass s := by
  unfold affineSkeletalClassMap skeletalAffineClass
  rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  congr 1
  apply (cancel_mono (((skeletalSingularPair K n).chainComplex
    (ModuleCat.of Coeff Coeff)).iCycles n)).mp
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n
      (affineSkeletalChains K n (Finsupp.single s 1)) =
    ((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n
      (TauCeti.simplexChain (affineSkeletalSimplex s) 1)
  rw [affineSkeletalChains_single]
  rfl

/-- The degree-wise class map is precisely the inverse cellular/ordered identification. -/
theorem affineSkeletalClassMap_eq (K : AbstractSimplicialComplex V) (n : ℕ) :
    affineSkeletalClassMap K n =
      (TauCeti.cellularChainRealizationLinearEquiv K Coeff n).toModuleIso.inv := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (affineSkeletalClassMap K n).hom (Finsupp.single s 1) =
    (TauCeti.cellularChainRealizationLinearEquiv K Coeff n).symm (Finsupp.single s 1)
  calc
    _ = (skeletalAffineClass s).hom 1 :=
      ConcreteCategory.congr_hom (affineSkeletalClassMap_single s) 1
    _ = TauCeti.cellularChainBasis (Set.univ : Set K.Realization) Coeff n
        ((AbstractSimplicialComplex.realizationCellEquiv K n).symm s) :=
      skeletalAffineClass_apply_eq_basis s
    _ = _ := by
      apply (TauCeti.cellularChainRealizationLinearEquiv K Coeff n).injective
      rw [LinearEquiv.apply_symm_apply]
      exact coordinates_cellularChainBasis s

theorem affineSkeletal_cycles_condition (K : AbstractSimplicialComplex V) (n : ℕ) :
    ((TauCeti.orderedSimplicialChainComplex K Coeff).iCycles n ≫
      affineSkeletalDegreeMap K n) ≫
        ((skeletalSingularPair K n).right.chainComplex (ModuleCat.of Coeff Coeff)).d n
          ((ComplexShape.down ℕ).next n) = 0 := by
  cases n with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down_Rel]), comp_zero]
  | succ n =>
    rw [ChainComplex.next_nat_succ]
    have hc := congrArg (fun f => f ≫
      eqToHom (TauCeti.orderedSimplicialChainComplex_X (K := K) Coeff n))
        ((TauCeti.orderedSimplicialChainComplex K Coeff).iCycles_d (n + 1) n)
    simp only [TauCeti.orderedSimplicialChainComplex_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.comp_id, zero_comp] at hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hz := ConcreteCategory.congr_hom hc z
    change boundary n ((eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff (n + 1)))
      ((TauCeti.orderedSimplicialChainComplex K Coeff).iCycles (n + 1) z)) = 0 at hz
    change Singular.boundary n (affineSkeletalChains K (n + 1)
      ((eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff (n + 1)))
        ((TauCeti.orderedSimplicialChainComplex K Coeff).iCycles (n + 1) z))) = 0
    rw [boundary_affineSkeletalChains, hz, map_zero, map_zero]

/-- The homology class of a simplicial cycle, taken in its actual skeleton. -/
def affineCyclesInSkeleton (K : AbstractSimplicialComplex V) (n : ℕ) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).cycles n ⟶
      TauCeti.skeletonHomology (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff)
        (n + 1) n :=
  ((skeletalSingularPair K n).right.chainComplex (ModuleCat.of Coeff Coeff)).liftCycles
    ((TauCeti.orderedSimplicialChainComplex K Coeff).iCycles n ≫ affineSkeletalDegreeMap K n)
    ((ComplexShape.down ℕ).next n) rfl (affineSkeletal_cycles_condition K n) ≫
      ((skeletalSingularPair K n).right.chainComplex (ModuleCat.of Coeff Coeff)).homologyπ n

def affineCyclesInBasePair (K : AbstractSimplicialComplex V) (n : ℕ) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).cycles n ⟶
      (TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomology
        (ModuleCat.of Coeff Coeff) n :=
  affineCyclesInSkeleton K n ≫
    (TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomologyπ
      (ModuleCat.of Coeff Coeff) n

theorem affineCyclesInSkeleton_relative (K : AbstractSimplicialComplex V) (n : ℕ) :
    affineCyclesInSkeleton K n ≫ (skeletalSingularPair K n).homologyπ
      (ModuleCat.of Coeff Coeff) n =
    (TauCeti.orderedSimplicialChainComplex K Coeff).iCycles n ≫
      eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
        affineSkeletalClassMap K n := by
  unfold affineCyclesInSkeleton affineSkeletalClassMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  conv_rhs =>
    rw [← Category.assoc, ← Category.assoc, HomologicalComplex.comp_liftCycles]
  congr 1

theorem affineCyclesInBasePair_projection (K : AbstractSimplicialComplex V) (n : ℕ) :
    affineCyclesInBasePair K n ≫
      (TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomologyMap
        (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set K.Realization) n)
          (ModuleCat.of Coeff Coeff) n =
    (TauCeti.orderedSimplicialChainComplex K Coeff).iCycles n ≫
      eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff n) ≫
        affineSkeletalClassMap K n := by
  unfold affineCyclesInBasePair
  rw [Category.assoc, ← TopPair.singularHomologyπ_naturality,
    TauCeti.skeletonBasePairToSkeletonPair_fst]
  erw [CategoryTheory.Functor.map_id, SSet.homologyMap_id, Category.id_comp]
  exact affineCyclesInSkeleton_relative K n

theorem cellularCyclesIso_hom_projection (K : AbstractSimplicialComplex V) (n : ℕ) :
    (TauCeti.cellularCyclesIso (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff) n).hom ≫
      (TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomologyMap
        (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set K.Realization) n)
          (ModuleCat.of Coeff Coeff) n =
    (TauCeti.cellularChainComplex (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff)).iCycles n ≫
      eqToHom (TauCeti.cellularChainComplex_X (Set.univ : Set K.Realization)
        (ModuleCat.of Coeff Coeff) n) := by
  apply (cancel_epi (TauCeti.cellularCyclesIso (Set.univ : Set K.Realization)
    (ModuleCat.of Coeff Coeff) n).inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc,
    TauCeti.cellularCyclesIso_inv_comp_iCycles, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- On cycles the affine map agrees with the cellular comparison's actual inverse. -/
theorem affineCyclesInBasePair_eq (K : AbstractSimplicialComplex V) (n : ℕ) :
    affineCyclesInBasePair K n =
      HomologicalComplex.cyclesMap (TauCeti.cellularChainComplexRealizationIso K Coeff).inv n ≫
        (TauCeti.cellularCyclesIso (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff) n).hom := by
  apply (cancel_mono ((TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomologyMap
    (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set K.Realization) n)
      (ModuleCat.of Coeff Coeff) n)).mp
  rw [Category.assoc, cellularCyclesIso_hom_projection, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, affineCyclesInBasePair_projection,
    affineSkeletalClassMap_eq, TauCeti.cellularChainComplexRealizationIso_inv_f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Singular chains of the realization and relative chains modulo its empty CW base. -/
def wholePairComparison (K : AbstractSimplicialComplex V) :
    (TauCeti.singularChains Coeff).obj (TopCat.of K.Realization) ⟶
      (TauCeti.complexBasePair (Set.univ : Set K.Realization)).singularChainComplex
        (ModuleCat.of Coeff Coeff) :=
  (TauCeti.singularChains Coeff).map (TopCat.isoOfHomeo (Homeomorph.Set.univ K.Realization)).inv ≫
    (TauCeti.complexBasePair (Set.univ : Set K.Realization)).singularChainComplexπ
      (ModuleCat.of Coeff Coeff)

instance isIso_wholePairComparison (K : AbstractSimplicialComplex V) :
    IsIso (wholePairComparison K) := by
  let P := TauCeti.complexBasePair (Set.univ : Set K.Realization)
  haveI : IsEmpty P.snd := inferInstance
  haveI : IsIso (P.singularChainComplexπ (ModuleCat.of Coeff Coeff)) := inferInstance
  unfold wholePairComparison
  infer_instance

def affineWholePairComplexMap (K : AbstractSimplicialComplex V) :
    TauCeti.orderedSimplicialChainComplex K Coeff ⟶
      (TauCeti.complexBasePair (Set.univ : Set K.Realization)).singularChainComplex
        (ModuleCat.of Coeff Coeff) :=
  affineRealizationComplexMap K ≫ wholePairComparison K

theorem affineSkeletalDegreeMap_pushforward (K : AbstractSimplicialComplex V) (n : ℕ) :
    affineSkeletalDegreeMap K n ≫
      ((TauCeti.singularChains Coeff).map (skeletalInclusion K (n + 1))).f n =
        (affineRealizationComplexMap K).f n := by
  rw [affineRealizationComplexMap_f]
  unfold affineSkeletalDegreeMap
  rw [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact pushforward_affineSkeletalChains c

/-- The map to the whole pair factors through the skeleton of each source degree. -/
theorem affineWholePairComplexMap_f (K : AbstractSimplicialComplex V) (n : ℕ) :
    (affineWholePairComplexMap K).f n = affineSkeletalDegreeMap K n ≫
      ((TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularChainComplexπ
        (ModuleCat.of Coeff Coeff)).f n ≫
      (TopPair.singularChainComplexMap
        (TauCeti.skeletonBasePairToComplex (Set.univ : Set K.Realization) n)
          (ModuleCat.of Coeff Coeff)).f n := by
  let f := TauCeti.skeletonBasePairToComplex (Set.univ : Set K.Realization) n
  have hπ := congrArg (fun g => g.f n)
    (TopPair.singularChainComplexπ_pair_naturality f (ModuleCat.of Coeff Coeff))
  simp only [HomologicalComplex.comp_f] at hπ
  have hf : TopPair.Hom.fst f = skeletalInclusion K (n + 1) ≫
      (TopCat.isoOfHomeo (Homeomorph.Set.univ K.Realization)).inv := by
    rw [TauCeti.skeletonBasePairToComplex_fst]
    ext x
    rfl
  symm
  erw [← hπ]
  change affineSkeletalDegreeMap K n ≫
    (((TauCeti.singularChains Coeff).map (TopPair.Hom.fst f)).f n ≫
      ((TauCeti.complexBasePair (Set.univ : Set K.Realization)).singularChainComplexπ
        (ModuleCat.of Coeff Coeff)).f n) = _
  rw [hf, (TauCeti.singularChains Coeff).map_comp, HomologicalComplex.comp_f,
    ← Category.assoc, ← Category.assoc, affineSkeletalDegreeMap_pushforward]
  rfl

theorem affineWholePair_on_cycles (K : AbstractSimplicialComplex V) (n : ℕ) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).homologyπ n ≫
      HomologicalComplex.homologyMap (affineWholePairComplexMap K) n =
    affineCyclesInBasePair K n ≫
      (TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n).singularHomologyMap
        (TauCeti.skeletonBasePairToComplex (Set.univ : Set K.Realization) n)
          (ModuleCat.of Coeff Coeff) n := by
  let P := TauCeti.skeletonBasePair (Set.univ : Set K.Realization) n
  let f := TauCeti.skeletonBasePairToComplex (Set.univ : Set K.Realization) n
  let g := TopPair.singularChainComplexMap f (ModuleCat.of Coeff Coeff)
  have hmaps : P.singularHomologyπ (ModuleCat.of Coeff Coeff) n ≫
      P.singularHomologyMap f (ModuleCat.of Coeff Coeff) n =
    HomologicalComplex.homologyMap (P.singularChainComplexπ (ModuleCat.of Coeff Coeff) ≫ g) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
  rw [HomologicalComplex.homologyπ_naturality, affineCyclesInBasePair, Category.assoc, hmaps]
  unfold affineCyclesInSkeleton
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  apply (cancel_mono (((TauCeti.complexBasePair (Set.univ : Set K.Realization)).singularChainComplex
    (ModuleCat.of Coeff Coeff)).iCycles n)).mp
  rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [affineWholePairComplexMap_f]

/-- The actual affine map induces the existing cellular--singular comparison. -/
theorem homologyMap_affineWholePair_eq (K : AbstractSimplicialComplex V) (n : ℕ) :
    HomologicalComplex.homologyMap (affineWholePairComplexMap K) n =
      HomologicalComplex.homologyMap (TauCeti.cellularChainComplexRealizationIso K Coeff).inv n ≫
        (TauCeti.cellularSingularHomologyIso (Set.univ : Set K.Realization)
          (ModuleCat.of Coeff Coeff) n).hom := by
  apply (cancel_epi ((TauCeti.orderedSimplicialChainComplex K Coeff).homologyπ n)).mp
  rw [affineWholePair_on_cycles, affineCyclesInBasePair_eq]
  simp only [Category.assoc]
  rw [← TauCeti.homologyπ_comp_cellularSingularHomologyIso_hom, ← Category.assoc,
    ← HomologicalComplex.homologyπ_naturality]
  exact Category.assoc _ _ _

instance isIso_homologyMap_affineWholePairComplexMap (K : AbstractSimplicialComplex V) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (affineWholePairComplexMap K) n) := by
  rw [homologyMap_affineWholePair_eq]
  infer_instance

instance isIso_homologyMap_affineRealizationComplexMap (K : AbstractSimplicialComplex V) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (affineRealizationComplexMap K) n) := by
  haveI := isIso_homologyMap_affineWholePairComplexMap K n
  change IsIso (HomologicalComplex.homologyMap
    (affineRealizationComplexMap K ≫ wholePairComparison K) n) at this
  rw [HomologicalComplex.homologyMap_comp] at this
  exact (isIso_comp_right_iff _ (HomologicalComplex.homologyMap (wholePairComparison K) n)).mp this

/-- The canonical affine comparison is a homology isomorphism, with its exact coordinate target. -/
instance isIso_homologyMap_affineChainComplexMapIn (K : AbstractSimplicialComplex V) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (affineChainComplexMapIn K) n) := by
  haveI := isIso_homologyMap_affineRealizationComplexMap K n
  change IsIso (HomologicalComplex.homologyMap
    (affineChainComplexMapIn K ≫ (TauCeti.singularChains Coeff).map (coordinatesToRealization K)) n) at this
  rw [HomologicalComplex.homologyMap_comp] at this
  exact (isIso_comp_right_iff _
    (HomologicalComplex.homologyMap ((TauCeti.singularChains Coeff).map (coordinatesToRealization K)) n)).mp this

end SharpTopologicalOverlap.Comparison
