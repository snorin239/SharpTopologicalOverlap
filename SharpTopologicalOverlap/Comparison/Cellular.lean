module

public import SharpTopologicalOverlap.Comparison.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex
public import TauCeti.AlgebraicTopology.Singular.Relative

/-! # Affine generators in the cellular skeletal filtration

These are the concrete relative classes used to identify the canonical
affine comparison with TauCeti's cellular comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Convexity Topology Topology.RelCWComplex
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V] [Fintype V]
variable {K : AbstractSimplicialComplex V} {n : ℕ}

local instance : CWComplex (Set.univ : Set K.Realization) :=
  AbstractSimplicialComplex.realizationCWComplex K

/-- The affine characteristic simplex in the actual weak realization. -/
def affineRealizationMap (s : Cell K n) : C(Simplex (Fin (n + 1)), K.Realization) :=
  (⟨(realizedComplexHomeomorph K).symm,
    (realizedComplexHomeomorph K).symm.continuous⟩ :
    C(realizedComplex K.toPreAbstractSimplicialComplex, K.Realization)).comp
    ((TopCat.of (realizedComplex K.toPreAbstractSimplicialComplex)).toSSetObjEquiv _
      (affineSimplexIn s))

@[simp] theorem affineRealizationMap_weights (s : Cell K n) (μ : Simplex (Fin (n + 1))) :
    (affineRealizationMap s μ).1 = (μ.map s.vertexEmbedding).weights := rfl

theorem affineRealizationMap_mem_skeleton (s : Cell K n) (μ : Simplex (Fin (n + 1))) :
    affineRealizationMap s μ ∈
      (skeletonLT (Set.univ : Set K.Realization) ((n + 1 : ℕ) : ℕ∞) : Set K.Realization) := by
  rw [AbstractSimplicialComplex.skeletonLT_realizationCWComplex]
  change (((affineRealizationMap s μ).1.support.card : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞))
  rw [affineRealizationMap_weights]
  have hsub : (μ.map s.vertexEmbedding).weights.support ⊆ s.1.1 :=
    affineSimplex_mem_closedFace s μ
  exact_mod_cast (Finset.card_le_card hsub).trans_eq s.2

/-- The affine simplex corestricted to the skeleton of its own dimension. -/
def affineSkeletalMap (s : Cell K n) :
    C(Simplex (Fin (n + 1)), TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 1)) :=
  ⟨fun μ => ⟨affineRealizationMap s μ, affineRealizationMap_mem_skeleton s μ⟩,
    (map_continuous (affineRealizationMap s)).subtype_mk _⟩

/-- The singular simplex in the indicated skeletal stage. -/
def affineSkeletalSimplex (s : Cell K n) :
    (TopCat.toSSet.obj (TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 1))) _⦋n⦌ :=
  ((TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 1)).toSSetObjEquiv _).symm
    (affineSkeletalMap s)

/-- Each singular facet comes from the preceding skeletal stage. -/
theorem affineSkeletalSimplex_face (s : Cell K (n + 1)) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj (TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 2))).δ j
      (affineSkeletalSimplex s) =
    (TopCat.toSSet.map (TauCeti.skeletonPair (Set.univ : Set K.Realization) (n + 1)).map).app _
      (affineSkeletalSimplex (s.face j)) := by
  apply ((TauCeti.skeletonObj (Set.univ : Set K.Realization) (n + 2)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro μ
  apply Subtype.ext
  apply Subtype.ext
  change ((μ.map j.succAbove).map s.vertexEmbedding).weights =
    (μ.map (s.face j).vertexEmbedding).weights
  rw [← StdSimplex.map_comp, AbstractSimplicialComplex.RealizationCell.vertexEmbedding_face]

/-- A generator from the subspace is zero in relative chains, in every degree. -/
theorem relative_subspace_generator_zero (Q : SSetPair.{0}) (k : ℕ) (s : Q.left _⦋k⦌) :
    Q.right.ιChainComplex (R := ModuleCat.of Coeff Coeff)
      (Q.hom.app (F := Q.left) (G := Q.right) _ s) ≫
      (Q.chainComplexπ (ModuleCat.of Coeff Coeff)).f k = 0 := by
  rw [← SSet.ι_chainComplexMap_f Q.left Q.right Q.hom (ModuleCat.of Coeff Coeff) s,
    Category.assoc, Q.chainComplex_condition_f, comp_zero]

/-- The singular pair of consecutive skeleta. -/
abbrev skeletalSingularPair (K : AbstractSimplicialComplex V) (n : ℕ) : SSetPair.{0} :=
  TopPair.toSSetPair.obj (TauCeti.skeletonPair (Set.univ : Set K.Realization) n)

/-- The affine face generator projected to the appropriate relative chain module. -/
def skeletalAffineChain (s : Cell K n) :
    ModuleCat.of Coeff Coeff ⟶
      ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).X n :=
  (skeletalSingularPair K n).right.ιChainComplex (affineSkeletalSimplex s) ≫
    ((skeletalSingularPair K n).chainComplexπ (ModuleCat.of Coeff Coeff)).f n

/-- Every facet of a characteristic simplex vanishes in the relative quotient. -/
theorem skeletalAffine_facet_projection_zero (s : Cell K (n + 1)) (j : Fin (n + 2)) :
    (skeletalSingularPair K (n + 1)).right.ιChainComplex (R := ModuleCat.of Coeff Coeff)
        ((skeletalSingularPair K (n + 1)).right.δ j (affineSkeletalSimplex s)) ≫
      ((skeletalSingularPair K (n + 1)).chainComplexπ (ModuleCat.of Coeff Coeff)).f n = 0 := by
  let Q := skeletalSingularPair K (n + 1)
  let t : Q.left _⦋n⦌ := affineSkeletalSimplex (s.face j)
  have hf : Q.right.δ j (affineSkeletalSimplex s) =
      Q.hom.app (F := Q.left) (G := Q.right) _ t := affineSkeletalSimplex_face s j
  exact (congrArg (fun σ => Q.right.ιChainComplex (R := ModuleCat.of Coeff Coeff) σ ≫
    (Q.chainComplexπ (ModuleCat.of Coeff Coeff)).f n) hf).trans
      (relative_subspace_generator_zero Q n t)

/-- The projected affine simplex is a relative cycle in positive degrees. -/
theorem skeletalAffineChain_cycle_succ (s : Cell K (n + 1)) :
    skeletalAffineChain s ≫
      ((skeletalSingularPair K (n + 1)).chainComplex (ModuleCat.of Coeff Coeff)).d (n + 1) n =
        0 := by
  unfold skeletalAffineChain
  rw [Category.assoc, ((skeletalSingularPair K (n + 1)).chainComplexπ _).comm,
    ← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_eq_zero
  intro j _
  rw [skeletalAffine_facet_projection_zero, smul_zero]

/-- The same cycle convention includes degree zero with its zero outgoing differential. -/
theorem skeletalAffineChain_cycle (s : Cell K n) :
    skeletalAffineChain s ≫
      ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).d n
        ((ComplexShape.down ℕ).next n) = 0 := by
  cases n with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down_Rel]), comp_zero]
  | succ n =>
    rw [ChainComplex.next_nat_succ]
    exact skeletalAffineChain_cycle_succ s

/-- The actual affine simplex as a cellular relative homology class. -/
def skeletalAffineClass (s : Cell K n) :
    ModuleCat.of Coeff Coeff ⟶ TauCeti.cellularChainGroup
      (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff) n :=
  ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).liftCycles
    (skeletalAffineChain s) ((ComplexShape.down ℕ).next n) rfl (skeletalAffineChain_cycle s) ≫
      ((skeletalSingularPair K n).chainComplex (ModuleCat.of Coeff Coeff)).homologyπ n

/-- The affine facets, as an absolute chain in the preceding skeleton. -/
def affineFacetChain (s : Cell K (n + 1)) :
    ModuleCat.of Coeff Coeff ⟶
      ((skeletalSingularPair K (n + 1)).left.chainComplex (ModuleCat.of Coeff Coeff)).X n :=
  ∑ j : Fin (n + 2),
    (skeletalSingularPair K (n + 1)).left.ιChainComplex (affineSkeletalSimplex (s.face j))

/-- Its inclusion is the singular boundary of the original affine generator. -/
theorem affineFacetChain_boundary (s : Cell K (n + 1)) :
    affineFacetChain s ≫
      (SSet.chainComplexMap (skeletalSingularPair K (n + 1)).hom
        (ModuleCat.of Coeff Coeff)).f n =
    (skeletalSingularPair K (n + 1)).right.ιChainComplex (affineSkeletalSimplex s) ≫
      ((skeletalSingularPair K (n + 1)).right.chainComplex (ModuleCat.of Coeff Coeff)).d
        (n + 1) n := by
  rw [SSet.ιChainComplex_d]
  simp only [← Int.cast_smul_eq_zsmul Coeff, Int.cast_pow, Int.cast_neg, Int.cast_one,
    show (-1 : Coeff) = 1 by decide, one_pow, one_smul]
  unfold affineFacetChain
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [SSet.ι_chainComplexMap_f]
  exact congrArg (fun σ => (skeletalSingularPair K (n + 1)).right.ιChainComplex
    (R := ModuleCat.of Coeff Coeff) σ) (affineSkeletalSimplex_face s j).symm

/-- The affine facet chain is an absolute cycle. -/
theorem affineFacetChain_cycle (s : Cell K (n + 1)) :
    affineFacetChain s ≫
      ((skeletalSingularPair K (n + 1)).left.chainComplex (ModuleCat.of Coeff Coeff)).d n
        ((ComplexShape.down ℕ).next n) = 0 := by
  let Q := skeletalSingularPair K (n + 1)
  have hS := Q.shortExact_chainComplexShortComplex (ModuleCat.of Coeff Coeff)
  have := hS.mono_f
  rw [← cancel_mono ((SSet.chainComplexMap Q.hom (ModuleCat.of Coeff Coeff)).f
    ((ComplexShape.down ℕ).next n)), zero_comp, Category.assoc]
  have hcomm := (SSet.chainComplexMap Q.hom (ModuleCat.of Coeff Coeff)).comm n
    ((ComplexShape.down ℕ).next n)
  have hstep := congrArg (fun f => affineFacetChain s ≫ f) hcomm.symm
  refine hstep.trans ?_
  rw [← Category.assoc, affineFacetChain_boundary, Category.assoc]
  exact (congrArg (fun f => Q.right.ιChainComplex (R := ModuleCat.of Coeff Coeff)
    (affineSkeletalSimplex s) ≫ f)
      ((Q.right.chainComplex (ModuleCat.of Coeff Coeff)).d_comp_d
        (n + 1) n ((ComplexShape.down ℕ).next n))).trans (comp_zero)

/-- The connecting morphism is represented by the actual affine boundary chain. -/
theorem skeletalAffineClass_connecting (s : Cell K (n + 1)) :
    skeletalAffineClass s ≫
      (skeletalSingularPair K (n + 1)).homologyδ (ModuleCat.of Coeff Coeff) (n + 1) n =
    ((skeletalSingularPair K (n + 1)).left.chainComplex (ModuleCat.of Coeff Coeff)).liftCycles
      (affineFacetChain s) ((ComplexShape.down ℕ).next n) rfl (affineFacetChain_cycle s) ≫
        ((skeletalSingularPair K (n + 1)).left.chainComplex (ModuleCat.of Coeff Coeff)).homologyπ n := by
  let Q := skeletalSingularPair K (n + 1)
  have h := (Q.shortExact_chainComplexShortComplex (ModuleCat.of Coeff Coeff)).δ_eq
    (n + 1) n (by simp) (skeletalAffineChain s) (skeletalAffineChain_cycle_succ s)
    (Q.right.ιChainComplex (affineSkeletalSimplex s)) rfl
    (affineFacetChain s) (affineFacetChain_boundary s) ((ComplexShape.down ℕ).next n) rfl
  exact h

/-- The affine relative classes commute with the actual cellular differential. -/
theorem skeletalAffineClass_differential (s : Cell K (n + 1)) :
    skeletalAffineClass s ≫
      TauCeti.cellularDifferential (Set.univ : Set K.Realization) (ModuleCat.of Coeff Coeff) n =
        ∑ j : Fin (n + 2), skeletalAffineClass (s.face j) := by
  let Q := skeletalSingularPair K n
  rw [TauCeti.cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ, ← Category.assoc]
  change (skeletalAffineClass s ≫
    (skeletalSingularPair K (n + 1)).homologyδ (ModuleCat.of Coeff Coeff) (n + 1) n) ≫
      Q.homologyπ (ModuleCat.of Coeff Coeff) n = _
  rw [skeletalAffineClass_connecting, Category.assoc]
  change _ ≫ ((Q.right.chainComplex (ModuleCat.of Coeff Coeff)).homologyπ n ≫
    HomologicalComplex.homologyMap (Q.chainComplexπ (ModuleCat.of Coeff Coeff)) n) = _
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  have hsum : affineFacetChain s ≫ (Q.chainComplexπ (ModuleCat.of Coeff Coeff)).f n =
      ∑ j : Fin (n + 2), skeletalAffineChain (s.face j) := by
    unfold affineFacetChain skeletalAffineChain
    rw [Preadditive.sum_comp]
    rfl
  simp only [skeletalAffineClass, ← Preadditive.sum_comp]
  congr 1
  apply (cancel_mono ((Q.chainComplex (ModuleCat.of Coeff Coeff)).iCycles n)).mp
  simp only [Preadditive.sum_comp, HomologicalComplex.liftCycles_i]
  refine hsum.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact (HomologicalComplex.liftCycles_i _ _ _ _ _).symm

end SharpTopologicalOverlap.Comparison
