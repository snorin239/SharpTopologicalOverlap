module

public import SharpTopologicalOverlap.Comparison.Cellular
public import SharpTopologicalOverlap.Comparison.CellularNaturality
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Cellular.Zero

/-! # Identifying affine classes with the cellular basis

The standard simplex has one top cell. Over `𝔽₂` any nonzero top relative
class is its basis vector. Naturality and the affine boundary formula allow
the identification to be proved by induction on the dimension.
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

/-- The unique top cell of the standard simplex. -/
def standardCell (n : ℕ) : Cell (⊤ : AbstractSimplicialComplex (Fin (n + 1))) n :=
  (fullCellEquiv (Fin (n + 1)) n).symm ⟨Finset.univ, by simp⟩

theorem standardCell_unique (s : Cell (⊤ : AbstractSimplicialComplex (Fin (n + 1))) n) :
    s = standardCell n := by
  apply cell_vertices_injective
  change s.1.1 = Finset.univ
  exact Finset.eq_univ_of_card _ (by simpa using s.2)

/-- The increasing simplicial map from the standard simplex onto a given face. -/
def standardCellMap (s : Cell K n) :
    PreAbstractSimplicialComplex.SimplicialMap
      (⊤ : AbstractSimplicialComplex (Fin (n + 1))).toPreAbstractSimplicialComplex
      K.toPreAbstractSimplicialComplex where
  toFun := s.vertexEmbedding
  map_face' _τ hτ := K.isRelLowerSet_faces.mem_of_le s.1.2
    (Finset.image_subset_iff.mpr fun _ _ => s.vertexEmbedding_mem _)
    (Finset.image_nonempty.mpr hτ)

omit [Fintype V] in
theorem standardCellMap_strictMono (s : Cell K n) : StrictMono (standardCellMap s) :=
  s.strictMono_vertexEmbedding

omit [Fintype V] in
theorem standardCell_map (s : Cell K n) :
    (standardCell n).map (standardCellMap s)
      (standardCellMap_strictMono s).injective.injOn = s := by
  apply cell_vertices_injective
  change ((standardCell n).map (standardCellMap s)
    (standardCellMap_strictMono s).injective.injOn).1.1 = s.1.1
  simp only [AbstractSimplicialComplex.RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply]
  change Finset.univ.image s.vertexEmbedding = s.1.1
  exact s.image_vertexEmbedding

/-- The point underlying a zero-dimensional affine characteristic simplex. -/
def skeletalZeroPoint (s : Cell K 0) :
    TauCeti.skeletonObj (Set.univ : Set K.Realization) 1 :=
  TopCat.toSSetObj₀Equiv (affineSkeletalSimplex s)

theorem skeletalAffineClass_zero_eq (s : Cell K 0) :
    skeletalAffineClass s =
      TauCeti.singularHomology₀Section (ModuleCat.of Coeff Coeff) (skeletalZeroPoint s) ≫
        (TauCeti.skeletonPair (Set.univ : Set K.Realization) 0).singularHomologyπ
          (ModuleCat.of Coeff Coeff) 0 := by
  rw [TauCeti.singularHomology₀Section_def, SSet.ιHomology₀_eq]
  change _ = _ ≫ HomologicalComplex.homologyMap
    ((skeletalSingularPair K 0).chainComplexπ (ModuleCat.of Coeff Coeff)) 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  unfold skeletalAffineClass
  congr 1
  apply (cancel_mono (((skeletalSingularPair K 0).chainComplex
    (ModuleCat.of Coeff Coeff)).iCycles 0)).mp
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  unfold skeletalAffineChain
  congr 1
  exact congrArg (fun σ => (skeletalSingularPair K 0).right.ιChainComplex
    (R := ModuleCat.of Coeff Coeff) σ)
    (Equiv.symm_apply_apply TopCat.toSSetObj₀Equiv (affineSkeletalSimplex s)).symm

/-- No zero-dimensional affine class vanishes. -/
theorem skeletalAffineClass_zero_ne_zero (s : Cell K 0) : skeletalAffineClass s ≠ 0 := by
  let P := TauCeti.skeletonPair (Set.univ : Set K.Realization) 0
  let : IsEmpty (TauCeti.skeletonObj (Set.univ : Set K.Realization) 0) :=
    TauCeti.zeroSkeletonPreviousIsEmpty (Set.univ : Set K.Realization)
  let : IsEmpty P.snd := by
    change IsEmpty (TauCeti.skeletonObj (Set.univ : Set K.Realization) 0)
    infer_instance
  have : IsIso (P.singularHomologyπ (ModuleCat.of Coeff Coeff) 0) := inferInstance
  intro hz
  rw [skeletalAffineClass_zero_eq] at hz
  have hp : TauCeti.singularHomology₀Section (ModuleCat.of Coeff Coeff)
      (skeletalZeroPoint s) = 0 := by
    apply (cancel_mono (P.singularHomologyπ (ModuleCat.of Coeff Coeff) 0)).mp
    simpa only [zero_comp] using hz
  have hunit := TauCeti.singularHomology₀Section_singularHomology₀ε
    (ModuleCat.of Coeff Coeff) (skeletalZeroPoint s)
  rw [hp, zero_comp] at hunit
  have h01 : (0 : Coeff) = 1 := ConcreteCategory.congr_hom hunit 1
  exact zero_ne_one h01

theorem skeletalAffineClass_zero_apply_ne_zero (s : Cell K 0) :
    (skeletalAffineClass s).hom 1 ≠ 0 := by
  intro h
  apply skeletalAffineClass_zero_ne_zero s
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simpa using h

/-- Coordinates of the actual affine relative class in TauCeti's ordered-cell basis. -/
def affineClassCoordinates (s : Cell K n) : Chain K n :=
  TauCeti.cellularChainRealizationLinearEquiv K Coeff n ((skeletalAffineClass s).hom 1)

theorem standardChain_eq_single (c : Chain
    (⊤ : AbstractSimplicialComplex (Fin (n + 1))) n) :
    c = Finsupp.single (standardCell n) (c (standardCell n)) := by
  ext s
  have hs := standardCell_unique s
  subst s
  simp

theorem coeff_unit_coe_eq_one (u : Coeffˣ) : (u : Coeff) = 1 := by
  rcases (show ∀ r : Coeff, r = 0 ∨ r = 1 by decide) (u : Coeff) with h | h
  · exact (u.ne_zero h).elim
  · exact h

omit [Fintype V] in
/-- No orientation rescaling remains over `𝔽₂`. -/
theorem coordinates_cellularChainBasis (s : Cell K n) :
    TauCeti.cellularChainRealizationLinearEquiv K Coeff n
      (TauCeti.cellularChainBasis (Set.univ : Set K.Realization) Coeff n
        ((AbstractSimplicialComplex.realizationCellEquiv K n).symm s)) =
      Finsupp.single s 1 := by
  rw [TauCeti.cellularChainRealizationLinearEquiv_cellularChainBasis,
    coeff_unit_coe_eq_one]

theorem standardClassCoordinates_eq_single_of_ne_zero
    (h : (skeletalAffineClass (standardCell n)).hom 1 ≠ 0) :
    affineClassCoordinates (standardCell n) = Finsupp.single (standardCell n) 1 := by
  have hc : affineClassCoordinates (standardCell n) ≠ 0 := by
    intro hz
    apply h
    exact (TauCeti.cellularChainRealizationLinearEquiv _ Coeff n).injective
      (hz.trans (map_zero _).symm)
  have hcoeff : affineClassCoordinates (standardCell n) (standardCell n) ≠ 0 := by
    intro hz
    apply hc
    rw [standardChain_eq_single (affineClassCoordinates (standardCell n)), hz,
      Finsupp.single_zero]
  have hone : affineClassCoordinates (standardCell n) (standardCell n) = 1 := by
    exact ((show ∀ r : Coeff, r = 0 ∨ r = 1 by decide) _).resolve_left hcoeff
  rw [standardChain_eq_single (affineClassCoordinates (standardCell n)), hone]

/-- Naturality transports the standard generator identification onto any cell. -/
theorem affineClassCoordinates_eq_single_of_standard (s : Cell K n)
    (hstd : affineClassCoordinates (standardCell n) = Finsupp.single (standardCell n) 1) :
    affineClassCoordinates s = Finsupp.single s 1 := by
  let M : AbstractSimplicialComplex (Fin (n + 1)) := ⊤
  let : CWComplex (Set.univ : Set M.Realization) :=
    AbstractSimplicialComplex.realizationCWComplex M
  let f := standardCellMap s
  have hf : StrictMonoOn f (↑(standardCell n).1.1 : Set (Fin (n + 1))) :=
    (standardCellMap_strictMono s).strictMonoOn _
  have hmodel : (skeletalAffineClass (standardCell n)).hom 1 =
      TauCeti.cellularChainBasis (Set.univ : Set M.Realization) Coeff n
        ((AbstractSimplicialComplex.realizationCellEquiv M n).symm (standardCell n)) := by
    apply (TauCeti.cellularChainRealizationLinearEquiv M Coeff n).injective
    exact hstd.trans (coordinates_cellularChainBasis _).symm
  have hnat := ConcreteCategory.congr_hom
    (skeletalAffineClass_naturality f (standardCell n) hf) 1
  have hmap := TauCeti.cellularChainGroupMap_realization_cellularChainBasis Coeff
    f (standardCell n) hf
  rw [standardCell_map] at hnat hmap
  have hcell : (skeletalAffineClass s).hom 1 =
      TauCeti.cellularChainBasis (Set.univ : Set K.Realization) Coeff n
        ((AbstractSimplicialComplex.realizationCellEquiv K n).symm s) := by
    calc
      _ = (TauCeti.cellularChainGroupMap (Set.univ : Set M.Realization)
          (Set.univ : Set K.Realization) f.isCellular_realizationMap
            (ModuleCat.of Coeff Coeff) n).hom
              ((skeletalAffineClass (standardCell n)).hom 1) := hnat.symm
      _ = _ := (congrArg (fun c =>
        (TauCeti.cellularChainGroupMap (Set.univ : Set M.Realization)
          (Set.univ : Set K.Realization) f.isCellular_realizationMap
            (ModuleCat.of Coeff Coeff) n).hom c) hmodel).trans hmap
  exact (congrArg (TauCeti.cellularChainRealizationLinearEquiv K Coeff n) hcell).trans
    (coordinates_cellularChainBasis s)

omit [Fintype V] in
theorem sum_affineFacet_basis_ne_zero (s : Cell K (n + 1)) :
    (∑ j : Fin (n + 2), Finsupp.single (s.face j) (1 : Coeff)) ≠ 0 := by
  intro hz
  have h := congrArg (fun c : Chain K n => c (s.face 0)) hz
  have hinj (i j : Fin (n + 2)) : s.face i = s.face j ↔ i = j := s.face_injective.eq_iff
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, hinj, Finsupp.zero_apply] at h
  simp at h

/-- The canonical affine class is exactly the cellular generator in every dimension. -/
theorem affineClassCoordinates_eq_single (n : ℕ) :
    ∀ (U : Type) [LinearOrder U] [Fintype U] (A : AbstractSimplicialComplex U)
      (s : Cell A n), affineClassCoordinates s = Finsupp.single s 1 := by
  induction n with
  | zero =>
    intro U _ _ A s
    exact affineClassCoordinates_eq_single_of_standard s
      (standardClassCoordinates_eq_single_of_ne_zero (skeletalAffineClass_zero_apply_ne_zero _))
  | succ n ih =>
    intro U _ _ A s
    apply affineClassCoordinates_eq_single_of_standard s
    apply standardClassCoordinates_eq_single_of_ne_zero
    intro hz
    let M : AbstractSimplicialComplex (Fin (n + 2)) := ⊤
    let t : Cell M (n + 1) := standardCell (n + 1)
    let : CWComplex (Set.univ : Set M.Realization) :=
      AbstractSimplicialComplex.realizationCWComplex M
    have hsum : (∑ j : Fin (n + 2), (skeletalAffineClass (t.face j)).hom 1) = 0 := by
      have hd := ConcreteCategory.congr_hom (skeletalAffineClass_differential t) 1
      change (TauCeti.cellularDifferential (Set.univ : Set M.Realization)
          (ModuleCat.of Coeff Coeff) n).hom ((skeletalAffineClass t).hom 1) =
        (∑ j : Fin (n + 2), skeletalAffineClass (t.face j)).hom 1 at hd
      simp only [ModuleCat.hom_sum, LinearMap.sum_apply] at hd
      rw [hz, map_zero] at hd
      exact hd.symm
    have hcoords : (∑ j : Fin (n + 2), affineClassCoordinates (t.face j)) = 0 := by
      have h := congrArg (TauCeti.cellularChainRealizationLinearEquiv M Coeff n) hsum
      simpa only [map_sum, map_zero, affineClassCoordinates] using h
    have hbad : (∑ j : Fin (n + 2), Finsupp.single (t.face j) (1 : Coeff)) = 0 := by
      simpa only [ih] using hcoords
    exact sum_affineFacet_basis_ne_zero t hbad

theorem skeletalAffineClass_apply_eq_basis (s : Cell K n) :
    (skeletalAffineClass s).hom 1 =
      TauCeti.cellularChainBasis (Set.univ : Set K.Realization) Coeff n
        ((AbstractSimplicialComplex.realizationCellEquiv K n).symm s) := by
  apply (TauCeti.cellularChainRealizationLinearEquiv K Coeff n).injective
  exact (affineClassCoordinates_eq_single n V K s).trans
    (coordinates_cellularChainBasis s).symm

end SharpTopologicalOverlap.Comparison
