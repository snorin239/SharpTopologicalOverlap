module

public import SharpTopologicalOverlap.Comparison.Canonical
public import SharpTopologicalOverlap.Comparison.Precomplex
public import SharpTopologicalOverlap.Comparison.HomologyElements

/-! # The unconditional homology comparison on every ambient precomplex -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory
open SharpTopologicalOverlap.Simplicial

namespace SharpTopologicalOverlap.Comparison

variable {V : Type} [LinearOrder V] [Fintype V]

attribute [local instance 1] Classical.propDecidable

/-- Transport between the concrete face module and the library degree object. -/
def orderedElementEquiv (K : AbstractSimplicialComplex V) (k : ℕ) :
    Chain K k ≃ₗ[Coeff] (TauCeti.orderedSimplicialChainComplex K Coeff).X k :=
  (eqToIso (TauCeti.orderedSimplicialChainComplex_X Coeff k).symm).toLinearEquiv

omit [Fintype V] in
@[simp] theorem orderedElementEquiv_apply (K : AbstractSimplicialComplex V) (k : ℕ) (c : Chain K k) :
    orderedElementEquiv K k c = (eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff k).symm) c := rfl

omit [Fintype V] in
@[simp] theorem orderedElementEquiv_symm_apply (K : AbstractSimplicialComplex V) (k : ℕ)
    (c : (TauCeti.orderedSimplicialChainComplex K Coeff).X k) :
    (orderedElementEquiv K k).symm c = (eqToHom (TauCeti.orderedSimplicialChainComplex_X Coeff k)) c := rfl

omit [Fintype V] in
theorem orderedElement_boundary (K : AbstractSimplicialComplex V) (k : ℕ) (c : Chain K (k + 1)) :
    (TauCeti.orderedSimplicialChainComplex K Coeff).d (k + 1) k (orderedElementEquiv K (k + 1) c) =
      orderedElementEquiv K k (boundary k c) := by
  apply (orderedElementEquiv K k).symm.injective
  rw [LinearEquiv.symm_apply_apply, orderedElementEquiv_symm_apply, orderedElementEquiv_apply]
  exact orderedComplex_boundary_apply K k c

/-- The reindexed actual chains, included in the original ambient simplex. -/
def actualAmbientChainMap (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Chain (actualComplex L) k →ₗ[Coeff] FullChain V k :=
  (includeSubcomplexChain (K := (⊤ : AbstractSimplicialComplex V)) L).comp
    (actualChainEquiv L k).toLinearMap

omit [Fintype V] in
theorem actualAmbientChainMap_injective (L : PreAbstractSimplicialComplex V) (k : ℕ) :
    Function.Injective (actualAmbientChainMap L k) :=
  Subtype.val_injective.comp (actualChainEquiv L k).injective

omit [Fintype V] in
theorem actualAmbientChainMap_carried (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Chain (actualComplex L) k) : CarriedBy L (actualAmbientChainMap L k c) :=
  (actualChainEquiv L k c).2

omit [Fintype V] in
theorem boundary_actualAmbientChainMap (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Chain (actualComplex L) (k + 1)) :
    boundary k (actualAmbientChainMap L (k + 1) c) = actualAmbientChainMap L k (boundary k c) :=
  boundary_actualChainEquiv L k c

omit [Fintype V] in
theorem actualChain_cycle_d (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Chain (actualComplex L) k) :
    (TauCeti.orderedSimplicialChainComplex (actualComplex L) Coeff).d k
      ((ComplexShape.down ℕ).next k) (orderedElementEquiv (actualComplex L) k c) = 0 ↔
        IsSimplicialCycle k (actualAmbientChainMap L k c) := by
  cases k with
  | zero =>
      rw [Simplicial.chainComplex_d_zero]
      simp [IsSimplicialCycle]
  | succ k =>
      rw [ChainComplex.next_nat_succ, orderedElement_boundary]
      change orderedElementEquiv (actualComplex L) k (boundary k c) = 0 ↔
        boundary k (actualAmbientChainMap L (k + 1) c) = 0
      rw [boundary_actualAmbientChainMap]
      exact ((orderedElementEquiv (actualComplex L) k).injective.eq_iff' (map_zero _)).trans
        ((actualAmbientChainMap_injective L k).eq_iff' (map_zero _)).symm

omit [LinearOrder V] in
theorem actualSingular_cycle_d (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (c : Singular.Chain (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex)) k) :
    ((TauCeti.singularChains Coeff).obj
      (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex))).d k
        ((ComplexShape.down ℕ).next k) c = 0 ↔ IsSingularCycle k (actualSingularInclusion L k c) := by
  cases k with
  | zero =>
      have hd : ((TauCeti.singularChains Coeff).obj
          (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex))).d
          0 ((ComplexShape.down ℕ).next 0) = 0 := by
        apply HomologicalComplex.shape
        simp [ComplexShape.down_Rel]
      rw [hd]
      simp [IsSingularCycle]
  | succ k =>
      rw [ChainComplex.next_nat_succ]
      change Singular.boundary k c = 0 ↔ singularBoundary k (actualSingularInclusion L (k + 1) c) = 0
      rw [boundary_actualSingularInclusion]
      exact ((actualSingularInclusion_injective L k).eq_iff' (map_zero _)).symm

theorem canonical_injectivity (L : PreAbstractSimplicialComplex V) (k : ℕ) (c : FullChain V k)
    (hcL : CarriedBy L c) (hc : IsSimplicialCycle k c)
    (hw : ∃ w : SingularChain V (k + 1),
      Singular.CarriedBy (X := TopCat.of (Simplex V)) (realizedComplex L) w ∧
        singularBoundary k w = affineChainMap k c) :
    ∃ t : FullChain V (k + 1), CarriedBy L t ∧ boundary k t = c := by
  let cS := (actualChainEquiv L k).symm ⟨c, hcL⟩
  have hce : actualAmbientChainMap L k cS = c :=
    congrArg Subtype.val ((actualChainEquiv L k).apply_symm_apply ⟨c, hcL⟩)
  have hcS := (actualChain_cycle_d L k cS).mpr (hce.symm ▸ hc)
  obtain ⟨w, hwL, hwb⟩ := hw
  obtain ⟨wS, hwS⟩ := exists_actualSingular_lift L (k + 1) w hwL
  have hwbS : Singular.boundary k wS = affineChainMapIn (actualComplex L) k cS := by
    apply actualSingularInclusion_injective L k
    calc
      actualSingularInclusion L k (Singular.boundary k wS) =
          singularBoundary k (actualSingularInclusion L (k + 1) wS) :=
        (boundary_actualSingularInclusion L k wS).symm
      _ = affineChainMap k c := by rw [hwS, hwb]
      _ = actualSingularInclusion L k (affineChainMapIn (actualComplex L) k cS) := by
        rw [actualAffineChainMap_natural]
        exact congrArg (affineChainMap k) hce.symm
  have hwf : ∃ wS, ((TauCeti.singularChains Coeff).obj
      (TopCat.of (realizedComplex (actualComplex L).toPreAbstractSimplicialComplex))).d
        (k + 1) k wS = (affineChainComplexMapIn (actualComplex L)).f k
          (orderedElementEquiv (actualComplex L) k cS) := by
    refine ⟨wS, ?_⟩
    rw [orderedElementEquiv_apply, affineChainComplexMapIn_apply]
    exact hwbS
  obtain ⟨tX, htX⟩ := homologyMap_cycle_injective (affineChainComplexMapIn (actualComplex L)) k
    (orderedElementEquiv (actualComplex L) k cS) hcS hwf
  let tS := (orderedElementEquiv (actualComplex L) (k + 1)).symm tX
  have htS : boundary k tS = cS := by
    apply (orderedElementEquiv (actualComplex L) k).injective
    rw [← orderedElement_boundary, LinearEquiv.apply_symm_apply]
    exact htX
  refine ⟨actualAmbientChainMap L (k + 1) tS, actualAmbientChainMap_carried L _ _, ?_⟩
  rw [boundary_actualAmbientChainMap, htS]
  exact hce

theorem canonical_surjectivity (L : PreAbstractSimplicialComplex V) (k : ℕ)
    (z : SingularChain V k)
    (hzL : Singular.CarriedBy (X := TopCat.of (Simplex V)) (realizedComplex L) z)
    (hz : IsSingularCycle k z) :
    ∃ (b : FullChain V k) (q : SingularChain V (k + 1)),
      CarriedBy L b ∧ IsSimplicialCycle k b ∧
        Singular.CarriedBy (X := TopCat.of (Simplex V)) (realizedComplex L) q ∧
          singularBoundary k q = z + affineChainMap k b := by
  obtain ⟨zS, hzS⟩ := exists_actualSingular_lift L k z hzL
  have hcycle := (actualSingular_cycle_d L k zS).mpr (hzS.symm ▸ hz)
  obtain ⟨bX, hbX, qS, hqS⟩ := homologyMap_cycle_surjective (affineChainComplexMapIn (actualComplex L)) k zS hcycle
  let bS := (orderedElementEquiv (actualComplex L) k).symm bX
  have hbcast : orderedElementEquiv (actualComplex L) k bS = bX :=
    (orderedElementEquiv (actualComplex L) k).apply_symm_apply bX
  have hbS := (actualChain_cycle_d L k bS).mp (hbcast.symm ▸ hbX)
  rw [← hbcast, orderedElementEquiv_apply, affineChainComplexMapIn_apply] at hqS
  refine ⟨actualAmbientChainMap L k bS, actualSingularInclusion L (k + 1) qS,
    actualAmbientChainMap_carried L k bS, hbS,
    actualSingularInclusion_carriedBy L (k + 1) qS, ?_⟩
  rw [boundary_actualSingularInclusion, hqS, map_sub, hzS, actualAffineChainMap_natural]
  change z - affineChainMap k (actualAmbientChainMap L k bS) =
    z + affineChainMap k (actualAmbientChainMap L k bS)
  have hneg : -(affineChainMap k (actualAmbientChainMap L k bS)) =
      affineChainMap k (actualAmbientChainMap L k bS) := by
    have h := coeff_add_self (affineChainMap k (actualAmbientChainMap L k bS))
    calc
      _ = _ + (affineChainMap k (actualAmbientChainMap L k bS) +
          affineChainMap k (actualAmbientChainMap L k bS)) := by rw [h, add_zero]
      _ = _ := by abel
  rw [sub_eq_add_neg, hneg]

/-- The canonical affine comparison is injective and surjective on homology
with every vertex-omitting ambient carrier retained. -/
theorem canonicalHomologyComparison : CanonicalHomologyComparison V :=
  ⟨canonical_injectivity, canonical_surjectivity⟩

end SharpTopologicalOverlap.Comparison
