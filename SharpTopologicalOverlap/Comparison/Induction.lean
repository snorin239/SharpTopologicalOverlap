module

public import SharpTopologicalOverlap.Comparison.DegreeZero

/-! # The supported inverse, conditional on the canonical homology comparison

The input below is precisely injectivity and surjectivity of the affine map
on homology of each carrier. No instance of that input is supplied here.
The construction proves the remaining algebraic induction of Lemma 2.4.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Simplicial

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V]

abbrev FullChain (V : Type) (k : ℕ) := Chain (⊤ : AbstractSimplicialComplex V) k

/-- The unaugmented cycle convention on simplicial chains. -/
def IsSimplicialCycle (k : ℕ) : FullChain V k → Prop :=
  Nat.rec (motive := fun j => FullChain V j → Prop) (fun _ => True)
    (fun j _ c => boundary j c = 0) k

/-- The unaugmented cycle convention on singular chains. -/
def IsSingularCycle (k : ℕ) : SingularChain V k → Prop :=
  Nat.rec (motive := fun j => SingularChain V j → Prop) (fun _ => True)
    (fun j _ c => singularBoundary j c = 0) k

omit [LinearOrder V] [Fintype V] [Nonempty V] in
theorem isSingularCycle_boundary (k : ℕ) (c : SingularChain V (k + 1)) :
    IsSingularCycle k (singularBoundary k c) := by
  cases k with
  | zero => trivial
  | succ k => exact Singular.boundary_boundary c

omit [Fintype V] [Nonempty V] in
theorem isSingularCycle_affine_iff (k : ℕ) (c : FullChain V k) :
    IsSingularCycle k (affineChainMap k c) ↔ IsSimplicialCycle k c := by
  cases k with
  | zero => rfl
  | succ k =>
    change singularBoundary k (affineChainMap (k + 1) c) = 0 ↔ boundary k c = 0
    rw [singularBoundary_affineChainMap]
    exact affineChainMap_injective.eq_iff' (map_zero _)

/-- The two chain-level consequences of the canonical homology isomorphism.
These remain explicit inputs until Theorem 2.3 has been proved for the affine map. -/
structure CanonicalHomologyComparison (V : Type) [LinearOrder V] where
  injectivity : ∀ (L : PreAbstractSimplicialComplex V) (k : ℕ) (c : FullChain V k),
    CarriedBy L c → IsSimplicialCycle k c →
    (∃ w : SingularChain V (k + 1), Singular.CarriedBy (realizedComplex L) w ∧
      singularBoundary k w = affineChainMap k c) →
    ∃ t : FullChain V (k + 1), CarriedBy L t ∧ boundary k t = c
  surjectivity : ∀ (L : PreAbstractSimplicialComplex V) (k : ℕ) (z : SingularChain V k),
    Singular.CarriedBy (realizedComplex L) z → IsSingularCycle k z →
    ∃ (b : FullChain V k) (q : SingularChain V (k + 1)),
      CarriedBy L b ∧ IsSimplicialCycle k b ∧ Singular.CarriedBy (realizedComplex L) q ∧
      singularBoundary k q = z + affineChainMap k b

/-- One degree of the inverse construction, retaining homotopy only on cycles.
This suffices to construct the next degree and avoids dependent finite-stage records. -/
structure ComparisonStage (V : Type) [LinearOrder V] (k : ℕ) where
  rho : SingularChain V k →ₗ[Coeff] FullChain V k
  Q : SingularChain V k →ₗ[Coeff] SingularChain V (k + 1)
  rho_carried : ∀ (L : PreAbstractSimplicialComplex V) (c : SingularChain V k),
    Singular.CarriedBy (realizedComplex L) c → CarriedBy L (rho c)
  Q_carried : ∀ (L : PreAbstractSimplicialComplex V) (c : SingularChain V k),
    Singular.CarriedBy (realizedComplex L) c → Singular.CarriedBy (realizedComplex L) (Q c)
  cycle_homotopy : ∀ (c : SingularChain V k), IsSingularCycle k c →
    singularBoundary k (Q c) = affineChainMap k (rho c) + c

/-- The unconditional, normalized base degree. -/
def zeroStage (x : V) : ComparisonStage V 0 where
  rho := rhoZero x
  Q := QZero x
  rho_carried := rhoZero_carriedBy x
  Q_carried := QZero_carriedBy x
  cycle_homotopy := fun c _ => singularBoundary_QZero x c

theorem coeff_add_self {M : Type*} [AddCommGroup M] [Module Coeff M] (c : M) : c + c = 0 := by
  have ht : (1 + 1 : Coeff) = 0 := by decide
  simpa only [ht, zero_smul, one_smul] using (add_smul (1 : Coeff) 1 c).symm

/-- The choices required on one new singular generator. -/
structure GeneratorStep (k : ℕ) (old : ComparisonStage V k)
    (s : Singular.Simplex (TopCat.of (Simplex V)) (k + 1)) where
  rho : FullChain V (k + 1)
  Q : SingularChain V (k + 2)
  rho_carried : CarriedBy (simplexCarrier s) rho
  Q_carried : Singular.CarriedBy (realizedComplex (simplexCarrier s)) Q
  boundary_rho : boundary k rho = old.rho (singularBoundary k (TauCeti.simplexChain s 1))
  boundary_Q : singularBoundary (k + 1) Q =
    TauCeti.simplexChain s 1 + old.Q (singularBoundary k (TauCeti.simplexChain s 1)) +
      affineChainMap (k + 1) rho

theorem exists_generatorStep (cmp : CanonicalHomologyComparison V)
    (k : ℕ) (old : ComparisonStage V k)
    (s : Singular.Simplex (TopCat.of (Simplex V)) (k + 1)) :
    Nonempty (GeneratorStep k old s) := by
  let c : SingularChain V (k + 1) := TauCeti.simplexChain s 1
  let L := simplexCarrier s
  have hc : Singular.CarriedBy (realizedComplex L) c := by
    apply singularSimplex_carriedBy
    rintro μ ⟨t, rfl⟩
    exact singularSimplex_mem_simplexCarrier s t
  have hcbd := Singular.carriedBy_boundary hc
  have hbdcycle := isSingularCycle_boundary k c
  have hQ := old.cycle_homotopy (singularBoundary k c) hbdcycle
  have hw : singularBoundary k (c + old.Q (singularBoundary k c)) =
      affineChainMap k (old.rho (singularBoundary k c)) := by
    rw [map_add, hQ]
    calc
      _ = affineChainMap k (old.rho (singularBoundary k c)) +
          (singularBoundary k c + singularBoundary k c) := by ac_rfl
      _ = _ := by rw [coeff_add_self, add_zero]
  have hrhocycle : IsSimplicialCycle k (old.rho (singularBoundary k c)) := by
    apply (isSingularCycle_affine_iff _ _).mp
    rw [← hw]
    exact isSingularCycle_boundary _ _
  obtain ⟨t, htL, htbd⟩ := cmp.injectivity L k (old.rho (singularBoundary k c))
    (old.rho_carried L _ hcbd) hrhocycle
    ⟨c + old.Q (singularBoundary k c),
      Singular.carriedBy_add hc (old.Q_carried L _ hcbd), hw⟩
  let z := c + old.Q (singularBoundary k c) + affineChainMap (k + 1) t
  have hzL : Singular.CarriedBy (realizedComplex L) z :=
    Singular.carriedBy_add (Singular.carriedBy_add hc (old.Q_carried L _ hcbd))
      (affineChainMap_carriedBy L t htL)
  have hzcycle : IsSingularCycle (k + 1) z := by
    change singularBoundary k z = 0
    dsimp only [z]
    rw [map_add, hw, singularBoundary_affineChainMap, htbd, coeff_add_self]
  obtain ⟨b, q, hbL, hbcycle, hqL, hqbd⟩ := cmp.surjectivity L (k + 1) z hzL hzcycle
  refine ⟨⟨t + b, q, carriedBy_add htL hbL, hqL, ?_, ?_⟩⟩
  · rw [map_add, htbd, show boundary k b = 0 from hbcycle, add_zero]
  · rw [hqbd]
    dsimp only [z]
    rw [map_add, add_assoc]

/-- Choose the already-proved simultaneous generator data. -/
def chosenGeneratorStep (cmp : CanonicalHomologyComparison V)
    (k : ℕ) (old : ComparisonStage V k)
    (s : Singular.Simplex (TopCat.of (Simplex V)) (k + 1)) : GeneratorStep k old s :=
  Classical.choice (exists_generatorStep cmp k old s)

def nextRho (cmp : CanonicalHomologyComparison V) (k : ℕ) (old : ComparisonStage V k) :
    SingularChain V (k + 1) →ₗ[Coeff] FullChain V (k + 1) :=
  TauCeti.chainsDesc fun s => (chosenGeneratorStep cmp k old s).rho

def nextQ (cmp : CanonicalHomologyComparison V) (k : ℕ) (old : ComparisonStage V k) :
    SingularChain V (k + 1) →ₗ[Coeff] SingularChain V (k + 2) :=
  TauCeti.chainsDesc fun s => (chosenGeneratorStep cmp k old s).Q

theorem chainsDesc_mem_submodule {X : TopCat.{0}} {k : ℕ} {M : Type}
    [AddCommGroup M] [Module Coeff M] (A : Set X) (P : Submodule Coeff M)
    (f : Singular.Simplex X k → M)
    (hf : ∀ s, Set.range (X.toSSetObjEquiv _ s) ⊆ A → f s ∈ P)
    (c : Singular.Chain X k) (hc : Singular.CarriedBy A c) : TauCeti.chainsDesc f c ∈ P := by
  classical
  have hc' := (Singular.carriedBy_iff_support _ _).mp hc
  rw [chain_eq_sum_simplexChain c, map_sum]
  apply P.sum_mem
  intro s hs
  rw [TauCeti.chainsDesc_simplexChain]
  exact P.smul_mem _ (hf s (hc' s hs))

theorem nextRho_carriedBy (cmp : CanonicalHomologyComparison V) (k : ℕ)
    (old : ComparisonStage V k) (L : PreAbstractSimplicialComplex V)
    (c : SingularChain V (k + 1)) (hc : Singular.CarriedBy (realizedComplex L) c) :
    CarriedBy L (nextRho cmp k old c) := by
  classical
  have hc' := (Singular.carriedBy_iff_support _ _).mp hc
  rw [carriedBy_iff_mem]
  unfold nextRho
  rw [chain_eq_sum_simplexChain c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [TauCeti.chainsDesc_simplexChain]
  apply carriedBy_smul
  exact carriedBy_mono (simplexCarrier_le s L (fun μ => hc' s hs ⟨μ, rfl⟩))
    (chosenGeneratorStep cmp k old s).rho_carried

theorem nextQ_carriedBy (cmp : CanonicalHomologyComparison V) (k : ℕ)
    (old : ComparisonStage V k) (L : PreAbstractSimplicialComplex V)
    (c : SingularChain V (k + 1)) (hc : Singular.CarriedBy (realizedComplex L) c) :
    Singular.CarriedBy (realizedComplex L) (nextQ cmp k old c) := by
  classical
  have hc' := (Singular.carriedBy_iff_support _ _).mp hc
  unfold Singular.CarriedBy nextQ
  rw [chain_eq_sum_simplexChain c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [TauCeti.chainsDesc_simplexChain]
  apply Singular.carriedBy_smul
  have hL := simplexCarrier_le s L (fun μ => hc' s hs ⟨μ, rfl⟩)
  exact Singular.carriedBy_mono (fun μ hμ => hL hμ)
    (chosenGeneratorStep cmp k old s).Q_carried

theorem boundary_nextRho (cmp : CanonicalHomologyComparison V) (k : ℕ)
    (old : ComparisonStage V k) (c : SingularChain V (k + 1)) :
    boundary k (nextRho cmp k old c) = old.rho (singularBoundary k c) := by
  have he : (boundary k).comp (nextRho cmp k old) =
      old.rho.comp (singularBoundary k) := by
    apply TauCeti.singularChains_linearMap_ext
    intro s
    simp only [LinearMap.comp_apply, nextRho, TauCeti.chainsDesc_simplexChain, one_smul]
    exact (chosenGeneratorStep cmp k old s).boundary_rho
  exact LinearMap.congr_fun he c

theorem boundary_nextQ (cmp : CanonicalHomologyComparison V) (k : ℕ)
    (old : ComparisonStage V k) (c : SingularChain V (k + 1)) :
    singularBoundary (k + 1) (nextQ cmp k old c) =
      c + old.Q (singularBoundary k c) + affineChainMap (k + 1) (nextRho cmp k old c) := by
  have he : (singularBoundary (k + 1)).comp (nextQ cmp k old) =
      LinearMap.id + old.Q.comp (singularBoundary k) +
        (affineChainMap (k + 1)).comp (nextRho cmp k old) := by
    apply TauCeti.singularChains_linearMap_ext
    intro s
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
      nextRho, nextQ, TauCeti.chainsDesc_simplexChain, one_smul]
    exact (chosenGeneratorStep cmp k old s).boundary_Q
  exact LinearMap.congr_fun he c

/-- Extend the supported comparison by one degree. -/
def nextStage (cmp : CanonicalHomologyComparison V) (k : ℕ) (old : ComparisonStage V k) :
    ComparisonStage V (k + 1) where
  rho := nextRho cmp k old
  Q := nextQ cmp k old
  rho_carried := nextRho_carriedBy cmp k old
  Q_carried := nextQ_carriedBy cmp k old
  cycle_homotopy c hc := by
    rw [boundary_nextQ, show singularBoundary k c = 0 from hc, map_zero, add_zero]
    exact add_comm _ _

def comparisonStages (cmp : CanonicalHomologyComparison V) (x : V) :
    (k : ℕ) → ComparisonStage V k :=
  Nat.rec (zeroStage x) (fun k old => nextStage cmp k old)

/-- The output of Lemma 2.4, with all degrees and simultaneous carriers explicit. -/
structure SupportedComparison (V : Type) [LinearOrder V] [Fintype V] [Nonempty V] (x : V) where
  rho : (k : ℕ) → SingularChain V k →ₗ[Coeff] FullChain V k
  boundary_rho : ∀ (k : ℕ) (c : SingularChain V (k + 1)),
    boundary k (rho (k + 1) c) = rho k (singularBoundary k c)
  carried : ∀ (L : PreAbstractSimplicialComplex V) (k : ℕ) (c : SingularChain V k),
    Singular.CarriedBy (realizedComplex L) c → CarriedBy L (rho k c)
  uniform : rho 0 (TauCeti.pointChain Coeff (SharpTopologicalOverlap.uniform : Simplex V)) =
    Finsupp.single (vertexCell x) 1

/-- Construct the full supported inverse from the specific affine homology comparison.
The canonical comparison is a hypothesis, not a project axiom. -/
def supportedComparison_of_canonicalHomology (cmp : CanonicalHomologyComparison V) (x : V) :
    SupportedComparison V x where
  rho k := (comparisonStages cmp x k).rho
  boundary_rho k c := boundary_nextRho cmp k (comparisonStages cmp x k) c
  carried L k c hc := (comparisonStages cmp x k).rho_carried L c hc
  uniform := rhoZero_uniform x

end SharpTopologicalOverlap.Comparison
