module

public import SharpTopologicalOverlap.Geometry.StrongGeneralPosition
public import SharpTopologicalOverlap.Geometry.TransversePlacements
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-! # Simultaneous generic placements

The finite open dense loci for G1--G4 are combined here, yielding Lemma A.2
for a finite source-simplex family and a finite family of fixed target
simplices. The target simplices and source vertex sets are actual inputs;
no triangulation or intersection-cochain existence is assumed.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Module Metric

variable {Q I : Type*} [Fintype Q] [Fintype I] {d : ℕ}
  {b : I → ℕ}

/-- G2 restricted to the specified source-simplex family. -/
def IndependentOnFamily (S : Finset (Finset Q))
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ A ∈ S, AffineIndependent ℝ (fun q : A => y q)

/-- G3 for all below-complementary source/target pairs. -/
def AvoidanceOn (S : Finset (Finset Q))
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i))
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ A ∈ S, ∀ i, A.card - 1 + b i < d →
    Disjoint (convexHull ℝ (y '' (A : Set Q))) (convexHull ℝ (range (t i).points))

/-- G4 for all source/target pairs at or above complementary dimension. -/
def SpanningOn (S : Finset (Finset Q))
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i))
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ A ∈ S, ∀ i, d ≤ A.card - 1 + b i →
    SpanningDirectionsOn (vectorSpan ℝ (range (t i).points)) A y

/-- All four placement conditions of Lemma A.2. -/
structure GenericPlacement (S : Finset (Finset Q))
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i))
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop where
  strong : StrongGeneralPositionOn S y
  independent : IndependentOnFamily S y
  avoidance : AvoidanceOn S t y
  spanning : SpanningOn S t y

omit [Fintype Q] [Fintype I] in
/-- The independently indexed source images are also pairwise distinct, as
required in G2. -/
theorem GenericPlacement.source_injective {S : Finset (Finset Q)}
    {t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)}
    {y : Q → EuclideanSpace ℝ (Fin d)} (hy : GenericPlacement S t y)
    {A : Finset Q} (hA : A ∈ S) : Function.Injective (fun q : A => y q) :=
  (hy.independent A hA).injective

omit [Fintype Q] [Fintype I] in
/-- G4 in the affine-direction formulation used for simplex intersections. -/
theorem GenericPlacement.affineDirections_span {S : Finset (Finset Q)}
    {t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)}
    {y : Q → EuclideanSpace ℝ (Fin d)} (hy : GenericPlacement S t y)
    {A : Finset Q} (hA : A ∈ S) (i : I) (hdim : d ≤ A.card - 1 + b i) :
    (affineSpan ℝ (y '' (A : Set Q))).direction ⊔
      (affineSpan ℝ (range (t i).points)).direction = ⊤ := by
  simpa only [SpanningDirectionsOn, direction_affineSpan] using hy.spanning A hA i hdim

omit [Fintype Q] in
theorem isOpen_independentOnFamily (S : Finset (Finset Q)) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | IndependentOnFamily S y} := by
  classical
  simp only [IndependentOnFamily, Set.ofPred_forall]
  apply isOpen_biInter_finset
  intro A _
  change IsOpen ((fun y : Q → EuclideanSpace ℝ (Fin d) => fun q : A => y q) ⁻¹'
    {p : A → EuclideanSpace ℝ (Fin d) | AffineIndependent ℝ p})
  exact isOpen_setOfPred_affineIndependent.preimage
    (continuous_pi fun q : A => continuous_apply (q : Q))

theorem dense_independentOnFamily (S : Finset (Finset Q))
    (hcard : ∀ A ∈ S, A.card ≤ d + 1) :
    Dense {y : Q → EuclideanSpace ℝ (Fin d) | IndependentOnFamily S y} := by
  have hd : Dense {y : Q → EuclideanSpace ℝ (Fin d) |
      GeneralPositionOn Finset.univ y} := dense_generalPosition
  apply hd.mono
  intro y hy A hA
  exact hy A (Finset.subset_univ _) (hcard A hA)

omit [Fintype I] in
private theorem target_direction_finrank
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)) (i : I) :
    finrank ℝ (vectorSpan ℝ (range (t i).points)) = b i :=
  (t i).independent.finrank_vectorSpan (Fintype.card_fin _)

/-- Every G3 condition is open and dense; there are only finitely many
source/target pairs satisfying its dimension inequality. -/
theorem open_dense_avoidanceOn (S : Finset (Finset Q))
    (hS : ∀ A ∈ S, A.Nonempty)
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | AvoidanceOn S t y} ∧
      Dense {y : Q → EuclideanSpace ℝ (Fin d) | AvoidanceOn S t y} := by
  classical
  let J := {p : S × I // p.1.1.card - 1 + b p.2 < d}
  let L (j : J) : Set (Q → EuclideanSpace ℝ (Fin d)) :=
    {y | Disjoint (convexHull ℝ (y '' (j.1.1.1 : Set Q)))
      (convexHull ℝ (range (t j.1.2).points))}
  have hL (j : J) : IsOpen (L j) ∧ Dense (L j) := by
    apply open_dense_hull_avoidance j.1.1.1 (hS _ j.1.1.2)
      (affineSpan ℝ (range (t j.1.2).points))
      ⟨(t j.1.2).points 0, (t j.1.2).mem_affineSpan_range 0⟩
    · rw [direction_affineSpan, target_direction_finrank]
      exact j.2
    · exact (Set.finite_range (t j.1.2).points).isClosed_convexHull ℝ
    · exact convexHull_subset_affineSpan _
  have heq : {y : Q → EuclideanSpace ℝ (Fin d) | AvoidanceOn S t y} = ⋂ j : J, L j := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iInter.mpr (fun j => hy _ j.1.1.2 j.1.2 j.2)
    · intro hy A hA i hdim
      exact Set.mem_iInter.mp hy ⟨(⟨A, hA⟩, i), hdim⟩
  rw [heq]
  exact ⟨isOpen_iInter_of_finite (fun j => (hL j).1),
    dense_iInter_of_isOpen (fun j => (hL j).1) (fun j => (hL j).2)⟩

/-- Every G4 condition is open and dense, on the same ambient placement
space and for all relevant source/target pairs simultaneously. -/
theorem open_dense_spanningOn (S : Finset (Finset Q))
    (hS : ∀ A ∈ S, A.Nonempty)
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | SpanningOn S t y} ∧
      Dense {y : Q → EuclideanSpace ℝ (Fin d) | SpanningOn S t y} := by
  classical
  let J := {p : S × I // d ≤ p.1.1.card - 1 + b p.2}
  let L (j : J) : Set (Q → EuclideanSpace ℝ (Fin d)) :=
    {y | SpanningDirectionsOn (vectorSpan ℝ (range (t j.1.2).points)) j.1.1.1 y}
  have hL (j : J) : IsOpen (L j) ∧ Dense (L j) := by
    refine ⟨isOpen_spanningDirectionsOn _ _ (hS _ j.1.1.2),
      dense_spanningDirectionsOn _ _ (hS _ j.1.1.2) ?_⟩
    rw [target_direction_finrank]
    exact j.2
  have heq : {y : Q → EuclideanSpace ℝ (Fin d) | SpanningOn S t y} = ⋂ j : J, L j := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iInter.mpr (fun j => hy _ j.1.1.2 j.1.2 j.2)
    · intro hy A hA i hdim
      exact Set.mem_iInter.mp hy ⟨(⟨A, hA⟩, i), hdim⟩
  rw [heq]
  exact ⟨isOpen_iInter_of_finite (fun j => (hL j).1),
    dense_iInter_of_isOpen (fun j => (hL j).1) (fun j => (hL j).2)⟩

/-- The simultaneous G1--G4 locus is open and dense. -/
theorem open_dense_genericPlacement (S : Finset (Finset Q))
    (hS : ∀ A ∈ S, A.Nonempty) (hcard : ∀ A ∈ S, A.card ≤ d + 1)
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i)) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | GenericPlacement S t y} ∧
      Dense {y : Q → EuclideanSpace ℝ (Fin d) | GenericPlacement S t y} := by
  have havoid := open_dense_avoidanceOn S hS t
  have hspan := open_dense_spanningOn S hS t
  have heq : {y : Q → EuclideanSpace ℝ (Fin d) | GenericPlacement S t y} =
      {y | StrongGeneralPositionOn S y} ∩
        ({y | IndependentOnFamily S y} ∩
          ({y | AvoidanceOn S t y} ∩ {y | SpanningOn S t y})) := by
    ext y
    exact ⟨fun h => ⟨h.strong, h.independent, h.avoidance, h.spanning⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  rw [heq]
  exact ⟨(isOpen_strongGeneralPositionOn S).inter
      ((isOpen_independentOnFamily S).inter (havoid.1.inter hspan.1)),
    (dense_strongGeneralPositionOn S).inter_of_isOpen_left
      ((dense_independentOnFamily S hcard).inter_of_isOpen_left
        (havoid.2.inter_of_isOpen_left hspan.2 havoid.1)
        (isOpen_independentOnFamily S)) (isOpen_strongGeneralPositionOn S)⟩

/-- Lemma A.2: perturb any finite placement arbitrarily little while meeting
all four generic-placement conditions for the designated source and target
simplices at once. -/
theorem exists_genericPlacement (S : Finset (Finset Q))
    (hS : ∀ A ∈ S, A.Nonempty) (hcard : ∀ A ∈ S, A.card ≤ d + 1)
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i))
    (y : Q → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d), (∀ q, ‖z q - y q‖ < ε) ∧
      GenericPlacement S t z := by
  obtain ⟨z, hz, hgeneric⟩ :=
    Metric.dense_iff.mp (open_dense_genericPlacement S hS hcard t).2 y ε hε
  exact ⟨z, fun q => by
    simpa only [dist_eq_norm] using (dist_pi_lt_iff hε).mp hz q, hgeneric⟩

end SharpTopologicalOverlap.Geometry
