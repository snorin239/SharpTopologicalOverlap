module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import SharpTopologicalOverlap.Geometry.PlacementAvoidance

/-! # Independent translations in strong general position

For one fixed family of affine subspaces, all translations producing a common
point lie in a single proper affine subspace of the product translation space.
Its direction is the image of `(x, (vᵢ)) ↦ (x - vᵢ)` and therefore has dimension
at most `d + ∑ i, dim Sᵢ`. This is the dimension argument for G1 of Lemma A.2.
-/

@[expose] public noncomputable section

open Set Metric Topology Module

namespace SharpTopologicalOverlap.Geometry

private theorem dense_compl_proper_affineSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : AffineSubspace ℝ E) (hS : S ≠ ⊤) : Dense (S : Set E)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hS
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top ⟨x, hx⟩]
  exact affineSpan_le.mpr interior_subset

variable {I : Type*} [Fintype I] {d : ℕ}

/-- The linear parameterization of the direction of the bad translation locus. -/
def translationDifference
    (S : I → AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))) :
    (EuclideanSpace ℝ (Fin d) × (∀ i, (S i).direction)) →ₗ[ℝ]
      (I → EuclideanSpace ℝ (Fin d)) where
  toFun p i := p.1 - p.2 i
  map_add' p q := by
    funext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Submodule.coe_add]
    abel
  map_smul' r p := by
    funext i
    simp [smul_sub]

/-- Independent translations avoiding a common point are dense under the
dimension hypothesis of G1. The conclusion excludes affine-hull intersections,
which is stronger than excluding convex-hull intersections. -/
theorem dense_independent_affineSubspace_translations
    (S : I → AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ i, (S i : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : d + ∑ i, finrank ℝ (S i).direction < Fintype.card I * d) :
    Dense {c : I → EuclideanSpace ℝ (Fin d) |
      ¬ ∃ x, ∀ i, x ∈ (fun y => c i + y) '' (S i : Set (EuclideanSpace ℝ (Fin d)))} := by
  classical
  choose s hs using hS
  let U : AffineSubspace ℝ (I → EuclideanSpace ℝ (Fin d)) :=
    AffineSubspace.mk' (fun i => -s i) (translationDifference S).range
  have hdom : finrank ℝ (EuclideanSpace ℝ (Fin d) × (∀ i, (S i).direction)) =
      d + ∑ i, finrank ℝ (S i).direction := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, finrank_euclideanSpace_fin]
  have hcod : finrank ℝ (I → EuclideanSpace ℝ (Fin d)) = Fintype.card I * d := by
    rw [Module.finrank_pi_fintype]
    simp
  have hU : U ≠ ⊤ := by
    intro htop
    have hdir : (translationDifference S).range = ⊤ := by
      have h := congrArg AffineSubspace.direction htop
      simpa only [U, AffineSubspace.direction_mk', AffineSubspace.direction_top] using h
    have hle := (translationDifference S).finrank_range_le
    rw [hdir, finrank_top, hdom, hcod] at hle
    omega
  apply (dense_compl_proper_affineSubspace U hU).mono
  intro c hc hcommon
  obtain ⟨x, hx⟩ := hcommon
  choose y hy hxy using hx
  apply hc
  change c ∈ AffineSubspace.mk' (fun i => -s i) (translationDifference S).range
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  refine ⟨(x, fun i => ⟨y i - s i, (S i).vsub_mem_direction (hy i) (hs i)⟩), ?_⟩
  funext i
  have hi := hxy i
  dsimp only [translationDifference, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst,
    Prod.snd, Pi.sub_apply, Pi.neg_apply]
  rw [← hi]
  simp only
  abel

/-- The translations in the preceding theorem can be chosen arbitrarily small. -/
theorem exists_small_independent_affineSubspace_translations
    (S : I → AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ i, (S i : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : d + ∑ i, finrank ℝ (S i).direction < Fintype.card I * d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : I → EuclideanSpace ℝ (Fin d), (∀ i, ‖c i‖ < ε) ∧
      ¬ ∃ x, ∀ i, x ∈ (fun y => c i + y) '' (S i : Set (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨c, hc, hsep⟩ :=
    (dense_independent_affineSubspace_translations S hS hdim).inter_open_nonempty
      (ball 0 ε) isOpen_ball ⟨0, mem_ball_self hε⟩
  have hc' : ‖c‖ < ε := by simpa only [mem_ball, dist_zero_right] using hc
  exact ⟨c, fun i => (norm_le_pi_norm c i).trans_lt hc', hsep⟩

section SourceFamily

variable {Q : Type*}

/-- Translate each member of a disjoint source-vertex family independently,
fixing all other source vertices. -/
def translateDisjointFamily (A : I → Finset Q)
    (c : I → EuclideanSpace ℝ (Fin d)) (y : Q → EuclideanSpace ℝ (Fin d))
    (q : Q) : EuclideanSpace ℝ (Fin d) := by
  classical
  exact if h : ∃ i, q ∈ A i then c h.choose + y q else y q

theorem translateDisjointFamily_on (A : I → Finset Q)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (c : I → EuclideanSpace ℝ (Fin d)) (y : Q → EuclideanSpace ℝ (Fin d))
    {i : I} {q : Q} (hq : q ∈ A i) :
    translateDisjointFamily A c y q = c i + y q := by
  classical
  have h : ∃ j, q ∈ A j := ⟨i, hq⟩
  have hi : h.choose = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis hne) h.choose_spec hq
  simp only [translateDisjointFamily, dite_eq_left h, hi]

/-- One fixed disjoint source family can be perturbed arbitrarily little so
that its affine hulls have no common point, under the strict G1 inequality. -/
theorem exists_perturb_disjoint_family_affineSpans
    (A : I → Finset Q) (hA : ∀ i, (A i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hI : 2 ≤ Fintype.card I)
    (hdim : ∑ i, ((A i).card - 1) < d * (Fintype.card I - 1))
    (y : Q → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d),
      (∀ q, ‖z q - y q‖ < ε) ∧
      ¬ ∃ x, ∀ i, x ∈ affineSpan ℝ (z '' (A i : Set Q)) := by
  classical
  let S (i : I) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) :=
    affineSpan ℝ (y '' (A i : Set Q))
  have hS (i : I) : (S i : Set (EuclideanSpace ℝ (Fin d))).Nonempty := by
    obtain ⟨q, hq⟩ := hA i
    exact ⟨y q, subset_affineSpan ℝ _ ⟨q, hq, rfl⟩⟩
  have hrank (i : I) : finrank ℝ (S i).direction ≤ (A i).card - 1 := by
    dsimp only [S]
    rw [direction_affineSpan, ← Finset.coe_image]
    apply finrank_vectorSpan_image_finset_le ℝ y (A i)
    have hpos : 1 ≤ (A i).card := (Finset.card_pos.mpr (hA i))
    exact (Nat.sub_add_cancel hpos).symm
  have hcard : Fintype.card I * d = d + d * (Fintype.card I - 1) := by
    have heq : Fintype.card I - 1 + 1 = Fintype.card I := Nat.sub_add_cancel (by omega)
    calc
      Fintype.card I * d = (Fintype.card I - 1 + 1) * d := by rw [heq]
      _ = d + d * (Fintype.card I - 1) := by ring
  have hdim' : d + ∑ i, finrank ℝ (S i).direction < Fintype.card I * d := by
    rw [hcard]
    exact Nat.add_lt_add_left ((Finset.sum_le_sum (fun i _ => hrank i)).trans_lt hdim) d
  obtain ⟨c, hc, hsep⟩ := exists_small_independent_affineSubspace_translations S hS hdim' hε
  let z := translateDisjointFamily A c y
  refine ⟨z, ?_, ?_⟩
  · intro q
    by_cases h : ∃ i, q ∈ A i
    · have hz : z q = c h.choose + y q := by
        simp only [z, translateDisjointFamily, dite_eq_left h]
      rw [hz, add_sub_cancel_right]
      exact hc h.choose
    · simp only [z, translateDisjointFamily, dite_eq_right h, sub_self, norm_zero]
      exact hε
  · rintro ⟨x, hx⟩
    apply hsep
    refine ⟨x, fun i => ?_⟩
    let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) (c i)).toAffineMap
    have himage : z '' (A i : Set Q) = f '' (y '' (A i : Set Q)) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨y q, ⟨q, hq, rfl⟩, (translateDisjointFamily_on A hdis c y hq).symm⟩
      · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨q, hq, translateDisjointFamily_on A hdis c y hq⟩
    have hxi : x ∈ (S i).map f := by
      change x ∈ (affineSpan ℝ (y '' (A i : Set Q))).map f
      rw [AffineSubspace.map_span, ← himage]
      exact hx i
    exact hxi

end SourceFamily

section Openness

variable {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Convexity.ConvexSpace.ofModule

omit [Fintype I] in
/-- The common intersection of one fixed finite family of moving source hulls
is empty on an open set of placements. -/
theorem isOpen_no_common_hulls [Nonempty I] (A : I → Finset Q) :
    IsOpen {y : Q → E |
      ¬ ∃ x, ∀ i, x ∈ convexHull ℝ (y '' (A i : Set Q))} := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let F (i : I) : (Q → E) × (∀ i, Simplex (A i)) → E :=
    fun z => ∑ q : A i, (z.2 i).weights q • z.1 q
  have hF (i : I) : Continuous (F i) :=
    continuous_finsetSum _ (fun q _ =>
      ((continuous_coordinate q).comp ((continuous_apply i).comp continuous_snd)).smul
        ((continuous_apply (q : Q)).comp continuous_fst))
  let B : Set ((Q → E) × (∀ i, Simplex (A i))) := {z | ∀ i, F i z = F i₀ z}
  have hB : IsClosed B := by
    simp only [B, Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (hF i) (hF i₀))
  have hclosed : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  have hrange (y : Q → E) (i : I) :
      y '' (A i : Set Q) = Set.range (fun q : A i => y q) := by
    ext p
    simp
  have heq : {y : Q → E | ¬ ∃ x, ∀ i, x ∈ convexHull ℝ (y '' (A i : Set Q))} =
      (Prod.fst '' B)ᶜ := by
    ext y
    constructor
    · intro hy hbad
      obtain ⟨⟨z, w⟩, hw, hzy⟩ := hbad
      change z = y at hzy
      subst z
      apply hy
      refine ⟨F i₀ (y, w), fun i => ?_⟩
      rw [hrange, convexHull_range_eq_range_affineMapMk]
      refine ⟨w i, ?_⟩
      simpa only [F, Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using hw i
    · intro hy hcommon
      obtain ⟨x, hx⟩ := hcommon
      have hw : ∀ i, ∃ w : Simplex (A i),
          Convexity.StdSimplex.affineMapMk (R := ℝ) (fun q : A i => y q) w = x := by
        intro i
        have hi := hx i
        rw [hrange, convexHull_range_eq_range_affineMapMk] at hi
        exact hi
      choose w hw using hw
      apply hy
      refine ⟨(y, w), ?_, rfl⟩
      intro i
      have hwi := hw i
      have hwi₀ := hw i₀
      simpa only [F, Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using
        hwi.trans hwi₀.symm
  rw [heq]
  exact hclosed.isOpen_compl

end Openness

section Simultaneous

variable {Q : Type*}

/-- Exactly the disjoint source families to which G1 of Lemma A.2 applies. -/
def AdmissibleStrongFamily (d : ℕ) (F : Finset (Finset Q)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ (F : Set (Finset Q)).Pairwise Disjoint ∧ 2 ≤ F.card ∧
    ∑ A ∈ F, (A.card - 1) < d * (F.card - 1)

/-- The finite list of G1 conditions for a designated source-simplex family. -/
def strongFamilies (S : Finset (Finset Q)) (d : ℕ) : Finset (Finset (Finset Q)) := by
  classical
  exact S.powerset.filter (AdmissibleStrongFamily d)

@[simp] theorem mem_strongFamilies {S : Finset (Finset Q)} {F : Finset (Finset Q)} :
    F ∈ strongFamilies S d ↔ F ⊆ S ∧ AdmissibleStrongFamily d F := by
  classical
  simp [strongFamilies]

/-- G1 on precisely the specified finite family `S` of source vertex sets. -/
def StrongGeneralPositionOn (S : Finset (Finset Q))
    (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ F ∈ strongFamilies S d,
    ¬ ∃ x, ∀ A : F, x ∈ convexHull ℝ (y '' (A.1 : Set Q))

/-- Apply G1 to an admissible subfamily, without subtype indices in the conclusion. -/
theorem StrongGeneralPositionOn.no_common_hulls
    {S : Finset (Finset Q)} {y : Q → EuclideanSpace ℝ (Fin d)}
    (hy : StrongGeneralPositionOn S y) (F : Finset (Finset Q))
    (hFS : F ⊆ S) (hF : AdmissibleStrongFamily d F) :
    ¬ ∃ x, ∀ A ∈ F, x ∈ convexHull ℝ (y '' (A : Set Q)) := by
  rintro ⟨x, hx⟩
  exact hy F (mem_strongFamilies.mpr ⟨hFS, hF⟩) ⟨x, fun A => hx A.1 A.2⟩

/-- A single admissible G1 condition is open. -/
theorem isOpen_admissibleStrongFamily (F : Finset (Finset Q))
    (hF : AdmissibleStrongFamily d F) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) |
      ¬ ∃ x, ∀ A : F, x ∈ convexHull ℝ (y '' (A.1 : Set Q))} := by
  have hne : F.Nonempty := Finset.card_pos.mp (by have := hF.2.2.1; omega)
  let : Nonempty F := hne.to_subtype
  exact isOpen_no_common_hulls (fun A : F => A.1)

/-- A single admissible G1 condition is dense in the finite placement space. -/
theorem dense_admissibleStrongFamily [Fintype Q] (F : Finset (Finset Q))
    (hF : AdmissibleStrongFamily d F) :
    Dense {y : Q → EuclideanSpace ℝ (Fin d) |
      ¬ ∃ x, ∀ A : F, x ∈ convexHull ℝ (y '' (A.1 : Set Q))} := by
  classical
  apply Metric.dense_iff.mpr
  intro y ε hε
  have hdis : Pairwise (fun A B : F => Disjoint A.1 B.1) := by
    intro A B hne
    exact hF.2.1 A.2 B.2 (fun h => hne (Subtype.ext h))
  have hcard : 2 ≤ Fintype.card F := by simpa using hF.2.2.1
  have hdim : ∑ A : F, (A.1.card - 1) < d * (Fintype.card F - 1) := by
    rw [Fintype.card_coe, Finset.sum_coe_sort F (fun A : Finset Q => A.card - 1)]
    exact hF.2.2.2
  obtain ⟨z, hz, hsep⟩ := exists_perturb_disjoint_family_affineSpans
    (fun A : F => A.1) (fun A => hF.1 A.1 A.2) hdis hcard hdim y hε
  refine ⟨z, ?_, ?_⟩
  · exact (dist_pi_lt_iff hε).mpr (fun q => by simpa only [dist_eq_norm] using hz q)
  · rintro ⟨x, hx⟩
    exact hsep ⟨x, fun A => convexHull_subset_affineSpan (𝕜 := ℝ) _ (hx A)⟩

/-- The simultaneous G1 locus for `S` is open. -/
theorem isOpen_strongGeneralPositionOn (S : Finset (Finset Q)) :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | StrongGeneralPositionOn S y} := by
  classical
  simp only [StrongGeneralPositionOn, Set.ofPred_forall]
  apply isOpen_biInter_finset
  intro F hF
  exact isOpen_admissibleStrongFamily F (mem_strongFamilies.mp hF).2

/-- All the designated G1 conditions can be met simultaneously and densely. -/
theorem dense_strongGeneralPositionOn [Fintype Q] (S : Finset (Finset Q)) :
    Dense {y : Q → EuclideanSpace ℝ (Fin d) | StrongGeneralPositionOn S y} := by
  classical
  have hopen (F : strongFamilies S d) :
      IsOpen {y : Q → EuclideanSpace ℝ (Fin d) |
        ¬ ∃ x, ∀ A : F.1, x ∈ convexHull ℝ (y '' (A.1 : Set Q))} :=
    isOpen_admissibleStrongFamily F.1 (mem_strongFamilies.mp F.2).2
  have hdense (F : strongFamilies S d) :
      Dense {y : Q → EuclideanSpace ℝ (Fin d) |
        ¬ ∃ x, ∀ A : F.1, x ∈ convexHull ℝ (y '' (A.1 : Set Q))} :=
    dense_admissibleStrongFamily F.1 (mem_strongFamilies.mp F.2).2
  have heq : {y : Q → EuclideanSpace ℝ (Fin d) | StrongGeneralPositionOn S y} =
      ⋂ F : strongFamilies S d,
        {y | ¬ ∃ x, ∀ A : F.1, x ∈ convexHull ℝ (y '' (A.1 : Set Q))} := by
    ext y
    simp only [StrongGeneralPositionOn, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h F => h F.1 F.2, fun h F hF => h ⟨F, hF⟩⟩
  rw [heq]
  exact dense_iInter_of_isOpen hopen hdense

/-- A prescribed placement can be perturbed uniformly to satisfy all G1
conditions for the designated source-simplex family. -/
theorem exists_strongGeneralPositionOn [Fintype Q] (S : Finset (Finset Q))
    (y : Q → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d), (∀ q, ‖z q - y q‖ < ε) ∧
      StrongGeneralPositionOn S z := by
  obtain ⟨z, hz, hgp⟩ := Metric.dense_iff.mp (dense_strongGeneralPositionOn S) y ε hε
  exact ⟨z, fun q => by
    simpa only [dist_eq_norm] using (dist_pi_lt_iff hε).mp hz q, hgp⟩

end Simultaneous

end SharpTopologicalOverlap.Geometry
