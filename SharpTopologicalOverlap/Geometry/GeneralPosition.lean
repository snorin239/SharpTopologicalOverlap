module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Finite placements in affine general position

This proves the approximation part of condition G2 in Lemma A.2. It does not
assert the other three conditions. The induction avoids the affine spans of
all small sets of already placed vertices.

Adapted to the pinned Mathlib from
`DifferentialGeometry/Analysis/Convex/FiniteGeneralPosition.lean` at revision
`fd2f07fba4c6c102ba626c59153ad98da8f0d442`, declarations
`dense_compl_affineSubspace`, `exists_near_avoiding_affineSpans`, and
`exists_generalPositionOn`:
https://github.com/qinz1yang/differential-geometry/blob/fd2f07fba4c6c102ba626c59153ad98da8f0d442/DifferentialGeometry/Analysis/Convex/FiniteGeneralPosition.lean
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open Set Metric Topology Module

variable {d : ℕ} {Q : Type*}

/-- The complement of a proper affine subspace is dense. -/
theorem dense_compl_affineSubspace (S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : S ≠ ⊤) : Dense (S : Set (EuclideanSpace ℝ (Fin d)))ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hS
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top ⟨x, hx⟩]
  exact affineSpan_le.mpr interior_subset

/-- The bad translation vectors for two affine subspaces lie in a coset of
the sum of their directions. This is the dimension argument behind G3. -/
theorem dense_disjoint_affineSubspace_translations
    (S T : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : (S : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hT : (T : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : Module.finrank ℝ S.direction + Module.finrank ℝ T.direction < d) :
    Dense {c : EuclideanSpace ℝ (Fin d) |
      Disjoint ((fun x => c + x) '' (S : Set (EuclideanSpace ℝ (Fin d)))) T} := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  let U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) :=
    AffineSubspace.mk' (t - s) (S.direction ⊔ T.direction)
  have hU : U ≠ ⊤ := by
    intro htop
    have hdir : S.direction ⊔ T.direction = ⊤ := by
      have h := congrArg AffineSubspace.direction htop
      simpa only [U, AffineSubspace.direction_mk', AffineSubspace.direction_top] using h
    have hle := Submodule.finrank_add_le_finrank_add_finrank S.direction T.direction
    rw [hdir, finrank_top, finrank_euclideanSpace_fin] at hle
    omega
  apply (dense_compl_affineSubspace U hU).mono
  intro c hc
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ hcy
  apply hc
  change c ∈ AffineSubspace.mk' (t - s) (S.direction ⊔ T.direction)
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have h₁ : c + y - t ∈ T.direction := T.vsub_mem_direction hcy ht
  have h₂ : y - s ∈ S.direction := S.vsub_mem_direction hy hs
  have hmem : (c + y - t) - (y - s) ∈ S.direction ⊔ T.direction :=
    Submodule.sub_mem _ (Submodule.mem_sup_right h₁) (Submodule.mem_sup_left h₂)
  convert hmem using 1; abel

/-- Arbitrarily small translations simultaneously separate finitely many
below-complementary pairs. Individual bad loci are closed proper cosets. -/
theorem exists_small_disjoint_affineSubspace_translations {ι : Type*} [Fintype ι]
    (S T : ι → AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ i, (S i : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hT : ∀ i, (T i : Set (EuclideanSpace ℝ (Fin d))).Nonempty)
    (hdim : ∀ i, Module.finrank ℝ (S i).direction +
      Module.finrank ℝ (T i).direction < d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : EuclideanSpace ℝ (Fin d), ‖c‖ < ε ∧
      ∀ i, Disjoint ((fun x => c + x) '' (S i : Set (EuclideanSpace ℝ (Fin d)))) (T i) := by
  classical
  choose s hs using hS
  choose t ht using hT
  let U (i : ι) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) :=
    AffineSubspace.mk' (t i - s i) ((S i).direction ⊔ (T i).direction)
  have hU (i : ι) : U i ≠ ⊤ := by
    intro htop
    have hdir : (S i).direction ⊔ (T i).direction = ⊤ := by
      have h := congrArg AffineSubspace.direction htop
      simpa only [U, AffineSubspace.direction_mk', AffineSubspace.direction_top] using h
    have hle := Submodule.finrank_add_le_finrank_add_finrank (S i).direction (T i).direction
    rw [hdir, finrank_top, finrank_euclideanSpace_fin] at hle
    have := hdim i
    omega
  have hopen (i : ι) : IsOpen (U i : Set (EuclideanSpace ℝ (Fin d)))ᶜ :=
    (AffineSubspace.closed_of_finiteDimensional _).isOpen_compl
  have hdense (i : ι) : Dense (U i : Set (EuclideanSpace ℝ (Fin d)))ᶜ :=
    dense_compl_affineSubspace _ (hU i)
  obtain ⟨c, hc, havoid⟩ := (dense_iInter_of_isOpen hopen hdense).inter_open_nonempty
    (ball 0 ε) isOpen_ball ⟨0, mem_ball_self hε⟩
  refine ⟨c, by simpa only [mem_ball, dist_zero_right] using hc, ?_⟩
  intro i
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ hcy
  have hcU := Set.mem_iInter.mp havoid i
  apply hcU
  change c ∈ AffineSubspace.mk' (t i - s i) ((S i).direction ⊔ (T i).direction)
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have h₁ : c + y - t i ∈ (T i).direction := (T i).vsub_mem_direction hcy (ht i)
  have h₂ : y - s i ∈ (S i).direction := (S i).vsub_mem_direction hy (hs i)
  have hmem : (c + y - t i) - (y - s i) ∈ (S i).direction ⊔ (T i).direction :=
    Submodule.sub_mem _ (Submodule.mem_sup_right h₁) (Submodule.mem_sup_left h₂)
  convert hmem using 1; abel

/-- Avoid all affine spans of at most `d` previously placed vertices while
staying arbitrarily close to a specified point. -/
theorem exists_near_avoiding_affineSpans (s : Finset Q)
    (y : Q → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z, ‖z - x‖ < ε ∧ ∀ t : Finset Q, t ⊆ s → t.card ≤ d →
      z ∉ affineSpan ℝ (y '' (t : Set Q)) := by
  classical
  let T := s.powerset.filter (fun t => t.card ≤ d)
  let F (t : T) : Set (EuclideanSpace ℝ (Fin d)) :=
    (affineSpan ℝ (y '' (t.1 : Set Q)) : Set (EuclideanSpace ℝ (Fin d)))ᶜ
  have hopen (t : T) : IsOpen (F t) :=
    (AffineSubspace.closed_of_finiteDimensional _).isOpen_compl
  have hdense (t : T) : Dense (F t) := by
    apply dense_compl_affineSubspace
    apply affineSpan_image_ne_top_of_encard_le_finrank ℝ t.1.finite_toSet
    have ht : t.1.card ≤ d := (Finset.mem_filter.mp t.2).2
    simpa using (show (t.1.card : ℕ∞) ≤ d by exact_mod_cast ht)
  obtain ⟨z, hz, havoid⟩ := (dense_iInter_of_isOpen hopen hdense).inter_open_nonempty
    (ball x ε) isOpen_ball ⟨x, mem_ball_self hε⟩
  refine ⟨z, mem_ball_iff_norm.mp hz, ?_⟩
  intro t hts htd
  exact mem_iInter.mp havoid
    ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, htd⟩⟩

/-- All subsets with at most `d + 1` elements have independent image points. -/
def GeneralPositionOn (s : Finset Q) (y : Q → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t : Finset Q, t ⊆ s → t.card ≤ d + 1 → AffineIndependent ℝ (fun i : t => y i)

private theorem affineIndependent_update_insert [DecidableEq Q] {s : Finset Q} {a : Q}
    (ha : a ∉ s) {y : Q → EuclideanSpace ℝ (Fin d)}
    (hy : AffineIndependent ℝ (fun i : s => y i)) {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ∉ affineSpan ℝ (y '' (s : Set Q))) :
    AffineIndependent ℝ (fun i : (insert a s : Finset Q) => Function.update y a z i) := by
  have heq : Set.EqOn y (Function.update y a z) (s : Set Q) := by
    intro i hi
    exact (Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _).symm
  have hu : AffineIndepOn ℝ (Function.update y a z) (s : Set Q) :=
    (show AffineIndepOn ℝ y (s : Set Q) from hy).congr heq
  have himage : Function.update y a z '' (s : Set Q) = y '' (s : Set Q) :=
    Set.image_congr heq.symm
  have hnot : Function.update y a z a ∉
      affineSpan ℝ (Function.update y a z '' (s : Set Q)) := by
    rw [Function.update_self, himage]
    exact hz
  change AffineIndepOn ℝ (Function.update y a z) (↑(insert a s) : Set Q)
  rw [Finset.coe_insert]
  exact hu.insert hnot

/-- Perturb a finite set of vertices into general position, with individual
positive error tolerances and all vertices outside that set fixed. -/
theorem exists_generalPositionOn (s : Finset Q)
    (y : Q → EuclideanSpace ℝ (Fin d)) (ε : Q → ℝ) (hε : ∀ i ∈ s, 0 < ε i) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d),
      (∀ i ∈ s, ‖z i - y i‖ < ε i) ∧ (∀ i ∉ s, z i = y i) ∧
      GeneralPositionOn s z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨y, by simp, by simp, ?_⟩
    intro t ht _
    have : t = ∅ := Finset.subset_empty.mp ht
    subst t
    exact affineIndependent_of_subsingleton ℝ _
  | @insert a s ha ih =>
    obtain ⟨z, hz, hfix, hgp⟩ := ih (fun i hi => hε i (Finset.mem_insert_of_mem hi))
    obtain ⟨p, hpnear, hpavoid⟩ := exists_near_avoiding_affineSpans s z (y a)
      (hε a (Finset.mem_insert_self a s))
    refine ⟨Function.update z a p, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hpnear
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
        exact hz i hi
    · intro i hi
      have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a s)
      rw [Function.update_of_ne hia]
      exact hfix i (fun his => hi (Finset.mem_insert_of_mem his))
    · intro t ht hcard
      by_cases hat : a ∈ t
      · have hts : t.erase a ⊆ s := by
          intro i hi
          have hi' := Finset.mem_erase.mp hi
          exact (Finset.mem_insert.mp (ht hi'.2)).resolve_left hi'.1
        have htcard : (t.erase a).card ≤ d := by
          rw [Finset.card_erase_of_mem hat]
          have := Finset.card_pos.mpr ⟨a, hat⟩
          omega
        have hind := affineIndependent_update_insert (Finset.notMem_erase a t)
          (hgp (t.erase a) hts (by omega)) (hpavoid (t.erase a) hts htcard)
        exact (congrArg (fun S : Finset Q => AffineIndependent ℝ
          (fun i : S => Function.update z a p i)) (Finset.insert_erase hat)).mp hind
      · have hts : t ⊆ s := by
          intro i hi
          exact (Finset.mem_insert.mp (ht hi)).resolve_left (fun h => hat (h ▸ hi))
        have heq : (fun i : t => Function.update z a p i) = (fun i : t => z i) := by
          funext i
          have hia : (i : Q) ≠ a := fun h => hat (h ▸ i.2)
          exact Function.update_of_ne hia _ _
        rw [heq]
        exact hgp t hts hcard

/-- A finite placement can be approximated uniformly by one satisfying G2
simultaneously for every source simplex with at most `d + 1` vertices. -/
theorem exists_generalPosition [Fintype Q] (y : Q → EuclideanSpace ℝ (Fin d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Q → EuclideanSpace ℝ (Fin d), (∀ i, ‖z i - y i‖ < ε) ∧
      ∀ s : Finset Q, s.card ≤ d + 1 → AffineIndependent ℝ (fun i : s => z i) := by
  obtain ⟨z, hz, _, hgp⟩ := exists_generalPositionOn Finset.univ y (fun _ => ε)
    (fun _ _ => hε)
  exact ⟨z, fun i => hz i (Finset.mem_univ i),
    fun s hs => hgp s (Finset.subset_univ s) hs⟩

/-- G2 is open in the finite placement space. -/
theorem isOpen_generalPosition [Fintype Q] :
    IsOpen {y : Q → EuclideanSpace ℝ (Fin d) | GeneralPositionOn Finset.univ y} := by
  classical
  simp only [GeneralPositionOn, Finset.subset_univ, true_implies, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro s
  apply isOpen_iInter_of_finite
  intro _
  change IsOpen ((fun y : Q → EuclideanSpace ℝ (Fin d) => fun i : s => y i) ⁻¹'
    {p : s → EuclideanSpace ℝ (Fin d) | AffineIndependent ℝ p})
  exact isOpen_setOfPred_affineIndependent.preimage
    (continuous_pi fun i : s => continuous_apply (i : Q))

/-- G2 is dense in the finite placement space. -/
theorem dense_generalPosition [Fintype Q] :
    Dense {y : Q → EuclideanSpace ℝ (Fin d) | GeneralPositionOn Finset.univ y} := by
  classical
  apply Metric.dense_iff.mpr
  intro y ε hε
  obtain ⟨z, hz, hgp⟩ := exists_generalPosition y hε
  refine ⟨z, ?_, fun t _ ht => hgp t ht⟩
  exact (dist_pi_lt_iff hε).mpr (fun i => by simpa only [dist_eq_norm] using hz i)

end SharpTopologicalOverlap.Geometry
