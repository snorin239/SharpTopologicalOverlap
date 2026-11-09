module

public import SharpTopologicalOverlap.Intersection
public import SharpTopologicalOverlap.Simplicial.Subcomplex
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Compatible exceptional vertex sets

The choices of disjoint support families are made once per target face.
Unions over subfaces therefore give compatible exceptional sets, as required
in Lemma 6.1 of the manuscript.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial

namespace Deletion

variable {V : Type*} [DecidableEq V]

/-- Pairwise vertex-disjoint members of a finite set family. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint s t

/-- A maximum-cardinality matching exists in every finite family. -/
theorem exists_maximumMatching (G : Finset (Finset V)) :
    ∃ M ⊆ G, IsMatching M ∧
      ∀ N ⊆ G, IsMatching N → N.card ≤ M.card := by
  classical
  let candidates := G.powerset.filter IsMatching
  have hn : candidates.Nonempty := ⟨∅, by simp [candidates, IsMatching]⟩
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card hn
  obtain ⟨hMG, hMd⟩ := Finset.mem_filter.mp hM
  refine ⟨M, Finset.mem_powerset.mp hMG, hMd, ?_⟩
  intro N hNG hNd
  exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hNG, hNd⟩)

/-- The fixed choice of a maximum matching. -/
def maximumMatching (G : Finset (Finset V)) : Finset (Finset V) :=
  (exists_maximumMatching G).choose

theorem maximumMatching_subset (G : Finset (Finset V)) : maximumMatching G ⊆ G :=
  (exists_maximumMatching G).choose_spec.1

theorem maximumMatching_isMatching (G : Finset (Finset V)) :
    IsMatching (maximumMatching G) :=
  (exists_maximumMatching G).choose_spec.2.1

theorem maximumMatching_maximum (G : Finset (Finset V))
    (N : Finset (Finset V)) (hNG : N ⊆ G) (hN : IsMatching N) :
    N.card ≤ (maximumMatching G).card :=
  (exists_maximumMatching G).choose_spec.2.2 N hNG hN

/-- Maximality makes the union of a matching a vertex cover. -/
theorem maximumMatching_hits {G : Finset (Finset V)}
    (hG : ∀ s ∈ G, s.Nonempty) {s : Finset V} (hs : s ∈ G) :
    ∃ i ∈ s, i ∈ (maximumMatching G).biUnion id := by
  classical
  by_contra h
  have hdisj : ∀ t ∈ maximumMatching G, Disjoint s t := by
    intro t ht
    apply Finset.disjoint_left.mpr
    intro i his hit
    exact h ⟨i, his, Finset.mem_biUnion.mpr ⟨t, ht, hit⟩⟩
  have hnot : s ∉ maximumMatching G := by
    intro hmem
    obtain ⟨i, hi⟩ := hG s hs
    exact Finset.disjoint_left.mp (hdisj s hmem) hi hi
  have hnew : IsMatching (insert s (maximumMatching G)) := by
    intro t ht u hu htu
    by_cases hts : t = s
    · subst t
      exact hdisj u (Finset.mem_of_mem_insert_of_ne hu htu.symm)
    · have ht' := Finset.mem_of_mem_insert_of_ne ht hts
      by_cases hus : u = s
      · subst u
        exact (hdisj t ht').symm
      · exact maximumMatching_isMatching G t ht' u
          (Finset.mem_of_mem_insert_of_ne hu hus) htu
  have hcard := maximumMatching_maximum G (insert s (maximumMatching G))
    (Finset.insert_subset hs (maximumMatching_subset G)) hnew
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

/-- A matching of bounded size in a uniform family has a bounded vertex union. -/
theorem card_matching_union_le {G : Finset (Finset V)} {r b : ℕ}
    (hG : IsUniform r G) (hb : (maximumMatching G).card ≤ b) :
    ((maximumMatching G).biUnion id).card ≤ r * b := by
  calc
    ((maximumMatching G).biUnion id).card ≤
        ∑ s ∈ maximumMatching G, s.card := Finset.card_biUnion_le
    _ = (maximumMatching G).card * r := by
      calc
        _ = ∑ _s ∈ maximumMatching G, r := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hG s (maximumMatching_subset G hs)
        _ = _ := by simp
    _ ≤ r * b := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left r hb

section Restriction

variable {U : Type*} [LinearOrder U] (Y : Finset U)

/-- Regard a simplex on a vertex subset as a simplex on the ambient vertices. -/
def subsetCell {k : ℕ}
    (s : Cell (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) k) :
    Cell (⊤ : AbstractSimplicialComplex U) k := by
  classical
  refine ⟨⟨s.1.1.image Subtype.val, ?_⟩, ?_⟩
  · change (s.1.1.image Subtype.val).Nonempty
    exact (Finset.card_pos.mp (by rw [s.2]; omega)).image _
  · rw [Finset.card_image_of_injective _ Subtype.val_injective, s.2]

@[simp] theorem subsetCell_vertices {k : ℕ}
    (s : Cell (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) k) :
    (subsetCell Y s).1.1 = s.1.1.image Subtype.val := rfl

theorem subsetCell_vertices_subset {k : ℕ}
    (s : Cell (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) k) :
    (subsetCell Y s).1.1 ⊆ Y := by
  classical
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.2

@[simp] theorem subsetCell_vertexEmbedding {k : ℕ}
    (s : Cell (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) k) (j : Fin (k + 1)) :
    (subsetCell Y s).vertexEmbedding j = (s.vertexEmbedding j).1 := by
  classical
  have ha := Finset.orderEmbOfFin_unique (subsetCell Y s).2
    (fun j => Finset.mem_image.mpr ⟨s.vertexEmbedding j, s.vertexEmbedding_mem j, rfl⟩)
    (show StrictMono (fun j => (s.vertexEmbedding j).1) from s.strictMono_vertexEmbedding)
  have hb := Finset.orderEmbOfFin_unique (subsetCell Y s).2
    (subsetCell Y s).vertexEmbedding_mem (subsetCell Y s).strictMono_vertexEmbedding
  exact congrFun (hb.trans ha.symm) j

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem subsetCell_face {k : ℕ}
    (s : Cell (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) (k + 1)) (j : Fin (k + 2)) :
    subsetCell Y (s.face j) = (subsetCell Y s).face j := by
  classical
  apply cell_vertices_injective
  change (subsetCell Y (s.face j)).1.1 = ((subsetCell Y s).face j).1.1
  rw [subsetCell_vertices, AbstractSimplicialComplex.RealizationCell.face_val,
    AbstractSimplicialComplex.RealizationCell.face_val,
    subsetCell_vertexEmbedding, subsetCell_vertices]
  ext v
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hne, hw⟩, rfl⟩
    exact ⟨fun heq => hne (Subtype.ext heq), w, hw, rfl⟩
  · rintro ⟨hne, w, hw, rfl⟩
    exact ⟨w, ⟨fun heq => hne (congrArg Subtype.val heq), hw⟩, rfl⟩

/-- Restrict an ambient cochain to the full simplex on a vertex subset. -/
def subsetCochain {k : ℕ} (a : Cochain (⊤ : AbstractSimplicialComplex U) k) :
    Cochain (⊤ : AbstractSimplicialComplex {v // v ∈ Y}) k :=
  fun s => a (subsetCell Y s)

theorem coboundary_subsetCochain {k : ℕ}
    (a : Cochain (⊤ : AbstractSimplicialComplex U) k) :
    coboundary (subsetCochain Y a) = subsetCochain Y (coboundary a) := by
  funext s
  simp only [coboundary_apply, subsetCochain, subsetCell_face]

theorem isCocycle_subsetCochain {k : ℕ}
    (a : Cochain (⊤ : AbstractSimplicialComplex U) k) (ha : IsCocycle a) :
    IsCocycle (subsetCochain Y a) := by
  unfold IsCocycle at *
  rw [coboundary_subsetCochain, ha]
  rfl

end Restriction

end Deletion

namespace IntersectionData

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}
  (I : IntersectionData T f)

/-- The cover chosen once for a target cell, rather than separately in each
larger cell containing it. -/
def localCover (p : ℕ) (η : Cell T p) : Finset (Fin n) := by
  classical
  exact if hp : p ≤ d then
    (Deletion.maximumMatching (supportFamily (I.cochain p (d - p)
      (Nat.add_sub_of_le hp) η))).biUnion id else ∅

theorem localCover_card_le {p : ℕ} (η : Cell T p) (hp : 0 < p) :
    (I.localCover p η).card ≤ (d + 1 - p) * (d / p) := by
  classical
  have hpd := I.dimension_le p η
  simp only [localCover, dite_eq_left hpd]
  apply Deletion.card_matching_union_le
  · simpa [Nat.sub_add_comm hpd] using
      supportFamily_uniform (I.cochain p (d - p) (Nat.add_sub_of_le hpd) η)
  · exact I.matching_bound p (d - p) (Nat.add_sub_of_le hpd) η hp _
      (Deletion.maximumMatching_subset _) (Deletion.maximumMatching_isMatching _)

theorem support_meets_localCover {p q : ℕ} (h : p + q = d)
    (η : Cell T p) (_hp : 0 < p) {s : Finset (Fin n)}
    (hs : s ∈ supportFamily (I.cochain p q h η)) :
    ∃ i ∈ s, i ∈ I.localCover p η := by
  classical
  have hpd := I.dimension_le p η
  have hq : q = d - p := by omega
  subst q
  simp only [localCover, dite_eq_left hpd]
  apply Deletion.maximumMatching_hits ?_ hs
  intro t ht
  exact Finset.card_pos.mp (by rw [supportFamily_uniform _ t ht]; omega)

/-- The target subfaces of a fixed degree inside a given target cell. -/
def subfaces (_I : IntersectionData T f) {p : ℕ} (τ : Cell T p) (r : ℕ) : Finset (Cell T r) := by
  classical
  exact Finset.univ.filter fun η => η.1.1 ⊆ τ.1.1

@[simp] theorem mem_subfaces {p r : ℕ} (τ : Cell T p) (η : Cell T r) :
    η ∈ I.subfaces τ r ↔ η.1.1 ⊆ τ.1.1 := by
  classical
  simp [subfaces]

theorem subfaces_card_le {p r : ℕ} (τ : Cell T p) :
    (I.subfaces τ r).card ≤ (d + 1).choose (r + 1) := by
  classical
  calc
    (I.subfaces τ r).card ≤ (τ.1.1.powersetCard (r + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun η => η.1.1)
      · intro η hη
        exact Finset.mem_powersetCard.mpr ⟨(I.mem_subfaces τ η).mp hη, η.2⟩
      · intro η _ ξ _ heq
        exact cell_vertices_injective heq
    _ = (p + 1).choose (r + 1) := by rw [Finset.card_powersetCard, τ.2]
    _ ≤ (d + 1).choose (r + 1) := Nat.choose_le_choose _ (by
      have := I.dimension_le p τ
      omega)

/-- The compatible exceptional set `S_τ`. -/
def exceptionalSet {p : ℕ} (τ : Cell T p) : Finset (Fin n) := by
  classical
  exact (Finset.Icc 1 d).biUnion fun r => (I.subfaces τ r).biUnion (I.localCover r)

theorem localCover_subset_exceptionalSet {p r : ℕ} (τ : Cell T p) (η : Cell T r)
    (hr : 0 < r) (hητ : η.1.1 ⊆ τ.1.1) :
    I.localCover r η ⊆ I.exceptionalSet τ := by
  classical
  intro i hi
  apply Finset.mem_biUnion.mpr
  refine ⟨r, Finset.mem_Icc.mpr ⟨hr, I.dimension_le r η⟩, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨η, (I.mem_subfaces τ η).mpr hητ, hi⟩

theorem exceptionalSet_mono {p r : ℕ} {τ : Cell T p} {η : Cell T r}
    (hητ : η.1.1 ⊆ τ.1.1) : I.exceptionalSet η ⊆ I.exceptionalSet τ := by
  classical
  intro i hi
  obtain ⟨s, hs, hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨ξ, hξ, hi⟩ := Finset.mem_biUnion.mp hi
  apply Finset.mem_biUnion.mpr
  refine ⟨s, hs, Finset.mem_biUnion.mpr ⟨ξ, ?_, hi⟩⟩
  exact (I.mem_subfaces τ ξ).mpr (((I.mem_subfaces η ξ).mp hξ).trans hητ)

theorem exceptionalSet_card_le {p : ℕ} (τ : Cell T p) :
    (I.exceptionalSet τ).card ≤ deletionBound d := by
  classical
  unfold exceptionalSet deletionBound
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  calc
    ((I.subfaces τ r).biUnion (I.localCover r)).card ≤
        ∑ η ∈ I.subfaces τ r, (I.localCover r η).card := Finset.card_biUnion_le
    _ ≤ ∑ _η ∈ I.subfaces τ r, (d + 1 - r) * (d / r) := by
      exact Finset.sum_le_sum fun η _ => I.localCover_card_le η hrpos
    _ = (I.subfaces τ r).card * ((d + 1 - r) * (d / r)) := by simp
    _ ≤ (d + 1).choose (r + 1) * (d + 1 - r) * (d / r) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (I.subfaces_card_le τ)

/-- The complement `Y_τ`, still as a finite subset of the source vertices. -/
def remainingVertices {p : ℕ} (τ : Cell T p) : Finset (Fin n) :=
  Finset.univ \ I.exceptionalSet τ

@[simp] theorem mem_remainingVertices {p : ℕ} (τ : Cell T p) (i : Fin n) :
    i ∈ I.remainingVertices τ ↔ i ∉ I.exceptionalSet τ := by
  classical
  simp [remainingVertices]

theorem remainingVertices_antitone {p r : ℕ} {τ : Cell T p} {η : Cell T r}
    (hητ : η.1.1 ⊆ τ.1.1) : I.remainingVertices τ ⊆ I.remainingVertices η := by
  intro i hi
  exact (I.mem_remainingVertices η i).mpr fun his =>
    ((I.mem_remainingVertices τ i).mp hi) (I.exceptionalSet_mono hητ his)

theorem remainingVertices_nonempty {p : ℕ} (τ : Cell T p)
    (hn : deletionBound d < n) : (I.remainingVertices τ).Nonempty := by
  classical
  have hcard : (I.exceptionalSet τ).card < n := (I.exceptionalSet_card_le τ).trans_lt hn
  apply Finset.card_pos.mp
  simp only [remainingVertices, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

theorem support_meets_exceptionalSet {p r q : ℕ} (τ : Cell T p) (η : Cell T r)
    (h : r + q = d) (hr : 0 < r) (hητ : η.1.1 ⊆ τ.1.1)
    {s : Finset (Fin n)} (hs : s ∈ supportFamily (I.cochain r q h η)) :
    ∃ i ∈ s, i ∈ I.exceptionalSet τ := by
  obtain ⟨i, his, hi⟩ := I.support_meets_localCover h η hr hs
  exact ⟨i, his, I.localCover_subset_exceptionalSet τ η hr hητ hi⟩

/-- Positive-dimensional cochains vanish outside the exceptional set. -/
theorem cochain_eq_zero_on_remaining {p r q : ℕ} (τ : Cell T p) (η : Cell T r)
    (h : r + q = d) (hr : 0 < r) (hητ : η.1.1 ⊆ τ.1.1)
    (s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) q)
    (hs : s.1.1 ⊆ I.remainingVertices τ) : I.cochain r q h η s = 0 := by
  by_contra hne
  obtain ⟨i, his, hi⟩ := I.support_meets_exceptionalSet τ η h hr hητ
    ((mem_supportFamily _ s).mpr hne)
  exact ((I.mem_remainingVertices τ i).mp (hs his)) hi

@[simp] theorem exceptionalSet_vertex (v : Cell T 0) : I.exceptionalSet v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨η, hη, _⟩ := Finset.mem_biUnion.mp hi
  have hsub := (I.mem_subfaces v η).mp hη
  have hc := Finset.card_le_card hsub
  rw [η.2, v.2] at hc
  have := (Finset.mem_Icc.mp hr).1
  omega

/-- The edge coboundary identity identifies vertex cochains on the complement. -/
theorem vertex_cochain_eq_on_remaining {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (v w : W) (hv : v ∈ τ.1.1) (hw : w ∈ τ.1.1)
    (s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) d)
    (hs : s.1.1 ⊆ I.remainingVertices τ) :
    I.cochain 0 d (Nat.zero_add d) (AbstractSimplicialComplex.RealizationCell.vertex T v) s =
      I.cochain 0 d (Nat.zero_add d) (AbstractSimplicialComplex.RealizationCell.vertex T w) s := by
  classical
  cases d with
  | zero => omega
  | succ k =>
    suffices hordered : ∀ v w : W, v ∈ τ.1.1 → w ∈ τ.1.1 → v < w →
        I.cochain 0 (k + 1) (Nat.zero_add _) (AbstractSimplicialComplex.RealizationCell.vertex T v) s =
        I.cochain 0 (k + 1) (Nat.zero_add _) (AbstractSimplicialComplex.RealizationCell.vertex T w) s by
      rcases lt_trichotomy v w with h | h | h
      · exact hordered v w hv hw h
      · subst w; rfl
      · exact (hordered w v hw hv h).symm
    intro v w hv hw hvw
    let c := AbstractSimplicialComplex.RealizationCell.vertex T v
    have hlt : ∀ z ∈ c.1.1, z < w := by simpa [c] using hvw
    have hedge : insert w c.1.1 ∈ T := by
      apply T.isRelLowerSet_faces.mem_of_le τ.1.2
      · simpa [c] using Finset.insert_subset hw (Finset.singleton_subset_iff.mpr hv)
      · exact Finset.insert_nonempty _ _
    let e := c.cone w hlt hedge
    have hesub : e.1.1 ⊆ τ.1.1 := by
      simpa [e, AbstractSimplicialComplex.RealizationCell.cone_val, c] using
        Finset.insert_subset hw (Finset.singleton_subset_iff.mpr hv)
    have hcb := congrFun (I.facet_coboundary 0 k (by omega) e) s
    have hzero : coboundary (I.cochain 1 k (by omega) e) s = 0 := by
      rw [coboundary_apply]
      apply Finset.sum_eq_zero
      intro j _
      apply I.cochain_eq_zero_on_remaining τ e (by omega) (by omega) hesub (s.face j)
      exact (s.face_val_subset j).trans hs
    rw [hzero] at hcb
    simp only [Finset.sum_apply] at hcb
    change 0 = ∑ j : Fin 2, I.cochain 0 (k + 1) _ (e.face j) s at hcb
    rw [Fin.sum_univ_two] at hcb
    have hlast : e.face 1 = c := by
      exact AbstractSimplicialComplex.RealizationCell.face_cone_last c w hlt hedge
    have hfirst : e.face 0 = AbstractSimplicialComplex.RealizationCell.vertex T w :=
      AbstractSimplicialComplex.RealizationCell.face_cone_zero c w hlt hedge
    rw [hfirst, hlast] at hcb
    change (0 : Coeff) = _ + _ at hcb
    have htwo : ∀ x y : Coeff, 0 = x + y → y = x := by decide
    exact htwo _ _ hcb

/-- The common family `G_τ`, represented in the fixed ambient vertex type. -/
def restrictedFamily {p : ℕ} (τ : Cell T p) : Finset (Finset (Fin n)) := by
  classical
  exact (upwardSupport I.cochain τ).filter fun s => s ⊆ I.remainingVertices τ

@[simp] theorem mem_restrictedFamily {p : ℕ} (τ : Cell T p) (s : Finset (Fin n)) :
    s ∈ I.restrictedFamily τ ↔ s ∈ upwardSupport I.cochain τ ∧
      s ⊆ I.remainingVertices τ := by
  classical
  simp [restrictedFamily]

theorem restrictedFamily_uniform {p : ℕ} (τ : Cell T p) :
    IsUniform (d + 1) (I.restrictedFamily τ) := by
  intro s hs
  exact upwardSupport_uniform _ τ s ((I.mem_restrictedFamily τ s).mp hs).1

theorem restrictedFamily_subset_upwardSupport {p : ℕ} (τ : Cell T p) :
    I.restrictedFamily τ ⊆ upwardSupport I.cochain τ :=
  fun s hs => ((I.mem_restrictedFamily τ s).mp hs).1

theorem restrictedFamily_card_le_overlap {p : ℕ} (τ : Cell T p) :
    (I.restrictedFamily τ).card ≤ overlap f :=
  (Finset.card_le_card (I.restrictedFamily_subset_upwardSupport τ)).trans
    (I.upwardSupport_card_le_overlap τ)

/-- On a remaining source face, upward support is exactly the support of any
one vertex cochain of the target face. -/
theorem mem_restrictedFamily_iff_vertex {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (v : W) (hv : v ∈ τ.1.1)
    (s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) d)
    (hs : s.1.1 ⊆ I.remainingVertices τ) :
    s.1.1 ∈ I.restrictedFamily τ ↔
      I.cochain 0 d (Nat.zero_add d) (AbstractSimplicialComplex.RealizationCell.vertex T v) s ≠ 0 := by
  classical
  rw [mem_restrictedFamily, and_iff_left hs, mem_upwardSupport, and_iff_right s.2]
  constructor
  · rintro ⟨r, q, h, η, hητ, s', hs', hss⟩
    by_cases hr : r = 0
    · subst r
      have hq : q = d := by omega
      subst q
      have hcard := supportFamily_uniform (I.cochain 0 d h η) s' hs'
      have heq : s' = s.1.1 := Finset.eq_of_subset_of_card_le hss (by omega)
      subst s'
      have hne := (mem_supportFamily (I.cochain 0 d h η) s).mp hs'
      have hη := η.eq_vertex
      rw [hη] at hne
      have hmem : η.vertexEmbedding 0 ∈ τ.1.1 := hητ (η.vertexEmbedding_mem 0)
      rw [I.vertex_cochain_eq_on_remaining τ hd (η.vertexEmbedding 0) v hmem hv s hs] at hne
      exact hne
    · obtain ⟨i, his', hi⟩ := I.support_meets_exceptionalSet τ η h (by omega) hητ hs'
      exact False.elim (((I.mem_remainingVertices τ i).mp (hs (hss his'))) hi)
  · intro hne
    refine ⟨0, d, Nat.zero_add d, AbstractSimplicialComplex.RealizationCell.vertex T v, ?_,
      s.1.1, (mem_supportFamily _ s).mpr hne, Finset.Subset.refl _⟩
    simpa using Finset.singleton_subset_iff.mpr hv

/-- The common cocycle on the actual finite type `Y_τ`. -/
def remainingCochain {p : ℕ} (τ : Cell T p) :
    Cochain (⊤ : AbstractSimplicialComplex {i // i ∈ I.remainingVertices τ}) d :=
  Deletion.subsetCochain (I.remainingVertices τ)
    (I.cochain 0 d (Nat.zero_add d)
      (AbstractSimplicialComplex.RealizationCell.vertex T (τ.vertexEmbedding 0)))

theorem remainingCochain_isCocycle {p : ℕ} (τ : Cell T p) :
    IsCocycle (I.remainingCochain τ) :=
  Deletion.isCocycle_subsetCochain _ _ (I.vertex_cocycle _)

/-- The cocycle family on `Y_τ`, with its vertices reindexed only internally. -/
def remainingFamily {p : ℕ} (τ : Cell T p) :
    Finset (Finset {i // i ∈ I.remainingVertices τ}) :=
  supportFamily (I.remainingCochain τ)

theorem remainingFamily_uniform {p : ℕ} (τ : Cell T p) :
    IsUniform (d + 1) (I.remainingFamily τ) :=
  supportFamily_uniform _

theorem remainingFamily_hasCocycleParity {p : ℕ} (τ : Cell T p) :
    HasCocycleParity (d + 1) (I.remainingFamily τ) :=
  (isCocycle_full_iff_parity _).mp (I.remainingCochain_isCocycle τ)

/-- Reindexing the common cocycle gives exactly the ambient family `G_τ`. -/
theorem mem_remainingFamily_iff {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (s : Cell (⊤ : AbstractSimplicialComplex {i // i ∈ I.remainingVertices τ}) d) :
    s.1.1 ∈ I.remainingFamily τ ↔
      s.1.1.image Subtype.val ∈ I.restrictedFamily τ := by
  rw [remainingFamily, mem_supportFamily]
  exact (I.mem_restrictedFamily_iff_vertex τ hd (τ.vertexEmbedding 0)
    (τ.vertexEmbedding_mem 0) (Deletion.subsetCell _ s)
    (Deletion.subsetCell_vertices_subset _ s)).symm

/-- The subtype and ambient presentations of `G_τ` agree as finite families. -/
theorem remainingFamily_image {p : ℕ} (τ : Cell T p) (hd : 0 < d) :
    (I.remainingFamily τ).image (Finset.image Subtype.val) = I.restrictedFamily τ := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    let c : Cell (⊤ : AbstractSimplicialComplex {i // i ∈ I.remainingVertices τ}) d :=
      ⟨⟨t, by change t.Nonempty; exact Finset.card_pos.mp (by
        rw [I.remainingFamily_uniform τ t ht]; omega)⟩, I.remainingFamily_uniform τ t ht⟩
    exact (I.mem_remainingFamily_iff τ hd c).mp ht
  · intro hs
    have hsub := ((I.mem_restrictedFamily τ s).mp hs).2
    let t := s.subtype (· ∈ I.remainingVertices τ)
    have himage : t.image Subtype.val = s := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_subtype.mp hj
      · intro hi
        exact Finset.mem_image.mpr ⟨⟨i, hsub hi⟩, Finset.mem_subtype.mpr hi, rfl⟩
    have hcard : t.card = d + 1 := by
      rw [← Finset.card_image_of_injective t Subtype.val_injective, himage]
      exact I.restrictedFamily_uniform τ s hs
    let c : Cell (⊤ : AbstractSimplicialComplex {i // i ∈ I.remainingVertices τ}) d :=
      ⟨⟨t, by change t.Nonempty; exact Finset.card_pos.mp (by rw [hcard]; omega)⟩, hcard⟩
    refine Finset.mem_image.mpr ⟨t, (I.mem_remainingFamily_iff τ hd c).mpr ?_, himage⟩
    change t.image Subtype.val ∈ I.restrictedFamily τ
    rwa [himage]

end IntersectionData

end SharpTopologicalOverlap
