module

public import SharpTopologicalOverlap.Simplicial
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Group.Nat.Even

/-! # The cocycle exchange argument

The equality case in Lemma 4.1 only needs two facts about its vector labels:
labels are distinct within every edge, and each edge's label sum is zero.
The arguments here work for labels in an arbitrary additive commutative group.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Spectral

open Simplicial

variable {V A : Type*} [LinearOrder V] [AddCommGroup A]
  {k : ℕ} {G : Finset (Finset V)}

/-- A cocycle cannot have exactly one edge in a one-size-larger set. -/
theorem exists_second_edge (hG : HasCocycleParity k G) {s e : Finset V}
    (hs : s.card = k + 1) (heG : e ∈ G) (hes : e ⊆ s) :
    ∃ f ∈ G, f ⊆ s ∧ f ≠ e := by
  classical
  by_contra h
  push Not at h
  have hsingle : G.filter (fun f => f ⊆ s) = {e} := by
    ext f
    constructor
    · intro hf
      exact Finset.mem_singleton.mpr (h f (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp hf).2)
    · intro hf
      obtain rfl := Finset.mem_singleton.mp hf
      exact Finset.mem_filter.mpr ⟨heG, hes⟩
  have hpar := hG s hs
  rw [hsingle, Finset.card_singleton] at hpar
  exact Nat.not_even_one hpar

/-- A different equicardinal face inside `e ∪ {j}` replaces one vertex of `e`. -/
theorem eq_exchange_of_subset_insert {e f : Finset V} {j : V}
    (hj : j ∉ e) (hef : e.card = f.card) (hf : f ⊆ insert j e) (hne : f ≠ e) :
    ∃ i ∈ e, f = insert j (e.erase i) := by
  classical
  have hjf : j ∈ f := by
    by_contra hjf
    have hfe : f ⊆ e := by
      intro v hv
      exact (Finset.mem_insert.mp (hf hv)).resolve_left (fun hvj => hjf (hvj ▸ hv))
    exact hne (Finset.eq_of_subset_of_card_le hfe hef.le)
  have hcard : ((insert j e) \ f).card = 1 := by
    rw [Finset.card_sdiff_of_subset hf, Finset.card_insert_of_notMem hj, hef]
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hiU : i ∈ insert j e := by
    have : i ∈ (insert j e) \ f := by rw [hi]; simp
    exact (Finset.mem_sdiff.mp this).1
  have hinf : i ∉ f := by
    have : i ∈ (insert j e) \ f := by rw [hi]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hij : i ≠ j := by intro h; subst i; exact hinf hjf
  have hie : i ∈ e := (Finset.mem_insert.mp hiU).resolve_left hij
  refine ⟨i, hie, ?_⟩
  ext v
  constructor
  · intro hv
    rcases Finset.mem_insert.mp (hf hv) with rfl | hve
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hinf (h ▸ hv), hve⟩)
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hjf
    · obtain ⟨hvi, hve⟩ := Finset.mem_erase.mp hv
      by_contra hvf
      have hmem : v ∈ (insert j e) \ f :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hve, hvf⟩
      rw [hi] at hmem
      exact hvi (Finset.mem_singleton.mp hmem)

/-- A vertex outside an edge acquires its label from a unique edge vertex. -/
theorem exists_unique_label_representative (hG : IsUniform k G)
    (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0)
    {e : Finset V} (he : e ∈ G) (j : V) :
    ∃! i, i ∈ e ∧ w j = w i := by
  classical
  suffices hex : ∃ i ∈ e, w j = w i by
    obtain ⟨i, hie, hwi⟩ := hex
    refine ⟨i, ⟨hie, hwi⟩, ?_⟩
    intro z hz
    exact hinj e he hz.1 hie (hz.2.symm.trans hwi)
  by_cases hj : j ∈ e
  · exact ⟨j, hj, rfl⟩
  · obtain ⟨f, hfG, hfU, hfe⟩ := exists_second_edge hpar
      (by rw [Finset.card_insert_of_notMem hj, hG e he]) he (Finset.subset_insert _ _)
    obtain ⟨i, hie, hfi⟩ := eq_exchange_of_subset_insert hj
      ((hG e he).trans (hG f hfG).symm) hfU hfe
    refine ⟨i, hie, ?_⟩
    have hjs : j ∉ e.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hfzero := hsum f hfG
    rw [hfi, Finset.sum_insert hjs] at hfzero
    have hezero : w i + ∑ x ∈ e.erase i, w x = 0 := by
      rw [Finset.add_sum_erase _ _ hie]
      exact hsum e he
    exact add_right_cancel (hfzero.trans hezero.symm)

/-- Swapping a vertex with another vertex of the same label preserves edges. -/
theorem exchange_mem_of_label_eq (hG : IsUniform k G)
    (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0)
    {e : Finset V} (he : e ∈ G) {i j : V} (hi : i ∈ e) (hij : w j = w i) :
    insert j (e.erase i) ∈ G := by
  classical
  by_cases hj : j ∈ e
  · have hji : j = i := hinj e he hj hi hij
    subst j
    rwa [Finset.insert_erase hi]
  · obtain ⟨f, hfG, hfU, hfe⟩ := exists_second_edge hpar
      (by rw [Finset.card_insert_of_notMem hj, hG e he]) he (Finset.subset_insert _ _)
    obtain ⟨z, hze, hfz⟩ := eq_exchange_of_subset_insert hj
      ((hG e he).trans (hG f hfG).symm) hfU hfe
    have hjz : w j = w z := by
      have hfzero := hsum f hfG
      have hjs : j ∉ e.erase z := fun h => hj (Finset.mem_of_mem_erase h)
      rw [hfz, Finset.sum_insert hjs] at hfzero
      have hezero : w z + ∑ x ∈ e.erase z, w x = 0 := by
        rw [Finset.add_sum_erase _ _ hze]
        exact hsum e he
      exact add_right_cancel (hfzero.trans hezero.symm)
    have hzi : z = i := hinj e he hze hi (hjz.symm.trans hij)
    subst z
    rwa [hfz] at hfG

/-- Every label occurs among the vertices of each fixed edge. -/
theorem range_labels_eq_image_edge (hG : IsUniform k G)
    (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0)
    {e : Finset V} (he : e ∈ G) : Set.range w = w '' (e : Set V) := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi, _⟩ := exists_unique_label_representative hG hpar w hinj hsum he j
    exact ⟨i, hi.1, hi.2.symm⟩
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩

/-- The label classes have exactly `k` members. -/
theorem card_range_labels (hG : IsUniform k G)
    (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0)
    {e : Finset V} (he : e ∈ G) : Nat.card (Set.range w) = k := by
  classical
  let φ : {i // i ∈ e} → Set.range w := fun i => ⟨w i.1, ⟨i.1, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      exact Subtype.ext (hinj e he i.2 j.2 (congrArg Subtype.val hij))
    · rintro ⟨a, j, rfl⟩
      obtain ⟨i, hi, _⟩ := exists_unique_label_representative hG hpar w hinj hsum he j
      exact ⟨⟨i, hi.1⟩, Subtype.ext hi.2.symm⟩
  calc
    Nat.card (Set.range w) = Nat.card {i // i ∈ e} :=
      Nat.card_congr (Equiv.ofBijective φ hφ).symm
    _ = e.card := by simp
    _ = k := hG e he

/-- Every `k`-set of vertices with distinct labels is an edge. Combined with
the converse hypothesis, this identifies `G` as the complete multipartite
family whose parts are the label fibres. -/
theorem mem_of_card_eq_and_injOn_labels (hG : IsUniform k G)
    (hne : G.Nonempty) (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0)
    (s : Finset V) (hcard : s.card = k) (hsinj : Set.InjOn w (s : Set V)) : s ∈ G := by
  classical
  obtain ⟨e, he, hmax⟩ := G.exists_max_image (fun e => (e ∩ s).card) hne
  by_contra hsG
  have hsen : ¬ s ⊆ e := by
    intro hse
    have heq : s = e := Finset.eq_of_subset_of_card_le hse (by rw [hcard, hG e he])
    exact hsG (heq.symm ▸ he)
  obtain ⟨j, hjs, hje⟩ := Finset.not_subset.mp hsen
  obtain ⟨i, hi, _⟩ := exists_unique_label_representative hG hpar w hinj hsum he j
  obtain ⟨hie, hji⟩ := hi
  have hins : i ∉ s := by
    intro his
    have hij : j = i := hsinj hjs his hji
    exact hje (hij.symm ▸ hie)
  have hswap := exchange_mem_of_label_eq hG hpar w hinj hsum he hie hji
  have hmax' := hmax (insert j (e.erase i)) hswap
  have hinter : (insert j (e.erase i)) ∩ s = insert j (e ∩ s) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | ⟨_, hve⟩, hvs⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hve, hvs⟩
    · rintro (rfl | ⟨hve, hvs⟩)
      · exact ⟨Or.inl rfl, hjs⟩
      · exact ⟨Or.inr ⟨fun hvi => hins (hvi ▸ hvs), hve⟩, hvs⟩
  rw [hinter, Finset.card_insert_of_notMem (by simp [hje])] at hmax'
  omega

/-- Exact multipartite characterization by the equality-case labels. -/
theorem mem_iff_card_eq_and_injOn_labels (hG : IsUniform k G)
    (hne : G.Nonempty) (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0) (s : Finset V) :
    s ∈ G ↔ s.card = k ∧ Set.InjOn w (s : Set V) := by
  constructor
  · intro hs
    exact ⟨hG s hs, hinj s hs⟩
  · rintro ⟨hcard, hsinj⟩
    exact mem_of_card_eq_and_injOn_labels hG hne hpar w hinj hsum s hcard hsinj

variable [Fintype V]

/-- The label fibres give an actual surjective coloring by `Fin k` whose
transversals are exactly the edges of `G`. -/
theorem exists_partite_coloring (hG : IsUniform k G)
    (hne : G.Nonempty) (hpar : HasCocycleParity k G) (w : V → A)
    (hinj : ∀ e ∈ G, Set.InjOn w (e : Set V))
    (hsum : ∀ e ∈ G, ∑ i ∈ e, w i = 0) :
    ∃ color : V → Fin k, Function.Surjective color ∧
      (∀ i j, color i = color j ↔ w i = w j) ∧
      ∀ s : Finset V, s ∈ G ↔ s.card = k ∧ Set.InjOn color (s : Set V) := by
  classical
  obtain ⟨e, he⟩ := hne
  let : Fintype (Set.range w) := Fintype.ofFinite _
  have hc : Fintype.card (Set.range w) = Fintype.card (Fin k) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using card_range_labels hG hpar w hinj hsum he
  let α : Set.range w ≃ Fin k := Fintype.equivOfCardEq hc
  let color : V → Fin k := fun i => α ⟨w i, ⟨i, rfl⟩⟩
  have heq : ∀ i j, color i = color j ↔ w i = w j := by
    intro i j
    exact α.injective.eq_iff.trans Subtype.ext_iff
  refine ⟨color, ?_, heq, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := α.surjective a
    obtain ⟨i, hi⟩ := b.2
    refine ⟨i, ?_⟩
    change α ⟨w i, ⟨i, rfl⟩⟩ = a
    rw [show (⟨w i, ⟨i, rfl⟩⟩ : Set.range w) = b from Subtype.ext hi]
    exact hb
  · intro s
    rw [mem_iff_card_eq_and_injOn_labels hG ⟨e, he⟩ hpar w hinj hsum]
    constructor
    · rintro ⟨hcard, hw⟩
      exact ⟨hcard, fun i hi j hj hij => hw hi hj ((heq i j).mp hij)⟩
    · rintro ⟨hcard, hcolor⟩
      exact ⟨hcard, fun i hi j hj hij => hcolor hi hj ((heq i j).mpr hij)⟩

end SharpTopologicalOverlap.Spectral
