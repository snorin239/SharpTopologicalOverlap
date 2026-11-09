module

public import SharpTopologicalOverlap.Intersection.Algebra
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Basic
public import SharpTopologicalOverlap.Geometry.BarycentricModel
public import SharpTopologicalOverlap.Intersection.VertexCocycles
public import SharpTopologicalOverlap.Geometry.BarycentricGeometry
public import SharpTopologicalOverlap.Geometry.BarycentricApproximation

/-! # The target sphere and its fundamental cycle

The boundary of a `(d + 1)`-simplex is the union of a distinguished `d`-face
and the cone on its boundary. Its last vertex is the vertex at infinity.
This gives an actual finite target complex and cycle before subdivision.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.TargetCycle

open SharpTopologicalOverlap.Simplicial

attribute [local instance] Classical.decEq

/-- The target sphere before subdivision. -/
abbrev sphere (d : ℕ) := AbstractSimplicialComplex.standardSuccSimplexBoundary d

/-- The `(d + 1)`-cell whose boundary is the target sphere. -/
def fullCell (d : ℕ) : Cell (⊤ : AbstractSimplicialComplex (Fin (d + 2))) (d + 1) :=
  ⟨⟨(Finset.univ : Finset (Fin (d + 2))), by
    change (Finset.univ : Finset (Fin (d + 2))).Nonempty
    exact Finset.univ_nonempty⟩, by simp [Nat.add_assoc]⟩

/-- A facet of the full simplex, regarded as a cell of its boundary sphere. -/
def facet (d : ℕ) (i : Fin (d + 2)) : Cell (sphere d) d :=
  ⟨⟨((fullCell d).face i).1.1, by
    apply AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mpr
    refine ⟨Finset.card_pos.mp (by rw [((fullCell d).face i).2]; omega), ?_⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    have hc := congrArg Finset.card h
    rw [((fullCell d).face i).2, Finset.card_univ, Fintype.card_fin] at hc
    omega⟩, ((fullCell d).face i).2⟩

@[simp] theorem include_facet (d : ℕ) (i : Fin (d + 2)) :
    includeCell (show sphere d ≤ (⊤ : AbstractSimplicialComplex (Fin (d + 2))) from le_top)
      (facet d i) = (fullCell d).face i := rfl

theorem facet_injective (d : ℕ) : Function.Injective (facet d) := by
  intro i j hij
  apply (fullCell d).face_injective
  exact congrArg (includeCell (show sphere d ≤
    (⊤ : AbstractSimplicialComplex (Fin (d + 2))) from le_top)) hij

/-- The sum of all top facets, each with coefficient one. -/
def cycle (d : ℕ) : Chain (sphere d) d :=
  ∑ i : Fin (d + 2), Finsupp.single (facet d i) 1

theorem include_cycle (d : ℕ) :
    includeChain (show sphere d ≤ (⊤ : AbstractSimplicialComplex (Fin (d + 2))) from le_top)
      (cycle d) = boundary d (Finsupp.single (fullCell d) 1) := by
  simp [cycle]

/-- The boundary-sphere fundamental chain is an actual cycle. -/
theorem boundary_cycle (k : ℕ) : boundary k (cycle (k + 1)) = 0 := by
  apply includeChain_injective (show sphere (k + 1) ≤
    (⊤ : AbstractSimplicialComplex (Fin (k + 3))) from le_top)
  rw [map_zero, ← boundary_includeChain, include_cycle, boundary_boundary]

theorem dimension_le {d p : ℕ} (τ : Cell (sphere d) p) : p ≤ d := by
  have hproper := (AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mp τ.1.2).2
  have hc := Finset.card_lt_card hproper
  rw [τ.2, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Every top cell is one of the facets used in the actual cycle. -/
theorem exists_facet {d : ℕ} (τ : Cell (sphere d) d) :
    ∃ i : Fin (d + 2), τ = facet d i := by
  let τ' := includeCell (show sphere d ≤
    (⊤ : AbstractSimplicialComplex (Fin (d + 2))) from le_top) τ
  obtain ⟨i, hi⟩ := ((fullCell d).exists_face_eq_iff_subset τ').mpr (Finset.subset_univ _)
  refine ⟨i, ?_⟩
  apply includeCell_injective (show sphere d ≤
    (⊤ : AbstractSimplicialComplex (Fin (d + 2))) from le_top)
  exact hi.symm

@[simp] theorem cycle_apply_facet (d : ℕ) (i : Fin (d + 2)) : cycle d (facet d i) = 1 := by
  classical
  rw [cycle, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [show facet d j ≠ facet d i from fun h => hji (facet_injective d h)]
  · simp

@[simp] theorem cycle_apply {d : ℕ} (τ : Cell (sphere d) d) : cycle d τ = 1 := by
  obtain ⟨i, rfl⟩ := exists_facet τ
  exact cycle_apply_facet d i

/-- The final vertex is the cone vertex outside the distinguished target simplex. -/
def infinity (d : ℕ) : Fin (d + 2) := Fin.last (d + 1)

/-- Edges of the actual target complex, as a symmetric vertex relation. -/
def Edge (d : ℕ) (v w : Fin (d + 2)) : Prop :=
  v ≠ w ∧ ({v, w} : Finset (Fin (d + 2))) ∈ sphere d

theorem edge_of_ne {d : ℕ} (hd : 1 ≤ d) {v w : Fin (d + 2)} (hvw : v ≠ w) :
    Edge d v w := by
  refine ⟨hvw, AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mpr ?_⟩
  refine ⟨Finset.insert_nonempty _ _, Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, ?_⟩⟩
  intro h
  have hc := congrArg Finset.card h
  rw [Finset.card_pair hvw, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Before subdivision every vertex is joined to the zero anchor at infinity. -/
theorem path_to_infinity {d : ℕ} (hd : 1 ≤ d) (v : Fin (d + 2)) :
    Relation.ReflTransGen (Edge d) v (infinity d) := by
  by_cases hv : v = infinity d
  · subst v
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (edge_of_ne hd hv)

end SharpTopologicalOverlap.Geometry.TargetCycle

namespace SharpTopologicalOverlap.Geometry.BarycentricModel

open SharpTopologicalOverlap.Simplicial Finsupp

variable {V : Type} {K : AbstractSimplicialComplex V} (M : BarycentricModel K)

local instance stepDecidableEq : DecidableEq M.step.Vertex :=
  M.step.vertexLinearOrder.toDecidableEq

/-- An original face is a vertex of the next actual subdivision. -/
def faceVertex {k : ℕ} (s : Cell M.complex k) : M.step.Vertex := ⟨s.1.1, s.1.2⟩

/-- Subdivide a face by coning the subdivided boundary to its barycenter.
The rank-first order of the subdivision vertices permits the ordered cone. -/
def subdividedCell : ∀ k : ℕ, Cell M.complex k → Chain M.step.complex k
  | 0, s => Finsupp.single (AbstractSimplicialComplex.RealizationCell.vertex
      M.step.complex (M.faceVertex s)) 1
  | k + 1, s => TauCeti.OrderedSimplicialChain.cone Coeff (M.faceVertex s) k
      (∑ i : Fin (k + 2), subdividedCell k (s.face i))

/-- Linear extension of the actual abstract subdivision of individual faces. -/
def subdivisionMap (k : ℕ) : Chain M.complex k →ₗ[Coeff] Chain M.step.complex k :=
  Finsupp.linearCombination Coeff (M.subdividedCell k)

@[simp] theorem subdivisionMap_single {k : ℕ} (s : Cell M.complex k) (r : Coeff) :
    M.subdivisionMap k (Finsupp.single s r) = r • M.subdividedCell k s := by
  simp [subdivisionMap]

/-- A nonzero coned cell comes from an actual supported base cell. -/
private theorem cone_support {Q : Type*} [LinearOrder Q]
    {L : AbstractSimplicialComplex Q} {k : ℕ} (v : Q) (c : Chain L k)
    {t : Cell L (k + 1)}
    (ht : t ∈ (TauCeti.OrderedSimplicialChain.cone Coeff v k c).support) :
    ∃ u ∈ c.support, ∃ h : (∀ w ∈ u.1.1, w < v) ∧ insert v u.1.1 ∈ L,
      t = u.cone v h.1 h.2 := by
  rw [← c.sum_single, map_finsuppSum] at ht
  obtain ⟨u, hu, ht⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum ht)
  by_cases h : (∀ w ∈ u.1.1, w < v) ∧ insert v u.1.1 ∈ L
  · rw [TauCeti.OrderedSimplicialChain.cone_single u h.1 h.2] at ht
    exact ⟨u, hu, h, Finset.mem_singleton.mp (Finsupp.support_single_subset ht)⟩
  · rw [TauCeti.OrderedSimplicialChain.cone_single_of_not u h] at ht
    simp at ht

/-- Every subdivision vertex in the chain of a face is a subface of that face. -/
theorem subdividedCell_carried : ∀ (k : ℕ) (s : Cell M.complex k),
    ∀ t ∈ (M.subdividedCell k s).support, ∀ v ∈ t.1.1, v.1 ⊆ s.1.1 := by
  intro k
  induction k with
  | zero =>
    intro s t ht v hv
    have ht' : t = AbstractSimplicialComplex.RealizationCell.vertex M.step.complex
        (M.faceVertex s) := by simpa [subdividedCell] using ht
    subst t
    have hv' : v = M.faceVertex s := by
      simpa only [AbstractSimplicialComplex.RealizationCell.vertex_val,
        Finset.mem_singleton] using hv
    subst v
    exact Finset.Subset.refl _
  | succ k ih =>
    intro s t ht v hv
    obtain ⟨u, hu, h, rfl⟩ := cone_support (M.faceVertex s) _ ht
    rw [AbstractSimplicialComplex.RealizationCell.cone_val] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.Subset.refl _
    · obtain ⟨i, _, hu⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hu)
      exact (ih (s.face i) u hu v hv).trans (s.face_val_subset i)

/-- Every supported subdivided boundary cell can genuinely be coned to the
full-face barycenter in the abstract barycentric subdivision. -/
theorem subdividedBoundary_cone_admissible {k : ℕ} (s : Cell M.complex (k + 1)) :
    ∀ t ∈ (∑ i : Fin (k + 2), M.subdividedCell k (s.face i)).support,
      (∀ v ∈ t.1.1, v < M.faceVertex s) ∧ insert (M.faceVertex s) t.1.1 ∈ M.step.complex := by
  intro t ht
  obtain ⟨i, _, ht⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum ht)
  have hsub (v : M.step.Vertex) (hv : v ∈ t.1.1) : v.1 ⊆ s.1.1 :=
    (M.subdividedCell_carried k (s.face i) t ht v hv).trans (s.face_val_subset i)
  refine ⟨?_, ?_⟩
  · intro v hv
    apply M.step_lt_of_card_lt
    have hc := Finset.card_le_card (M.subdividedCell_carried k (s.face i) t ht v hv)
    change v.1.card < s.1.1.card
    rw [(s.face i).2] at hc
    rw [s.2]
    omega
  · apply TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mpr
    refine ⟨Finset.insert_nonempty (α := M.step.Vertex) _ _, ?_⟩
    intro v hv w hw
    rcases (Finset.mem_insert (α := M.step.Vertex)).mp hv with rfl | hv
    · rcases (Finset.mem_insert (α := M.step.Vertex)).mp hw with rfl | hw
      · exact Or.inl (Finset.Subset.refl _)
      · exact Or.inr (hsub w hw)
    · rcases (Finset.mem_insert (α := M.step.Vertex)).mp hw with rfl | hw
      · exact Or.inl (hsub v hv)
      · exact (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mp
          t.1.2).2 v hv w hw

/-- The abstract subdivision map applied to a cell boundary is the sum used
in the recursive cone construction. -/
theorem subdivisionMap_boundary_single {k : ℕ} (s : Cell M.complex (k + 1)) :
    M.subdivisionMap k (boundary k (Finsupp.single s 1)) =
      ∑ i : Fin (k + 2), M.subdividedCell k (s.face i) := by
  simp

/-- The actual simplicial subdivision map commutes with boundary. -/
theorem boundary_subdivisionMap (k : ℕ) (c : Chain M.complex (k + 1)) :
    boundary k (M.subdivisionMap (k + 1) c) = M.subdivisionMap k (boundary k c) := by
  induction k with
  | zero =>
    have hcell (s : Cell M.complex 1) :
        boundary 0 (M.subdividedCell 1 s) =
          ∑ i : Fin 2, M.subdividedCell 0 (s.face i) := by
      rw [subdividedCell, TauCeti.OrderedSimplicialChain.boundary_cone_zero
        (M.subdividedBoundary_cone_admissible s)]
      have haug : Finsupp.linearCombination Coeff (fun _ => (1 : Coeff))
          (∑ i : Fin 2, M.subdividedCell 0 (s.face i)) = 0 := by
        simp only [map_add, subdividedCell, Finsupp.linearCombination_single,
          one_smul, Fin.sum_univ_two]
        decide
      rw [haug, Finsupp.single_zero, zero_sub]
      ext t
      exact (show ∀ x : Coeff, -x = x by decide) _
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c e hc he => simp only [map_add, hc, he]
    | single s r => simp [hcell]
  | succ k ih =>
    have hcell (s : Cell M.complex (k + 2)) :
        boundary (k + 1) (M.subdividedCell (k + 2) s) =
          ∑ i : Fin (k + 3), M.subdividedCell (k + 1) (s.face i) := by
      have hzero : boundary k
          (∑ i : Fin (k + 3), M.subdividedCell (k + 1) (s.face i)) = 0 := by
        rw [← subdivisionMap_boundary_single, ih, boundary_boundary, map_zero]
      rw [subdividedCell, TauCeti.OrderedSimplicialChain.boundary_cone_succ
        (M.subdividedBoundary_cone_admissible s), hzero, map_zero, zero_add]
      simp [show (-1 : Coeff) = 1 by decide]
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c e hc he => simp only [map_add, hc, he]
    | single s r => simp [hcell, Finset.smul_sum]

/-- The ordered cone preserves the coefficient at each admissible base cell. -/
private theorem cone_apply_cone {Q : Type*} [LinearOrder Q]
    {L : AbstractSimplicialComplex Q} {k : ℕ} (v : Q) (c : Chain L k)
    (hc : ∀ t ∈ c.support, (∀ w ∈ t.1.1, w < v) ∧ insert v t.1.1 ∈ L)
    (u : Cell L k) (hu : (∀ w ∈ u.1.1, w < v) ∧ insert v u.1.1 ∈ L) :
    TauCeti.OrderedSimplicialChain.cone Coeff v k c (u.cone v hu.1 hu.2) = c u := by
  have hdec : TauCeti.OrderedSimplicialChain.cone Coeff v k c =
      ∑ t ∈ c.support,
        TauCeti.OrderedSimplicialChain.cone Coeff v k (Finsupp.single t (c t)) := by
    conv_lhs => rw [← c.sum_single]
    simp only [Finsupp.sum, map_sum]
  rw [hdec, Finsupp.finsetSum_apply, Finset.sum_eq_single u]
  · rw [TauCeti.OrderedSimplicialChain.cone_single u hu.1 hu.2]
    simp
  · intro t ht htu
    obtain ⟨hlt, hL⟩ := hc t ht
    rw [TauCeti.OrderedSimplicialChain.cone_single t hlt hL]
    have hne : t.cone v hlt hL ≠ u.cone v hu.1 hu.2 := by
      intro h
      apply htu
      apply cell_vertices_injective
      have hv₁ : v ∉ t.1.1 := fun hv => (hlt v hv).false
      have hv₂ : v ∉ u.1.1 := fun hv => (hu.1 v hv).false
      have he := congrArg (fun s : Cell L (k + 1) => s.1.1.erase v) h
      simpa [AbstractSimplicialComplex.RealizationCell.cone_val, hv₁, hv₂] using he
    simp [Ne.symm hne]
  · intro hu'
    have hz := Finsupp.notMem_support_iff.mp hu'
    simp [hz]

/-- Each top flag inside a source face occurs exactly once in its subdivision. -/
theorem subdividedCell_apply_of_carried : ∀ (k : ℕ) (s : Cell M.complex k)
    (t : Cell M.step.complex k),
    (∀ v ∈ t.1.1, v.1 ⊆ s.1.1) → M.subdividedCell k s t = 1 := by
  intro k
  induction k with
  | zero =>
    intro s t hsub
    have hfull := M.full_face_mem_of_card s t hsub
    have ht : t = AbstractSimplicialComplex.RealizationCell.vertex M.step.complex
        (M.faceVertex s) := by
      apply cell_vertices_injective
      dsimp only
      rw [AbstractSimplicialComplex.RealizationCell.vertex_val]
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hfull, fun v hv => ?_⟩
      exact Finset.card_le_one.mp (by rw [t.2]) v hv (M.faceVertex s) hfull
    simp [subdividedCell, ht]
  | succ k ih =>
    intro s t hsub
    have hfull : M.faceVertex s ∈ t.1.1 := M.full_face_mem_of_card s t hsub
    have hmem : M.faceVertex s ∈ Finset.univ.image t.vertexEmbedding := by
      rw [t.image_vertexEmbedding]
      exact hfull
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    let u := t.face j
    have hproper : ∀ w ∈ u.1.1, w.1 ⊂ s.1.1 := by
      intro w hw
      have hw' : w ∈ t.1.1.erase (M.faceVertex s) := by
        simpa only [u, AbstractSimplicialComplex.RealizationCell.face_val, hj] using hw
      obtain ⟨hwne, hwt⟩ := Finset.mem_erase.mp hw'
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub w hwt, ?_⟩
      intro heq
      exact hwne (Subtype.ext heq)
    obtain ⟨p, ⟨hps, hpu⟩, huniq⟩ := M.exists_unique_parent_facet s u hproper
    obtain ⟨i, hi⟩ := (s.exists_face_eq_iff_subset p).mpr hps
    let c := ∑ i : Fin (k + 2), M.subdividedCell k (s.face i)
    have hcu : c u = 1 := by
      dsimp only [c]
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · rw [hi]
        exact ih p u hpu
      · intro l _ hli
        by_contra hne
        have hcar := M.subdividedCell_carried k (s.face l) u (Finsupp.mem_support_iff.mpr hne)
        have hlp : s.face l = p := huniq (s.face l) ⟨s.face_val_subset l, hcar⟩
        exact hli (s.face_injective (hlp.trans hi.symm))
      · simp
    have hu : u ∈ c.support := Finsupp.mem_support_iff.mpr (by rw [hcu]; exact one_ne_zero)
    have hcone := M.subdividedBoundary_cone_admissible s u hu
    have ht : t = u.cone (M.faceVertex s) hcone.1 hcone.2 := by
      apply cell_vertices_injective
      dsimp only
      rw [AbstractSimplicialComplex.RealizationCell.cone_val]
      change t.1.1 = insert (M.faceVertex s) (t.face j).1.1
      rw [AbstractSimplicialComplex.RealizationCell.face_val, hj]
      exact (Finset.insert_erase hfull).symm
    change TauCeti.OrderedSimplicialChain.cone Coeff (M.faceVertex s) k c t = 1
    rw [ht, cone_apply_cone _ _ (M.subdividedBoundary_cone_admissible s) _ hcone, hcu]

/-- Subdivision preserves coefficient one on every top-dimensional cell. -/
theorem subdivisionMap_top_one {d : ℕ}
    (hd : ∀ σ ∈ M.complex, σ.card ≤ d + 1) (c : Chain M.complex d)
    (hc : ∀ s : Cell M.complex d, c s = 1) (t : Cell M.step.complex d) :
    M.subdivisionMap d c t = 1 := by
  obtain ⟨v, hv, hsub, hcard⟩ := M.exists_max_face t
  have hle := hd v.1 v.2
  have hvcard : v.1.card = d + 1 := Nat.le_antisymm hle hcard
  let s : Cell M.complex d := ⟨v, hvcard⟩
  have hgen : M.subdividedCell d s t = 1 := M.subdividedCell_apply_of_carried d s t hsub
  have hzero (r : Cell M.complex d) (hrs : r ≠ s) : M.subdividedCell d r t = 0 := by
    by_contra hne
    have hcar := M.subdividedCell_carried d r t (Finsupp.mem_support_iff.mpr hne)
    have hvsub : v.1 ⊆ r.1.1 := hcar v hv
    have heq : v.1 = r.1.1 := Finset.eq_of_subset_of_card_le hvsub (by rw [hvcard, r.2])
    exact hrs (cell_vertices_injective heq.symm)
  simp only [subdivisionMap, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · rw [hc s, hgen, one_mul]
  · intro r _ hrs
    rw [hzero r hrs, mul_zero]
  · intro hs
    exact (hs (Finsupp.mem_support_iff.mpr (by rw [hc s]; exact one_ne_zero))).elim

/-- The copy of an original vertex among the vertices of the subdivision. -/
def singletonVertex (v : M.Vertex) : M.step.Vertex :=
  M.faceVertex (AbstractSimplicialComplex.RealizationCell.vertex M.complex v)

@[simp] theorem singletonVertex_val (v : M.Vertex) : (M.singletonVertex v).1 = {v} := by
  simp [singletonVertex, faceVertex, AbstractSimplicialComplex.RealizationCell.vertex_val]

/-- Nested faces are joined by an edge, allowing equality as a constant path. -/
theorem step_path_of_nested (σ τ : M.step.Vertex)
    (hnest : σ.1 ⊆ τ.1 ∨ τ.1 ⊆ σ.1) :
    Relation.ReflTransGen (TargetEdge M.step.complex) σ τ := by
  by_cases h : σ = τ
  · subst τ
    exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    refine ⟨h, ?_⟩
    apply TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mpr
    refine ⟨Finset.insert_nonempty (α := M.step.Vertex) _ _, ?_⟩
    intro a ha b hb
    rcases (Finset.mem_insert (α := M.step.Vertex)).mp ha with rfl | ha
    · rcases (Finset.mem_insert (α := M.step.Vertex)).mp hb with rfl | hb
      · exact Or.inl (Finset.Subset.refl _)
      · have hb' : b = τ := Finset.mem_singleton.mp hb
        subst b
        exact hnest
    · have ha' : a = τ := Finset.mem_singleton.mp ha
      subst a
      rcases (Finset.mem_insert (α := M.step.Vertex)).mp hb with rfl | hb
      · exact hnest.symm
      · have hb' : b = τ := Finset.mem_singleton.mp hb
        subst b
        exact Or.inl (Finset.Subset.refl _)

theorem step_path_of_edge {v w : M.Vertex} (hvw : TargetEdge M.complex v w) :
    Relation.ReflTransGen (TargetEdge M.step.complex)
      (M.singletonVertex v) (M.singletonVertex w) := by
  let e : M.step.Vertex := ⟨{v, w}, hvw.2⟩
  apply (M.step_path_of_nested (M.singletonVertex v) e (Or.inl ?_)).trans
    (M.step_path_of_nested e (M.singletonVertex w) (Or.inr ?_))
  · rw [M.singletonVertex_val]
    change ({v} : Finset M.Vertex) ⊆ {v, w}
    simp
  · rw [M.singletonVertex_val]
    change ({w} : Finset M.Vertex) ⊆ {v, w}
    simp

theorem step_lift_path {v w : M.Vertex}
    (hpath : Relation.ReflTransGen (TargetEdge M.complex) v w) :
    Relation.ReflTransGen (TargetEdge M.step.complex)
      (M.singletonVertex v) (M.singletonVertex w) := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w u _ hwu ih => exact ih.trans (M.step_path_of_edge hwu)

/-- Connectivity to a prescribed anchor survives the actual subdivision. -/
theorem step_paths_to_anchor (anchor : M.Vertex)
    (hpath : ∀ v, Relation.ReflTransGen (TargetEdge M.complex) v anchor)
    (σ : M.step.Vertex) :
    Relation.ReflTransGen (TargetEdge M.step.complex) σ (M.singletonVertex anchor) := by
  obtain ⟨v, hv⟩ := M.complex.isRelLowerSet_faces.prop_of_mem σ.2
  apply (M.step_path_of_nested σ (M.singletonVertex v) (Or.inr ?_)).trans
    (M.step_lift_path (hpath v))
  rw [M.singletonVertex_val]
  exact Finset.singleton_subset_iff.mpr hv

/-- Linear subdivision retains support on subfaces of supported input cells. -/
theorem subdivisionMap_support {k : ℕ} (c : Chain M.complex k)
    {t : Cell M.step.complex k} (ht : t ∈ (M.subdivisionMap k c).support) :
    ∃ s ∈ c.support, ∀ v ∈ t.1.1, v.1 ⊆ s.1.1 := by
  rw [← c.sum_single, map_finsuppSum] at ht
  obtain ⟨s, hs, ht⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum ht)
  rw [M.subdivisionMap_single] at ht
  have ht' := Finsupp.support_smul ht
  exact ⟨s, hs, M.subdividedCell_carried k s t ht'⟩

/-- Copying a vertex into the subdivision preserves its original realization. -/
@[simp] theorem singletonVertex_point (v : M.Vertex) :
    M.step.vertexPoint (M.singletonVertex v) = M.vertexPoint v := by
  apply Subtype.ext
  rw [M.step.vertexPoint_val, M.vertexPoint_val]
  change M.linearMap
    (AbstractSimplicialComplex.barycentricSubdivisionLinearMap M.complex
      (Finsupp.single (M.singletonVertex v) 1)) = M.linearMap (Finsupp.single v 1)
  rw [AbstractSimplicialComplex.barycentricSubdivisionLinearMap_single]
  congr 1
  ext w
  simp [AbstractSimplicialComplex.faceBarycenter_apply, Finsupp.single_apply, eq_comm]

end SharpTopologicalOverlap.Geometry.BarycentricModel

namespace SharpTopologicalOverlap.Geometry

open SharpTopologicalOverlap.Simplicial Finsupp

variable {V : Type} [Fintype V] [LinearOrder V] (K : AbstractSimplicialComplex V)

/-- The actual chain comparison from the original complex to each common
iterated barycentric subdivision. -/
def iteratedSubdivision : ∀ j k : ℕ,
    Chain K k →ₗ[Coeff] Chain (barycentricModel K j).complex k
  | 0, _ => LinearMap.id
  | j + 1, k => ((barycentricModel K j).subdivisionMap k).comp (iteratedSubdivision j k)

theorem boundary_iteratedSubdivision (j k : ℕ) (c : Chain K (k + 1)) :
    boundary k (iteratedSubdivision K j (k + 1) c) =
      iteratedSubdivision K j k (boundary k c) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change boundary k (((barycentricModel K j).subdivisionMap (k + 1))
      (iteratedSubdivision K j (k + 1) c)) =
        (barycentricModel K j).subdivisionMap k (iteratedSubdivision K j k (boundary k c))
    exact ((barycentricModel K j).boundary_subdivisionMap k _).trans
      (congrArg ((barycentricModel K j).subdivisionMap k) ih)

/-- The original vertex, as an actual vertex at every subdivision depth. -/
def originalVertex : ∀ j : ℕ, V → (barycentricModel K j).Vertex
  | 0, v => v
  | j + 1, v => (barycentricModel K j).singletonVertex (originalVertex j v)

@[simp] theorem originalVertex_point (j : ℕ) (v : V) :
    (barycentricModel K j).vertexPoint (originalVertex K j v) =
      AbstractSimplicialComplex.vertex K v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (barycentricModel K j).step.vertexPoint
      ((barycentricModel K j).singletonVertex (originalVertex K j v)) = _
    rw [BarycentricModel.singletonVertex_point, ih]

/-- A zero-dimensional source generator remains one copy of the same point. -/
@[simp] theorem iteratedSubdivision_vertex (j : ℕ) (v : V) (r : Coeff) :
    iteratedSubdivision K j 0
      (Finsupp.single (AbstractSimplicialComplex.RealizationCell.vertex K v) r) =
      Finsupp.single (AbstractSimplicialComplex.RealizationCell.vertex
        (barycentricModel K j).complex (originalVertex K j v)) r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [iteratedSubdivision, LinearMap.comp_apply, ih, BarycentricModel.subdividedCell,
      BarycentricModel.singletonVertex, originalVertex]

/-- Every actual iterated child retains the original source face carrier. -/
theorem iteratedSubdivision_carried (j k : ℕ) (s : Cell K k)
    {t : Cell (barycentricModel K j).complex k}
    (ht : t ∈ (iteratedSubdivision K j k (Finsupp.single s 1)).support) :
    ∀ v ∈ t.1.1, ((barycentricModel K j).vertexPoint v).1.support ⊆ s.1.1 := by
  induction j with
  | zero =>
    have ht' : t = s := by simpa [iteratedSubdivision] using ht
    subst t
    intro v hv
    rw [(barycentricModel K 0).vertexPoint_val]
    change (Finsupp.single v (1 : ℝ)).support ⊆ s.1.1
    simpa using (Finset.singleton_subset_iff.mpr hv)
  | succ j ih =>
    obtain ⟨u, hu, htu⟩ := (barycentricModel K j).subdivisionMap_support _ ht
    intro v hv
    apply (barycentricModel K j).step_vertexPoint_support_subset
    intro w hw
    exact ih hu w (htu v hv hw)

/-- The same original carrier controls every weighted point of every actual
child, not only the child vertices. -/
theorem iteratedSubdivision_facePoint_carried (j k : ℕ) (s : Cell K k)
    {t : Cell (barycentricModel K j).complex k}
    (ht : t ∈ (iteratedSubdivision K j k (Finsupp.single s 1)).support)
    (w : Simplex t.1.1) :
    ((barycentricModel K j).facePoint t.1 w).1.support ⊆ s.1.1 := by
  let M := barycentricModel K j
  let w' := (Finset.standardSimplexHomeomorph t.1.1).symm w
  apply M.homeomorph_support_subset
  intro q hq
  have hqt : q ∈ t.1.1 := by
    apply AbstractSimplicialComplex.StandardSimplex.support_subset w'
    simpa only [AbstractSimplicialComplex.faceInclusion_val] using hq
  exact iteratedSubdivision_carried K j k s ht q hqt

end SharpTopologicalOverlap.Geometry

namespace SharpTopologicalOverlap.Geometry.TargetCycle

open SharpTopologicalOverlap.Simplicial

/-- The actual target sphere after a prescribed number of barycentric subdivisions. -/
abbrev model (d j : ℕ) := barycentricModel (sphere d) j

/-- Transport the explicitly constructed target cycle through actual chain maps. -/
def refinedCycle (d : ℕ) : ∀ j : ℕ, Chain (model d j).complex d
  | 0 => cycle d
  | j + 1 => (model d j).subdivisionMap d (refinedCycle d j)

theorem sphere_faceCardBound (d : ℕ) : ∀ σ ∈ sphere d, σ.card ≤ d + 1 := by
  intro σ hσ
  have hc := Finset.card_lt_card
    (AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mp hσ).2
  rw [Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem refined_dimension_le (d j p : ℕ) (τ : Cell (model d j).complex p) : p ≤ d := by
  have hc := barycentricModel_faceCardBound (sphere d) d (sphere_faceCardBound d) j τ.1.1 τ.1.2
  rw [τ.2] at hc
  omega

/-- Every top simplex of the actual refined target sphere has coefficient one. -/
@[simp] theorem refinedCycle_apply (d j : ℕ) (τ : Cell (model d j).complex d) :
    refinedCycle d j τ = 1 := by
  induction j with
  | zero => exact cycle_apply τ
  | succ j ih =>
    exact (model d j).subdivisionMap_top_one
      (barycentricModel_faceCardBound (sphere d) d (sphere_faceCardBound d) j)
      (refinedCycle d j) ih τ

theorem boundary_refinedCycle (k j : ℕ) : boundary k (refinedCycle (k + 1) j) = 0 := by
  induction j with
  | zero => exact boundary_cycle k
  | succ j ih =>
    rw [refinedCycle, BarycentricModel.boundary_subdivisionMap, ih, map_zero]

/-- The distinguished zero anchor under repeated subdivision. -/
def refinedInfinity (d : ℕ) : ∀ j : ℕ, (model d j).Vertex
  | 0 => infinity d
  | j + 1 => (model d j).singletonVertex (refinedInfinity d j)

theorem refined_path_to_infinity {d : ℕ} (hd : 1 ≤ d) (j : ℕ)
    (v : (model d j).Vertex) :
    Relation.ReflTransGen (TargetEdge (model d j).complex) v (refinedInfinity d j) := by
  induction j with
  | zero => exact path_to_infinity hd v
  | succ j ih => exact (model d j).step_paths_to_anchor (refinedInfinity d j) ih v

end SharpTopologicalOverlap.Geometry.TargetCycle
