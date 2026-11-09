module

public import SharpTopologicalOverlap.Geometry.BarycentricModel
public import SharpTopologicalOverlap.Simplicial
public import TauCeti.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Geometry of the actual barycentric cells -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.BarycentricModel

open AbstractSimplicialComplex Set
open SharpTopologicalOverlap.Simplicial

variable {V : Type*} {K : AbstractSimplicialComplex V}

/-- A closed original face carries every convex combination of fine vertices
that it carries. Nonnegative coordinate sums introduce no new support. -/
theorem support_subset_of_vertices (M : BarycentricModel K)
    (x : M.complex.Realization) (σ : Finset V)
    (hσ : ∀ q ∈ x.1.support, (M.vertexPoint q).1.support ⊆ σ) :
    (M.homeomorph x).1.support ⊆ σ := by
  classical
  intro v hv
  by_contra hvs
  have hz : (M.homeomorph x).1 v = 0 := by
    rw [M.homeomorph_val_sum]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro q hq
    have hqv : (M.vertexPoint q).1 v = 0 := by
      by_contra hne
      exact hvs (hσ q hq (Finsupp.mem_support_iff.mpr hne))
    rw [hqv, mul_zero]
  exact (Finsupp.mem_support_iff.mp hv) hz

theorem faceInclusion_support_subset (M : BarycentricModel K)
    (ρ : TauCeti.SetLike.Face M.complex) (σ : Finset V)
    (hσ : ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ)
    (x : StandardSimplex ρ.1) :
    (M.homeomorph (faceInclusion M.complex ρ x)).1.support ⊆ σ := by
  apply M.support_subset_of_vertices _ σ
  intro q hq
  apply hσ q
  apply StandardSimplex.support_subset x
  simpa only [faceInclusion_val] using hq

/-- Every actual model simplex is nondegenerate in the original coordinates.
The homeomorphism is injective on its whole realization, hence the ambient
linear coordinate map is injective on each closed simplex. -/
theorem cell_affineIndependent (M : BarycentricModel K)
    (σ : TauCeti.SetLike.Face M.complex) :
    AffineIndependent ℝ (fun q : σ.1 => (M.vertexPoint q).1) := by
  classical
  let p : σ.1 → (M.Vertex →₀ ℝ) := fun q => Finsupp.single q 1
  have hp : AffineIndependent ℝ p :=
    ((Finsupp.linearIndependent_single_one ℝ M.Vertex).comp
      (fun q : σ.1 => q.1) Subtype.val_injective).affineIndependent
  have hrange : Set.range p = (fun q => Finsupp.single q (1 : ℝ)) '' (σ.1 : Set M.Vertex) := by
    ext z
    simp [p]
  have hinj : Set.InjOn M.linearMap (convexHull ℝ (Set.range p)) := by
    intro x hx y hy hxy
    let a : StandardSimplex σ.1 := ⟨x, by
      rw [hrange] at hx
      simpa only [Finset.coe_image] using hx⟩
    let b : StandardSimplex σ.1 := ⟨y, by
      rw [hrange] at hy
      simpa only [Finset.coe_image] using hy⟩
    have he : M.homeomorph (faceInclusion M.complex σ a) =
        M.homeomorph (faceInclusion M.complex σ b) := by
      apply Subtype.ext
      simpa only [M.homeomorph_val, faceInclusion_val] using hxy
    simpa only [faceInclusion_val] using congrArg Subtype.val (M.homeomorph.injective he)
  have h := hp.map_of_injOn_convexHull M.linearMap.toAffineMap hinj
  simpa only [p, Function.comp_def, LinearMap.coe_toAffineMap, ← M.vertexPoint_val] using h

/-- A fine face contained in an original closed face cannot have larger
dimension. This includes faces on the boundary of the original simplex. -/
theorem card_le_of_support_subset (M : BarycentricModel K)
    (ρ : TauCeti.SetLike.Face M.complex) (σ : Finset V)
    (hσ : ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ) : ρ.1.card ≤ σ.card := by
  classical
  let p : ρ.1 → (V →₀ ℝ) := fun q => (M.vertexPoint q).1
  let t : σ → (V →₀ ℝ) := fun v => Finsupp.single v 1
  have hp : AffineIndependent ℝ p := M.cell_affineIndependent ρ
  have ht : AffineIndependent ℝ t :=
    ((Finsupp.linearIndependent_single_one ℝ V).comp
      (fun v : σ => v.1) Subtype.val_injective).affineIndependent
  have hρne := M.complex.isRelLowerSet_faces.prop_of_mem ρ.2
  let : Nonempty ρ.1 := hρne.to_subtype
  have hσne : σ.Nonempty := by
    obtain ⟨q, hq⟩ := hρne
    have hne : (M.vertexPoint q).1.support.Nonempty :=
      K.isRelLowerSet_faces.prop_of_mem (support_mem K (M.vertexPoint q))
    exact hne.mono (hσ q hq)
  let : Nonempty σ := hσne.to_subtype
  have hspan : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ (Set.range t) := by
    apply affineSpan_le.mpr
    rintro x ⟨q, rfl⟩
    apply convexHull_subset_affineSpan (𝕜 := ℝ) _
    have hrange : Set.range t = (fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set V) := by
      ext z
      simp [t]
    rw [hrange]
    exact mem_standardSimplex_iff.mpr
      ⟨Realization.nonneg K (M.vertexPoint q), Realization.sum_eq_one K (M.vertexPoint q), hσ q q.2⟩
  have hdir := AffineSubspace.direction_le hspan
  rw [direction_affineSpan, direction_affineSpan] at hdir
  have hle := Submodule.finrank_mono hdir
  have hρcard := hp.finrank_vectorSpan_add_one
  have hσcard := ht.finrank_vectorSpan_add_one
  simp only [Fintype.card_coe] at hρcard hσcard
  omega

/-- A full-dimensional flag of subfaces of a `k`-face contains that face.
This gives uniqueness of its original parent without enumerating permutations. -/
theorem full_face_mem_of_card (M : BarycentricModel K) {k : ℕ}
    (s : Cell M.complex k) (u : Cell M.step.complex k)
    (hsub : ∀ σ ∈ u.1.1, σ.1 ⊆ s.1.1) : s.1 ∈ u.1.1 := by
  classical
  by_contra hs
  have hnested := (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mp u.1.2).2
  have hinj : Set.InjOn (fun σ : M.step.Vertex => σ.1.card) (u.1.1 : Set M.step.Vertex) := by
    intro σ hσ τ hτ heq
    apply Subtype.ext
    rcases hnested σ hσ τ hτ with h | h
    · exact Finset.eq_of_subset_of_card_le h heq.ge
    · exact (Finset.eq_of_subset_of_card_le h heq.le).symm
  have hmaps : ∀ σ ∈ u.1.1, σ.1.card ∈ Finset.Icc 1 k := by
    intro σ hσ
    refine Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr
      (M.complex.isRelLowerSet_faces.prop_of_mem σ.2), ?_⟩
    have hne : σ.1 ≠ s.1.1 := by
      intro heq
      exact hs ((Subtype.ext heq : σ = s.1) ▸ hσ)
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub σ hσ, hne⟩)
    rw [s.2] at hc
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [u.2] at hcard
  simp at hcard

/-- A fine flag has a largest original face, of cardinality at least the
number of vertices in the flag. -/
theorem exists_max_face (M : BarycentricModel K) {k : ℕ}
    (u : Cell M.step.complex k) :
    ∃ v ∈ u.1.1, (∀ w ∈ u.1.1, w.1 ⊆ v.1) ∧ k + 1 ≤ v.1.card := by
  classical
  have hne := M.step.complex.isRelLowerSet_faces.prop_of_mem u.1.2
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image u.1.1 (fun w => w.1.card) hne
  have hnested := (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mp u.1.2).2
  have hsub : ∀ w ∈ u.1.1, w.1 ⊆ v.1 := by
    intro w hw
    rcases hnested w hw v hv with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax w hw)).symm.subset
  refine ⟨v, hv, hsub, ?_⟩
  have hinj : Set.InjOn (fun w : M.step.Vertex => w.1.card) (u.1.1 : Set M.step.Vertex) := by
    intro a ha b hb heq
    apply Subtype.ext
    rcases hnested a ha b hb with h | h
    · exact Finset.eq_of_subset_of_card_le h heq.ge
    · exact (Finset.eq_of_subset_of_card_le h heq.le).symm
  have hmaps : ∀ w ∈ u.1.1, w.1.card ∈ Finset.Icc 1 v.1.card := by
    intro w hw
    exact Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr (M.complex.isRelLowerSet_faces.prop_of_mem w.2), hmax w hw⟩
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [u.2] at hcard
  simpa using hcard

/-- A top-dimensional flag in the boundary of a face has one and only one
original facet as parent. -/
theorem exists_unique_parent_facet (M : BarycentricModel K) {k : ℕ}
    (s : Cell M.complex (k + 1)) (u : Cell M.step.complex k)
    (hproper : ∀ w ∈ u.1.1, w.1 ⊂ s.1.1) :
    ∃! t : Cell M.complex k,
      t.1.1 ⊆ s.1.1 ∧ ∀ w ∈ u.1.1, w.1 ⊆ t.1.1 := by
  classical
  obtain ⟨v, hv, hsub, hcard⟩ := M.exists_max_face u
  have hlt := Finset.card_lt_card (hproper v hv)
  rw [s.2] at hlt
  have hvcard : v.1.card = k + 1 := by omega
  let t : Cell M.complex k := ⟨v, hvcard⟩
  refine ⟨t, ⟨(hproper v hv).subset, hsub⟩, ?_⟩
  intro t' ht'
  apply cell_vertices_injective
  have hvt : v.1 ⊆ t'.1.1 := ht'.2 v hv
  exact (Finset.eq_of_subset_of_card_le hvt (by rw [hvcard, t'.2])).symm

end SharpTopologicalOverlap.Geometry.BarycentricModel
