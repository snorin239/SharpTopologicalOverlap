module

public import SharpTopologicalOverlap.Simplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness
public import TauCeti.Analysis.Convex.Interpolation

/-! # Continuous interpolation on common subdivision vertices

A placement is specified once on the abstract vertex type. Its interpolation
therefore agrees on intersecting source faces. This file constructs that global
continuous map and proves the uniform error bound for changing a placement.
Transport through TauCeti's edgewise subdivision homeomorphism gives the same
construction on the original realization.
-/

@[expose] public noncomputable section

open AbstractSimplicialComplex Finsupp

namespace SharpTopologicalOverlap.Geometry

variable {Q E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Barycentric interpolation of a single placement on all abstract vertices. -/
def interpolate (K : AbstractSimplicialComplex Q) (y : Q → E) (x : K.Realization) : E :=
  x.1.sum (fun q r => r • y q)

theorem interpolate_eq_sum [Fintype Q] (K : AbstractSimplicialComplex Q)
    (y : Q → E) (x : K.Realization) :
    interpolate K y x = ∑ q, x.1 q • y q := by
  exact Finsupp.sum_fintype _ _ (by simp)

theorem continuous_interpolate [Fintype Q] (K : AbstractSimplicialComplex Q) (y : Q → E) :
    Continuous (interpolate K y) := by
  simp only [funext (interpolate_eq_sum K y)]
  exact continuous_finsetSum _ (fun q _ =>
    ((continuous_apply q).comp (continuous_realization_coe K)).smul continuous_const)

@[simp] theorem interpolate_vertex (K : AbstractSimplicialComplex Q) (y : Q → E) (q : Q) :
    interpolate K y (AbstractSimplicialComplex.vertex K q) = y q := by
  simp [interpolate]

theorem interpolate_sub (K : AbstractSimplicialComplex Q) (y z : Q → E) (x : K.Realization) :
    interpolate K y x - interpolate K z x = interpolate K (fun q => y q - z q) x := by
  simp [interpolate, Finsupp.sum, Finset.sum_sub_distrib, smul_sub]

/-- A uniform change of the vertices gives the same uniform change of the interpolation. -/
theorem norm_interpolate_sub_le (K : AbstractSimplicialComplex Q) (y z : Q → E)
    {ε : ℝ} (hyz : ∀ q, ‖y q - z q‖ ≤ ε) (x : K.Realization) :
    ‖interpolate K y x - interpolate K z x‖ ≤ ε := by
  rw [interpolate_sub, interpolate, Finsupp.sum]
  exact norm_sum_smul_le
    (fun q _ => Realization.nonneg K x q)
    (by simpa [Finsupp.sum] using Realization.sum_eq_one K x)
    (fun q _ => hyz q)

/-- The interpolated image of a face lies in the hull of its placed vertices. -/
theorem interpolate_mem_convexHull (K : AbstractSimplicialComplex Q) (y : Q → E)
    (σ : Finset Q) (x : K.Realization) (hx : x.1.support ⊆ σ) :
    interpolate K y x ∈ convexHull ℝ (y '' (σ : Set Q)) := by
  rw [interpolate, Finsupp.sum]
  exact (convex_convexHull ℝ _).sum_mem
    (fun q _ => Realization.nonneg K x q)
    (by simpa [Finsupp.sum] using Realization.sum_eq_one K x)
    (fun q hq => subset_convexHull ℝ _ ⟨q, hx hq, rfl⟩)

section Edgewise

variable [LinearOrder Q] (K : AbstractSimplicialComplex Q) {r : ℕ}

/-- The interpolation transported back to the original source realization. -/
def edgewiseInterpolate (hr : r ≠ 0) (y : K.EdgewiseVertex r → E) : K.Realization → E :=
  interpolate (K.edgewiseSubdivision r) y ∘
    (K.edgewiseSubdivisionRealizationHomeomorph hr).symm

theorem continuous_edgewiseInterpolate [Fintype Q] (hr : r ≠ 0)
    (y : K.EdgewiseVertex r → E) : Continuous (edgewiseInterpolate K hr y) := by
  let : Fintype (K.EdgewiseVertex r) := Fintype.ofFinite _
  exact (continuous_interpolate _ y).comp
    (K.edgewiseSubdivisionRealizationHomeomorph hr).symm.continuous

@[simp] theorem edgewiseInterpolate_map (hr : r ≠ 0) (y : K.EdgewiseVertex r → E)
    (x : (K.edgewiseSubdivision r).Realization) :
    edgewiseInterpolate K hr y (K.edgewiseSubdivisionRealizationMap r x) =
      interpolate (K.edgewiseSubdivision r) y x := by
  unfold edgewiseInterpolate
  dsimp only [Function.comp_apply]
  rw [← K.edgewiseSubdivisionRealizationHomeomorph_apply hr x]
  rw [Homeomorph.symm_apply_apply]

/-- Uniform errors of subdivision placements remain uniform on the original space. -/
theorem norm_edgewiseInterpolate_sub_le (hr : r ≠ 0)
    (y z : K.EdgewiseVertex r → E) {ε : ℝ} (hyz : ∀ q, ‖y q - z q‖ ≤ ε)
    (x : K.Realization) :
    ‖edgewiseInterpolate K hr y x - edgewiseInterpolate K hr z x‖ ≤ ε :=
  norm_interpolate_sub_le _ y z hyz _

/-- An active subdivision vertex of a point of an original face uses only
vertices of that original face. -/
theorem edgewise_active_vertex_entries_subset
    (x : (K.edgewiseSubdivision r).Realization) {σ : Finset Q}
    (hx : (K.edgewiseSubdivisionRealizationMap r x).1.support ⊆ σ)
    {u : K.EdgewiseVertex r} (hu : u ∈ x.1.support) :
    ∀ l, u.1 l ∈ σ := by
  classical
  intro l
  apply hx
  apply Finsupp.mem_support_iff.mpr
  have hnonneg (v : K.EdgewiseVertex r) (i : Q) : 0 ≤ TauCeti.edgewisePoint v.1 i := by
    rw [TauCeti.edgewisePoint_apply]
    positivity
  have hup : 0 < x.1 u := Realization.pos_of_mem_support _ x hu
  have hui : 0 < TauCeti.edgewisePoint u.1 (u.1 l) := by
    apply lt_of_le_of_ne (hnonneg u (u.1 l))
    symm
    apply Finsupp.mem_support_iff.mp
    rw [TauCeti.support_edgewisePoint]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ l)
  have hsum : x.1 u * TauCeti.edgewisePoint u.1 (u.1 l) ≤
      (K.edgewiseSubdivisionRealizationMap r x).1 (u.1 l) := by
    rw [edgewiseSubdivisionRealizationMap_val]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.single_le_sum
      (fun v _ => mul_nonneg (Realization.nonneg _ x v) (hnonneg v (u.1 l))) hu
  exact ne_of_gt ((mul_pos hup hui).trans_le hsum)

/-- The global interpolation on an original closed face uses only placed
subdivision vertices belonging to that same face. -/
theorem edgewiseInterpolate_mem_convexHull (hr : r ≠ 0)
    (y : K.EdgewiseVertex r → E) (σ : Finset Q) (x : K.Realization)
    (hx : x.1.support ⊆ σ) :
    edgewiseInterpolate K hr y x ∈
      convexHull ℝ (y '' {u : K.EdgewiseVertex r | ∀ l, u.1 l ∈ σ}) := by
  let x' := (K.edgewiseSubdivisionRealizationHomeomorph hr).symm x
  have hxmap : K.edgewiseSubdivisionRealizationMap r x' = x := by
    rw [← K.edgewiseSubdivisionRealizationHomeomorph_apply hr x']
    exact Homeomorph.apply_symm_apply _ x
  have hx' : (K.edgewiseSubdivisionRealizationMap r x').1.support ⊆ σ := hxmap ▸ hx
  apply convexHull_mono (Set.image_mono (fun u hu =>
    edgewise_active_vertex_entries_subset K x' hx' hu))
  exact interpolate_mem_convexHull (K.edgewiseSubdivision r) y x'.1.support x'
    (Finset.Subset.refl _)

/-- The mesh bound in the original finite coordinate space. -/
theorem norm_edgewisePoint_sub_le [Fintype Q]
    {ρ : Finset (K.EdgewiseVertex r)} (hρ : ρ ∈ K.edgewiseSubdivision r)
    {u v : K.EdgewiseVertex r} (hu : u ∈ ρ) (hv : v ∈ ρ) :
    ‖(TauCeti.edgewisePoint u.1 : Q → ℝ) - (TauCeti.edgewisePoint v.1 : Q → ℝ)‖ ≤
      (r : ℝ)⁻¹ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have h := PreAbstractSimplicialComplex.norm_edgewisePoint_sub_edgewisePoint_le
    hρ hu hv (Finset.univ : Finset Q)
  have hi := norm_le_pi_norm
    (fun j : (Finset.univ : Finset Q) =>
      TauCeti.edgewisePoint u.1 j - TauCeti.edgewisePoint v.1 j)
    ⟨i, Finset.mem_univ i⟩
  exact hi.trans h

/-- Any continuous map on a finite complex is uniformly approximated by a single
placement on a sufficiently fine coherent edgewise subdivision. -/
theorem exists_edgewiseInterpolate_approx [Fintype Q]
    (f : K.Realization → E) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (hr : r ≠ 0), ∀ x : K.Realization,
      ‖edgewiseInterpolate K hr
          (fun u => f (K.edgewiseSubdivisionRealizationMap r
            (AbstractSimplicialComplex.vertex (K.edgewiseSubdivision r) u))) x - f x‖ < ε := by
  classical
  let e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  let : CompactSpace (Set.range fun x : K.Realization => (x.1 : Q → ℝ)) := e.compactSpace
  let F : (Set.range fun x : K.Realization => (x.1 : Q → ℝ)) → E := f ∘ e.symm
  have hF : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous (hf.comp e.symm.continuous)
  obtain ⟨δ, hδ, hsmall⟩ := hF.exists_pos_forall_norm_sum_smul_sub_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  let r := N + 1
  have hr : r ≠ 0 := Nat.succ_ne_zero N
  have hinv : (r : ℝ)⁻¹ < δ := by
    apply inv_lt_of_inv_lt₀ hδ
    exact hN.trans (by simp [r])
  refine ⟨r, hr, ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := K.edgewiseSubdivisionRealizationMap_surjective hr q
  rw [edgewiseInterpolate_map]
  let p : x.1.support → Set.range (fun x : K.Realization => (x.1 : Q → ℝ)) :=
    fun u => e (K.edgewiseSubdivisionRealizationMap r
      (AbstractSimplicialComplex.vertex (K.edgewiseSubdivision r) u.1))
  let w : x.1.support → ℝ := fun u => x.1 u.1
  have hw₀ : ∀ u, 0 ≤ w u := fun u => Realization.nonneg _ x u.1
  have hw₁ : ∑ u, w u = 1 := by
    simpa only [w, Finset.sum_coe_sort, Finsupp.sum] using
      Realization.sum_eq_one (K.edgewiseSubdivision r) x
  have hp : ∀ u v, ‖(p u : Q → ℝ) - p v‖ ≤ δ := by
    intro u v
    simp only [p, e, coe_realizationHomeomorphRange_apply,
      edgewiseSubdivisionRealizationMap_vertex]
    exact (norm_edgewisePoint_sub_le K (support_mem _ x) u.2 v.2).trans hinv.le
  have hq : (e (K.edgewiseSubdivisionRealizationMap r x) : Q → ℝ) =
      ∑ u, w u • (p u : Q → ℝ) := by
    ext i
    simp only [p, e, coe_realizationHomeomorphRange_apply,
      edgewiseSubdivisionRealizationMap_vertex, w]
    rw [edgewiseSubdivisionRealizationMap_val]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply]
    exact (Finset.sum_coe_sort x.1.support
      (fun u => x.1 u * TauCeti.edgewisePoint u.1 i)).symm
  have h := hsmall p w hw₀ hw₁ hp (e (K.edgewiseSubdivisionRealizationMap r x)) hq
  have hsum : (∑ u : x.1.support, w u • F (p u)) =
      interpolate (K.edgewiseSubdivision r)
        (fun u => f (K.edgewiseSubdivisionRealizationMap r
          (AbstractSimplicialComplex.vertex (K.edgewiseSubdivision r) u))) x := by
    simp only [w, F, p, Function.comp_apply, Homeomorph.symm_apply_apply,
      interpolate, Finsupp.sum]
    exact Finset.sum_coe_sort x.1.support (fun u : K.EdgewiseVertex r =>
      x.1 u • f (K.edgewiseSubdivisionRealizationMap r
        (AbstractSimplicialComplex.vertex (K.edgewiseSubdivision r) u)))
  rw [hsum] at h
  simpa only [F, Function.comp_apply, Homeomorph.symm_apply_apply] using h

end Edgewise

end SharpTopologicalOverlap.Geometry
