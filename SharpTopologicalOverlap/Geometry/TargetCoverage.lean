module

public import SharpTopologicalOverlap.Geometry.TargetGeometry
public import SharpTopologicalOverlap.Geometry.PlacementAvoidance

/-! # Coverage and unique top cells of the actual target patch

The barycentric model covers the original distinguished facet by its own
canonical homeomorphism. A point missing all lower patch hulls has a full
top-dimensional fine carrier. Injectivity of the physical realization of the
distinguished facet makes that carrier unique.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.TargetCoverage

open AbstractSimplicialComplex Set
open SharpTopologicalOverlap.Simplicial
open TargetGeometry

attribute [local instance] Convexity.ConvexSpace.ofModule

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every physical fine-hull point comes from a point of that very abstract
fine face, with exactly the corresponding physical coordinates. -/
theorem lift_hull_point (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d))
    (ρ : TauCeti.SetLike.Face M.complex) {x : E}
    (hx : x ∈ convexHull ℝ (position D M '' (ρ.1 : Set M.Vertex))) :
    ∃ z : M.complex.Realization, z.1.support ⊆ ρ.1 ∧
      affineMap D (M.homeomorph z).1 = x := by
  classical
  have hrange : position D M '' (ρ.1 : Set M.Vertex) =
      Set.range (fun q : ρ.1 => position D M q) := by ext p; simp
  rw [hrange, convexHull_range_eq_range_affineMapMk] at hx
  obtain ⟨w, hw⟩ := hx
  let z := faceInclusion M.complex ρ ((Finset.standardSimplexHomeomorph ρ.1).symm w)
  refine ⟨z, ?_, ?_⟩
  · rw [faceInclusion_val]
    exact StandardSimplex.support_subset _
  · change affineMap D (M.facePoint ρ w).1 = x
    rw [M.linearMap_facePoint]
    simpa only [position, Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using hw

/-- Every physical realized point lies in the physical hull of its actual
fine support face. -/
theorem physical_mem_support_hull (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (z : M.complex.Realization) :
    affineMap D (M.homeomorph z).1 ∈
      convexHull ℝ (position D M '' (z.1.support : Set M.Vertex)) := by
  have h := interpolate_mem_convexHull M.complex (position D M) z.1.support z
    (Finset.Subset.refl _)
  have heq : Geometry.interpolate M.complex (position D M) z =
      affineMap D (M.homeomorph z).1 := by
    rw [← M.interpolation_map (position D M) z]
    exact M.interpolation_linearMap (affineMap D) _
  exact heq ▸ h

/-- A top patch hull point missing all lower patch hulls has full fine
barycentric support in that top cell. -/
theorem lift_top_hull_point (D : Affine.Simplex ℝ E d) (M : BarycentricModel (sphere d))
    (x : E)
    (hlower : ∀ ρ : TauCeti.SetLike.Face M.complex, ρ.1.card ≤ d → InPatch M ρ.1 →
      x ∉ convexHull ℝ (position D M '' (ρ.1 : Set M.Vertex)))
    (τ : Cell M.complex d) (hτpatch : InPatch M τ.1.1)
    (hx : x ∈ convexHull ℝ (position D M '' (τ.1.1 : Set M.Vertex))) :
    ∃ z : M.complex.Realization, z.1.support = τ.1.1 ∧
      (M.homeomorph z).1.support ⊆ patch d ∧ affineMap D (M.homeomorph z).1 = x := by
  obtain ⟨z, hzsub, hzphysical⟩ := lift_hull_point D M τ.1 hx
  have hzpatch : InPatch M z.1.support := hτpatch.mono hzsub
  have hzeq : z.1.support = τ.1.1 := by
    by_contra hne
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hzsub, hne⟩)
    rw [τ.2] at hc
    have hsmall : z.1.support.card ≤ d := by omega
    exact hlower ⟨z.1.support, support_mem M.complex z⟩ hsmall hzpatch
      (hzphysical ▸ physical_mem_support_hull D M z)
  exact ⟨z, hzeq, M.homeomorph_support_subset z (patch d) hzpatch, hzphysical⟩

theorem sphere_face_card_bound (d : ℕ) : ∀ σ ∈ sphere d, σ.card ≤ d + 1 := by
  intro σ hσ
  have hp := (AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mp hσ).2
  have hc := Finset.card_lt_card hp
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- The actual fine target patch covers the target simplex. A point avoiding
all lower patch faces belongs to exactly one top-dimensional patch cell. -/
theorem existsUnique_top_patch_cell (D : Affine.Simplex ℝ E d) (i : ℕ)
    (x : E) (hx : x ∈ convexHull ℝ (Set.range D.points))
    (hlower : ∀ ρ : TauCeti.SetLike.Face (barycentricModel (sphere d) i).complex,
      ρ.1.card ≤ d → InPatch (barycentricModel (sphere d) i) ρ.1 →
        x ∉ convexHull ℝ (position D (barycentricModel (sphere d) i) '' (ρ.1 : Set _))) :
    ∃! τ : Cell (barycentricModel (sphere d) i).complex d,
      InPatch (barycentricModel (sphere d) i) τ.1.1 ∧
        x ∈ convexHull ℝ (position D (barycentricModel (sphere d) i) '' (τ.1.1 : Set _)) := by
  classical
  let M := barycentricModel (sphere d) i
  rw [convexHull_range_eq_range_affineMapMk] at hx
  obtain ⟨w, hw⟩ := hx
  let z := M.homeomorph.symm (patchPoint w)
  have hzmap : M.homeomorph z = patchPoint w := M.homeomorph.apply_symm_apply _
  have hzorig : (M.homeomorph z).1.support ⊆ patch d := by
    rw [hzmap]
    exact patchPoint_support_subset w
  have hzphysical : affineMap D (M.homeomorph z).1 = x := by
    rw [hzmap, affineMap_patchPoint]
    exact hw
  have hzpatch : InPatch M z.1.support := fun q hq =>
    M.active_vertex_support_subset z hzorig hq
  have hzsmall : z.1.support.card ≤ d + 1 :=
    barycentricModel_faceCardBound (sphere d) d (sphere_face_card_bound d) i _ (support_mem _ z)
  have hzcard : z.1.support.card = d + 1 := by
    by_contra hne
    have hsmall : z.1.support.card ≤ d := by omega
    exact hlower ⟨z.1.support, support_mem _ z⟩ hsmall hzpatch
      (hzphysical ▸ physical_mem_support_hull D M z)
  let τ₀ : Cell M.complex d := ⟨⟨z.1.support, support_mem _ z⟩, hzcard⟩
  have hτ₀ : InPatch M τ₀.1.1 ∧
      x ∈ convexHull ℝ (position D M '' (τ₀.1.1 : Set M.Vertex)) :=
    ⟨hzpatch, hzphysical ▸ physical_mem_support_hull D M z⟩
  refine ⟨τ₀, hτ₀, fun τ hτ => ?_⟩
  obtain ⟨u, husupport, huorig, huphysical⟩ := lift_top_hull_point D M x hlower τ hτ.1 hτ.2
  have hcoord : (M.homeomorph u).1 = (patchPoint w).1 :=
    affineMap_injective_on_patch_vectors D (Realization.sum_eq_one _ _)
      (Realization.sum_eq_one _ _) (last_eq_zero_of_support_subset_patch huorig)
      (patchPoint_last w) (huphysical.trans (by rw [affineMap_patchPoint]; exact hw.symm))
  have hueq : u = z := M.homeomorph.injective ((Subtype.ext hcoord).trans hzmap.symm)
  apply Subtype.ext
  apply Subtype.ext
  change τ.1.1 = z.1.support
  rw [← husupport, hueq]

/-- The same unique top-cell statement with the globally monotone target
carriers used by the cochain construction. -/
theorem existsUnique_top_targetCells (D : Affine.Simplex ℝ E d) (i : ℕ)
    (x : E) (hx : x ∈ convexHull ℝ (Set.range D.points))
    (hlower : ∀ ρ : TauCeti.SetLike.Face (barycentricModel (sphere d) i).complex,
      ρ.1.card ≤ d → InPatch (barycentricModel (sphere d) i) ρ.1 →
        x ∉ targetCells D (barycentricModel (sphere d) i) ρ.1) :
    ∃! τ : Cell (barycentricModel (sphere d) i).complex d,
      InPatch (barycentricModel (sphere d) i) τ.1.1 ∧
        x ∈ targetCells D (barycentricModel (sphere d) i) τ.1.1 := by
  have hav : ∀ ρ : TauCeti.SetLike.Face (barycentricModel (sphere d) i).complex,
      ρ.1.card ≤ d → InPatch (barycentricModel (sphere d) i) ρ.1 →
        x ∉ convexHull ℝ (position D (barycentricModel (sphere d) i) '' (ρ.1 : Set _)) := by
    intro ρ hρ hp
    simpa only [targetCells_eq_hull_of_inPatch D _ hp] using hlower ρ hρ hp
  obtain ⟨τ, hτ, huniq⟩ := existsUnique_top_patch_cell D i x hx hav
  refine ⟨τ, ⟨hτ.1, ?_⟩, fun σ hσ => huniq σ ⟨hσ.1, ?_⟩⟩
  · simpa only [targetCells_eq_hull_of_inPatch D _ hτ.1] using hτ.2
  · simpa only [targetCells_eq_hull_of_inPatch D _ hσ.1] using hσ.2

/-- Degree-indexed lower-dimensional avoidance, in the form supplied by G3. -/
theorem existsUnique_top_targetCells_of_cell_avoidance
    (D : Affine.Simplex ℝ E d) (i : ℕ) (x : E)
    (hx : x ∈ convexHull ℝ (Set.range D.points))
    (hlower : ∀ p : ℕ, p < d →
      ∀ ρ : Cell (barycentricModel (sphere d) i).complex p,
        InPatch (barycentricModel (sphere d) i) ρ.1.1 →
          x ∉ targetCells D (barycentricModel (sphere d) i) ρ.1.1) :
    ∃! τ : Cell (barycentricModel (sphere d) i).complex d,
      InPatch (barycentricModel (sphere d) i) τ.1.1 ∧
        x ∈ targetCells D (barycentricModel (sphere d) i) τ.1.1 := by
  apply existsUnique_top_targetCells D i x hx
  intro ρ hcard hp
  have hpos : 0 < ρ.1.card := Finset.card_pos.mpr
    ((barycentricModel (sphere d) i).complex.isRelLowerSet_faces.prop_of_mem ρ.2)
  have hdim : ρ.1.card - 1 < d := by omega
  let c : Cell (barycentricModel (sphere d) i).complex (ρ.1.card - 1) :=
    ⟨ρ, (Nat.sub_add_cancel (by omega : 1 ≤ ρ.1.card)).symm⟩
  exact hlower _ hdim c hp

end SharpTopologicalOverlap.Geometry.TargetCoverage
