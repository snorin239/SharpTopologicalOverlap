module

public import SharpTopologicalOverlap.Geometry.BarycentricApproximation
public import SharpTopologicalOverlap.Geometry.StrongGeneralPosition
public import SharpTopologicalOverlap.Skeleton
public import SharpTopologicalOverlap.Geometry.BarycentricGeometry
public import SharpTopologicalOverlap.Geometry.GenericPlacements
public import SharpTopologicalOverlap.Intersection.Matching
public import Mathlib.Topology.MetricSpace.Thickening

/-! # The first source approximation in strong general position -/

@[expose] public noncomputable section

open AbstractSimplicialComplex Set

namespace SharpTopologicalOverlap.Geometry

variable {n d : ℕ}

/-- All actual faces of a finite barycentric model, keeping source indices. -/
def BarycentricModel.faceFamily {V : Type*} {K : AbstractSimplicialComplex V}
    (M : BarycentricModel K) : Finset (Finset M.Vertex) := by
  classical
  exact (Set.toFinite M.complex.faces).toFinset

@[simp] theorem BarycentricModel.mem_faceFamily {V : Type*} {K : AbstractSimplicialComplex V}
    (M : BarycentricModel K) (ρ : Finset M.Vertex) :
    ρ ∈ M.faceFamily ↔ ρ ∈ M.complex := by
  classical
  change ρ ∈ (Set.toFinite M.complex.faces).toFinset ↔ ρ ∈ M.complex.faces
  simp

/-- Shared-vertex barycentric interpolation, on the paper's coordinate skeleton. -/
def barycentricSourceMap
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d)) :
    Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d) :=
  M.interpolation y ∘ (skeletonRealizationHomeomorph d).symm

theorem continuous_barycentricSourceMap
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d)) : Continuous (barycentricSourceMap M y) :=
  (M.continuous_interpolation y).comp (skeletonRealizationHomeomorph d).symm.continuous

theorem barycentricSourceMap_facePoint
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d))
    (ρ : TauCeti.SetLike.Face M.complex) (w : Simplex ρ.1) :
    barycentricSourceMap M y (skeletonRealizationHomeomorph d (M.facePoint ρ w)) =
      ∑ q : ρ.1, w.weights q • y q := by
  simp only [barycentricSourceMap, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact M.interpolation_facePoint y ρ w

/-- A fine geometric hull carried by an original source face is genuinely
contained in that original face's image under the constructed source map. -/
theorem fine_hull_subset_sourceFace_image
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d))
    (ρ : TauCeti.SetLike.Face M.complex) (σ : Finset (Fin n))
    (hσ : ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ) :
    convexHull ℝ (y '' (ρ.1 : Set M.Vertex)) ⊆ barycentricSourceMap M y '' skeletonFace d σ := by
  classical
  let : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) := Convexity.ConvexSpace.ofModule
  intro z hz
  have hrange : y '' (ρ.1 : Set M.Vertex) = Set.range (fun q : ρ.1 => y q) := by ext p; simp
  rw [hrange, convexHull_range_eq_range_affineMapMk] at hz
  obtain ⟨w, hw⟩ := hz
  refine ⟨skeletonRealizationHomeomorph d (M.facePoint ρ w), ?_, ?_⟩
  · exact (mem_face_skeletonRealizationHomeomorph _ σ).mpr (M.facePoint_support_subset ρ σ hσ w)
  · rw [barycentricSourceMap_facePoint]
    simpa only [Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype] using hw

/-- Strong general position for the images of the original closed source faces. -/
def SourceStrongGeneralPosition (g : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ F : Finset (Finset (Fin n)), AdmissibleStrongFamily d F →
    (∀ σ ∈ F, σ.card ≤ d + 1) →
    ¬ ∃ w, ∀ σ ∈ F, w ∈ g '' skeletonFace d σ

theorem sourceStrongGeneralPosition_iff
    (g : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)) :
    SourceStrongGeneralPosition g ↔ SharpTopologicalOverlap.StrongGeneralPosition g := by
  constructor
  · intro h F hfaces hdis hcard hdim
    exact h F ⟨(fun σ hσ => (hfaces σ hσ).1), hdis, hcard, hdim⟩
      (fun σ hσ => (hfaces σ hσ).2)
  · intro h F hF hcard
    exact h F (fun σ hσ => ⟨hF.1 σ hσ, hcard σ hσ⟩) hF.2.1 hF.2.2.1 hF.2.2.2

private theorem fineFaces_disjoint_of_original_disjoint
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    {σ τ : Finset (Fin n)} (hστ : Disjoint σ τ)
    (x z : M.complex.Realization)
    (hx : (M.homeomorph x).1.support ⊆ σ)
    (hz : (M.homeomorph z).1.support ⊆ τ) : Disjoint x.1.support z.1.support := by
  apply Finset.disjoint_left.mpr
  intro q hqx hqz
  have hqx' := M.active_vertex_support_subset x hx hqx
  have hqz' := M.active_vertex_support_subset z hz hqz
  obtain ⟨v, hv⟩ := (skeletonComplex (Fin n) d).isRelLowerSet_faces.prop_of_mem
    (support_mem _ (M.vertexPoint q))
  exact Finset.disjoint_left.mp hστ (hqx' hv) (hqz' hv)

/-- The set-family G1 condition also applies to an indexed disjoint family;
nonemptiness and disjointness make the indexing injective. -/
theorem StrongGeneralPositionOn.no_common_hulls_indexed
    {Q I : Type*} [Fintype I] {S : Finset (Finset Q)}
    {y : Q → EuclideanSpace ℝ (Fin d)} (hy : StrongGeneralPositionOn S y)
    (A : I → Finset Q) (hAS : ∀ i, A i ∈ S) (hA : ∀ i, (A i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hI : 2 ≤ Fintype.card I)
    (hdim : ∑ i, ((A i).card - 1) < d * (Fintype.card I - 1)) :
    ¬ ∃ w, ∀ i, w ∈ convexHull ℝ (y '' (A i : Set Q)) := by
  classical
  have hinj : Function.Injective A := by
    intro i j hij
    by_contra hne
    obtain ⟨q, hq⟩ := hA i
    exact Finset.disjoint_left.mp (hdis hne) hq (hij ▸ hq)
  let F := Finset.univ.image A
  have hFS : F ⊆ S := by
    intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact hAS i
  have hcard : F.card = Fintype.card I := by
    change (Finset.univ.image A).card = Fintype.card I
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hF : AdmissibleStrongFamily d F := by
    refine ⟨?_, ?_, by simpa only [hcard] using hI, ?_⟩
    · intro B hB
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact hA i
    · intro B hB C hC hBC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
      exact hdis (fun h => hBC (congrArg A h))
    · rw [hcard]
      change (∑ B ∈ Finset.univ.image A, (B.card - 1)) < _
      rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
      exact hdim
  rintro ⟨w, hw⟩
  apply hy.no_common_hulls F hFS hF
  refine ⟨w, fun B hB => ?_⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
  exact hw i

/-- G1 on actual fine faces implies strong general position on the original
source faces. The fine-face dimension estimate follows from nondegeneracy
of the actual coordinate cells. -/
theorem sourceStrong_of_modelStrong
    (M : BarycentricModel (skeletonComplex (Fin n) d))
    (y : M.Vertex → EuclideanSpace ℝ (Fin d))
    (hy : StrongGeneralPositionOn M.faceFamily y) :
    SourceStrongGeneralPosition (barycentricSourceMap M y) := by
  classical
  intro F hF _hFcard
  rintro ⟨w, hw⟩
  have hz : ∀ σ : F, ∃ z ∈ skeletonFace d σ.1, barycentricSourceMap M y z = w :=
    fun σ => hw σ.1 σ.2
  choose z hz hzy using hz
  let x (σ : F) := M.homeomorph.symm ((skeletonRealizationHomeomorph d).symm (z σ))
  have hxmap (σ : F) : M.homeomorph (x σ) =
      (skeletonRealizationHomeomorph d).symm (z σ) := M.homeomorph.apply_symm_apply _
  have hx (σ : F) : (M.homeomorph (x σ)).1.support ⊆ σ.1 := by
    rw [hxmap]
    apply (mem_face_skeletonRealizationHomeomorph _ σ.1).mp
    simpa only [Homeomorph.apply_symm_apply] using hz σ
  let A (σ : F) : Finset M.Vertex := (x σ).1.support
  have hAface (σ : F) : A σ ∈ M.complex := support_mem _ (x σ)
  have hAne (σ : F) : (A σ).Nonempty := M.complex.isRelLowerSet_faces.prop_of_mem (hAface σ)
  have hAcard (σ : F) : (A σ).card ≤ σ.1.card :=
    M.card_le_of_support_subset ⟨A σ, hAface σ⟩ σ.1
      (fun q hq => M.active_vertex_support_subset (x σ) (hx σ) hq)
  have hdis : Pairwise (fun σ τ : F => Disjoint (A σ) (A τ)) := by
    intro σ τ hne
    exact fineFaces_disjoint_of_original_disjoint M
      (hF.2.1 σ.2 τ.2 (fun h => hne (Subtype.ext h))) (x σ) (x τ) (hx σ) (hx τ)
  have hI : 2 ≤ Fintype.card F := by simpa using hF.2.2.1
  have hdim : ∑ σ : F, ((A σ).card - 1) < d * (Fintype.card F - 1) := by
    have hle := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset F)) =>
      Nat.sub_le_sub_right (hAcard σ) 1)
    have hstrict : ∑ σ : F, (σ.1.card - 1) < d * (Fintype.card F - 1) := by
      rw [Fintype.card_coe, Finset.sum_coe_sort F (fun σ : Finset (Fin n) => σ.card - 1)]
      exact hF.2.2.2
    exact hle.trans_lt hstrict
  apply hy.no_common_hulls_indexed A (fun σ => (M.mem_faceFamily (A σ)).mpr (hAface σ))
    hAne hdis hI hdim
  refine ⟨w, fun σ => ?_⟩
  have himage := interpolate_mem_convexHull M.complex y (A σ) (x σ) (Finset.Subset.refl _)
  have hvalue : Geometry.interpolate M.complex y (x σ) = w := by
    have heq := M.interpolation_map y (x σ)
    rw [hxmap] at heq
    exact heq.symm.trans (hzy σ)
  exact hvalue ▸ himage

/-- The first approximation in Appendix A: an actual shared-vertex
barycentric interpolation, uniformly close to `f`, whose original closed-face
images satisfy strong general position. -/
theorem exists_first_source_approximation
    (f : Skeleton (Fin n) d → EuclideanSpace ℝ (Fin d)) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∃ y : (barycentricModel (skeletonComplex (Fin n) d) j).Vertex →
        EuclideanSpace ℝ (Fin d),
      Continuous (barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) y) ∧
      (∀ x, ‖barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) y x -
        f x‖ < ε) ∧
      StrongGeneralPositionOn (barycentricModel (skeletonComplex (Fin n) d) j).faceFamily y ∧
      SourceStrongGeneralPosition
        (barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) y) := by
  classical
  let K := skeletonComplex (Fin n) d
  let e := skeletonRealizationHomeomorph (V := Fin n) d
  let f' : K.Realization → EuclideanSpace ℝ (Fin d) := f ∘ e
  have hf' : Continuous f' := hf.comp e.continuous
  have hdim : ∀ σ ∈ K, σ.card ≤ d + 1 := fun σ hσ => (mem_skeletonComplex.mp hσ).2
  obtain ⟨j, hj⟩ := exists_barycentric_interpolation_approx K d hdim f' hf' (half_pos hε)
  let M := barycentricModel K j
  let y₀ : M.Vertex → EuclideanSpace ℝ (Fin d) := fun q => f' (M.vertexPoint q)
  obtain ⟨y, hynear, hystrong⟩ := exists_strongGeneralPositionOn M.faceFamily y₀ (half_pos hε)
  refine ⟨j, y, continuous_barycentricSourceMap M y, ?_, hystrong,
    sourceStrong_of_modelStrong M y hystrong⟩
  intro x
  have hfirst : ‖M.interpolation y₀ (e.symm x) - f x‖ < ε / 2 := by
    simpa only [y₀, f', Function.comp_apply, Homeomorph.apply_symm_apply] using hj (e.symm x)
  have hsecond : ‖M.interpolation y (e.symm x) - M.interpolation y₀ (e.symm x)‖ ≤ ε / 2 :=
    M.norm_interpolation_sub_le y y₀ (fun q => (hynear q).le) _
  have htri := norm_add_le
    (M.interpolation y (e.symm x) - M.interpolation y₀ (e.symm x))
    (M.interpolation y₀ (e.symm x) - f x)
  have heq : M.interpolation y (e.symm x) - M.interpolation y₀ (e.symm x) +
      (M.interpolation y₀ (e.symm x) - f x) = M.interpolation y (e.symm x) - f x := by abel
  rw [heq] at htri
  exact htri.trans_lt (by linarith)

/-- The second perturbation remains on the identical source subdivision and
satisfies all four generic conditions relative to the actual target array. -/
theorem exists_second_source_approximation {I : Type*} [Fintype I] {b : I → ℕ}
    (j : ℕ)
    (yg : (barycentricModel (skeletonComplex (Fin n) d) j).Vertex →
      EuclideanSpace ℝ (Fin d))
    (t : ∀ i : I, Affine.Simplex ℝ (EuclideanSpace ℝ (Fin d)) (b i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ yh : (barycentricModel (skeletonComplex (Fin n) d) j).Vertex →
        EuclideanSpace ℝ (Fin d),
      GenericPlacement (barycentricModel (skeletonComplex (Fin n) d) j).faceFamily t yh ∧
      Continuous (barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) yh) ∧
      ∀ x, ‖barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) yh x -
        barycentricSourceMap (barycentricModel (skeletonComplex (Fin n) d) j) yg x‖ < ε := by
  let K := skeletonComplex (Fin n) d
  let M := barycentricModel K j
  have hS : ∀ A ∈ M.faceFamily, A.Nonempty := fun A hA =>
    M.complex.isRelLowerSet_faces.prop_of_mem ((M.mem_faceFamily A).mp hA)
  have hdim : ∀ σ ∈ K, σ.card ≤ d + 1 := fun σ hσ => (mem_skeletonComplex.mp hσ).2
  have hcard : ∀ A ∈ M.faceFamily, A.card ≤ d + 1 := fun A hA =>
    barycentricModel_faceCardBound K d hdim j A ((M.mem_faceFamily A).mp hA)
  obtain ⟨yh, hynear, hygeneric⟩ := exists_genericPlacement M.faceFamily hS hcard t yg (half_pos hε)
  refine ⟨yh, hygeneric, continuous_barycentricSourceMap M yh, fun x => ?_⟩
  exact (M.norm_interpolation_sub_le yh yg (fun q => (hynear q).le) _).trans_lt (half_lt_self hε)

/-- Uniformly close source maps remain inside any set containing the
corresponding closed neighborhood of the first map's image. -/
theorem range_subset_of_near_cthickening {X E : Type*}
    [NormedAddCommGroup E] (g h : X → E) {ε : ℝ} {D : Set E}
    (hnear : ∀ x, ‖h x - g x‖ < ε)
    (hD : Metric.cthickening ε (Set.range g) ⊆ D) : Set.range h ⊆ D := by
  rintro z ⟨x, rfl⟩
  apply hD
  exact Metric.mem_cthickening_of_dist_le (h x) (g x) ε (Set.range g) ⟨x, rfl⟩
    (by simpa only [dist_eq_norm] using (hnear x).le)

end SharpTopologicalOverlap.Geometry
