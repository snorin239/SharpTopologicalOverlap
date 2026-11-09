module

public import SharpTopologicalOverlap.Geometry.BarycentricModel
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-! # Mesh and continuous affine approximation on one coherent barycentric model -/

@[expose] public noncomputable section

open AbstractSimplicialComplex TauCeti.SetLike Finsupp Convexity
open scoped Topology

namespace SharpTopologicalOverlap.Geometry

universe u
variable {V : Type u}

namespace BarycentricModel
variable {K : AbstractSimplicialComplex V}
/-- The finite-coordinate form of the ambient linear map. -/
def coordinateMap (M : BarycentricModel K) : (M.Vertex →₀ ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun c v := M.linearMap c v
  map_add' c e := by ext v; simp
  map_smul' r c := by ext v; simp

/-- Original finite coordinates of a shared subdivision vertex. -/
def coordinates (M : BarycentricModel K) (q : M.Vertex) : V → ℝ := (M.vertexPoint q).1

@[simp] theorem coordinateMap_single (M : BarycentricModel K) (q : M.Vertex) :
    M.coordinateMap (Finsupp.single q 1) = M.coordinates q := by
  ext v
  simp [coordinateMap, coordinates]

theorem step_vertexPoint_val (M : BarycentricModel K)
    (σ : Face M.complex.toPreAbstractSimplicialComplex) :
    (M.step.vertexPoint σ).1 = M.linearMap (faceBarycenter M.complex σ) := by
  rw [M.step.vertexPoint_val]
  change M.linearMap (barycentricSubdivisionLinearMap M.complex (Finsupp.single σ 1)) = _
  rw [barycentricSubdivisionLinearMap_single]

/-- In the original coordinates each new vertex is the centroid of the old
vertices of the face indexing it. -/
theorem step_coordinates_centroid (M : BarycentricModel K)
    (σ : Face M.complex.toPreAbstractSimplicialComplex) :
    M.step.coordinates σ = σ.1.centroid ℝ M.coordinates := by
  classical
  have hsum := σ.1.sum_centroidWeights_eq_one_of_nonempty ℝ
    (M.complex.isRelLowerSet_faces.prop_of_mem σ.2)
  have hface : faceBarycenter M.complex σ =
      σ.1.centroid ℝ (fun q => Finsupp.single q 1) := by
    rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    ext q
    simp [faceBarycenter_apply, Finset.centroidWeights_apply, Finsupp.single_apply]
  have h := σ.1.map_affineCombination (fun q => Finsupp.single q 1)
    (σ.1.centroidWeights ℝ) hsum M.coordinateMap.toAffineMap
  have hcoords : M.step.coordinates σ = M.coordinateMap (faceBarycenter M.complex σ) := by
    ext v
    exact congrArg (fun c : V →₀ ℝ => c v) (step_vertexPoint_val M σ)
  rw [hcoords, hface, Finset.centroid_def, Finset.centroid_def]
  have hfun : M.coordinateMap ∘ (fun q => Finsupp.single q 1) = M.coordinates :=
    funext (M.coordinateMap_single)
  simpa only [LinearMap.coe_toAffineMap, hfun] using h

/-- A bound on the number of vertices of every actual model face. -/
def HasFaceCardBound (M : BarycentricModel K) (d : ℕ) : Prop :=
  ∀ σ ∈ M.complex, σ.card ≤ d + 1

/-- Pairwise original-coordinate distances on every actual model face. -/
def HasMesh [Fintype V] (M : BarycentricModel K) (D : ℝ) : Prop :=
  ∀ σ ∈ M.complex, ∀ q ∈ σ, ∀ r ∈ σ, dist (M.coordinates q) (M.coordinates r) ≤ D

theorem step_faceCardBound (M : BarycentricModel K) (d : ℕ) (hd : M.HasFaceCardBound d) :
    M.step.HasFaceCardBound d := by
  intro ρ hρ
  exact TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision hd hρ

theorem step_dist_le_of_subset [Fintype V] (M : BarycentricModel K) (d : ℕ)
    (hd : M.HasFaceCardBound d) {D : ℝ} (hD : 0 ≤ D) (hmesh : M.HasMesh D)
    (σ τ : Face M.complex.toPreAbstractSimplicialComplex) (hστ : σ.1 ⊆ τ.1) :
    dist (M.step.coordinates σ) (M.step.coordinates τ) ≤ (d : ℝ) / (d + 1) * D := by
  classical
  rw [step_coordinates_centroid, step_coordinates_centroid]
  have hσne := M.complex.isRelLowerSet_faces.prop_of_mem σ.2
  have hτne := M.complex.isRelLowerSet_faces.prop_of_mem τ.2
  have hcent := Finset.dist_centroid_centroid_le_of_subset
    (p := M.coordinates) (s := τ.1) (t := σ.1)
    (fun i hi j hj => hmesh τ.1 τ.2 i (Finset.mem_sdiff.mp hi).1 j (hστ hj)) hστ hσne
  apply hcent.trans
  apply mul_le_mul_of_nonneg_right _ hD
  have hτpos : (0 : ℝ) < τ.1.card := by exact_mod_cast hτne.card_pos
  have hσone : (1 : ℝ) ≤ σ.1.card := by exact_mod_cast hσne.card_pos
  have hτd : (τ.1.card : ℝ) ≤ d + 1 := by exact_mod_cast hd τ.1 τ.2
  have hdiv : (1 : ℝ) / (d + 1) ≤ (σ.1.card : ℝ) / τ.1.card := by
    apply (div_le_div_iff₀ (by positivity) hτpos).mpr
    nlinarith
  have hq : (d : ℝ) / (d + 1) = 1 - 1 / (d + 1) := by
    field_simp
    ring
  rw [hq]
  linarith

/-- One common barycentric subdivision shrinks every actual geometric simplex. -/
theorem step_mesh [Fintype V] (M : BarycentricModel K) (d : ℕ)
    (hd : M.HasFaceCardBound d) {D : ℝ} (hD : 0 ≤ D) (hmesh : M.HasMesh D) :
    M.step.HasMesh ((d : ℝ) / (d + 1) * D) := by
  intro ρ hρ σ hσ τ hτ
  have hnested := (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff'.mp hρ).2
  rcases hnested σ hσ τ hτ with hστ | hτσ
  · exact step_dist_le_of_subset M d hd hD hmesh σ τ hστ
  · rw [dist_comm]
    exact step_dist_le_of_subset M d hd hD hmesh τ σ hτσ

end BarycentricModel

theorem barycentricModel_faceCardBound [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (d : ℕ)
    (hd : ∀ σ ∈ K, σ.card ≤ d + 1) (j : ℕ) :
    (barycentricModel K j).HasFaceCardBound d := by
  induction j with
  | zero => exact hd
  | succ j ih => exact BarycentricModel.step_faceCardBound _ d ih

theorem barycentricModel_mesh [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (d : ℕ)
    (hd : ∀ σ ∈ K, σ.card ≤ d + 1) (j : ℕ) :
    (barycentricModel K j).HasMesh (((d : ℝ) / (d + 1)) ^ j) := by
  induction j with
  | zero =>
    intro σ hσ q hq r hr
    have hcoord (q : V) : (barycentricModel K 0).coordinates q =
        (Finsupp.single q (1 : ℝ) : V → ℝ) := by
      funext v
      change ((barycentricModel K 0).vertexPoint q).1 v = _
      rw [(barycentricModel K 0).vertexPoint_val]
      rfl
    rw [hcoord q, hcoord r, pow_zero]
    apply (dist_pi_le_iff (by positivity)).mpr
    intro v
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  | succ j ih =>
    rw [barycentricModel_succ, pow_succ']
    exact BarycentricModel.step_mesh _ d (barycentricModel_faceCardBound K d hd j)
      (by positivity) ih

namespace BarycentricModel

variable {K : AbstractSimplicialComplex V}
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interpolation on exactly the shared vertices of this barycentric model. -/
def interpolation (M : BarycentricModel K) (y : M.Vertex → E) : K.Realization → E :=
  Geometry.interpolate M.complex y ∘ M.homeomorph.symm

theorem continuous_interpolation (M : BarycentricModel K) (y : M.Vertex → E) :
    Continuous (M.interpolation y) :=
  (continuous_interpolate M.complex y).comp M.homeomorph.symm.continuous

@[simp] theorem interpolation_map (M : BarycentricModel K) (y : M.Vertex → E)
    (x : M.complex.Realization) :
    M.interpolation y (M.homeomorph x) = Geometry.interpolate M.complex y x := by
  simp [interpolation]

@[simp] theorem interpolation_vertexPoint (M : BarycentricModel K)
    (y : M.Vertex → E) (q : M.Vertex) : M.interpolation y (M.vertexPoint q) = y q := by
  simp [vertexPoint]

theorem norm_interpolation_sub_le (M : BarycentricModel K) (y z : M.Vertex → E)
    {ε : ℝ} (hyz : ∀ q, ‖y q - z q‖ ≤ ε) (x : K.Realization) :
    ‖M.interpolation y x - M.interpolation z x‖ ≤ ε :=
  norm_interpolate_sub_le M.complex y z hyz _

/-- Refining an ambient affine-coordinate placement reproduces that same
placement exactly. In particular the physical target map does not change
when the target simplex is barycentrically subdivided. -/
theorem interpolation_linearMap (M : BarycentricModel K)
    (L : (V →₀ ℝ) →ₗ[ℝ] E) (x : K.Realization) :
    M.interpolation (fun q => L (M.vertexPoint q).1) x = L x.1 := by
  obtain ⟨z, rfl⟩ := M.homeomorph.surjective x
  rw [M.interpolation_map, M.homeomorph_val_sum]
  simp only [Geometry.interpolate, Finsupp.sum, map_sum, map_smul]

/-- On any original face, interpolation uses only fine vertices of that same face. -/
theorem interpolation_mem_convexHull (M : BarycentricModel K) (y : M.Vertex → E)
    (σ : Finset V) (x : K.Realization) (hx : x.1.support ⊆ σ) :
    M.interpolation y x ∈
      convexHull ℝ (y '' {q : M.Vertex | (M.vertexPoint q).1.support ⊆ σ}) := by
  let x' := M.homeomorph.symm x
  have hx' : (M.homeomorph x').1.support ⊆ σ := by
    simpa only [x', Homeomorph.apply_symm_apply] using hx
  apply convexHull_mono (Set.image_mono (fun q hq =>
    M.active_vertex_support_subset x' hx' hq))
  exact interpolate_mem_convexHull M.complex y x'.1.support x' (Finset.Subset.refl _)

/-- The canonical parametrization of an actual fine face, transported to the
original realization, with its fine barycentric coordinates retained. -/
def facePoint (M : BarycentricModel K) (σ : Face M.complex.toPreAbstractSimplicialComplex)
    (w : Simplex σ.1) : K.Realization :=
  M.homeomorph (faceInclusion M.complex σ ((Finset.standardSimplexHomeomorph σ.1).symm w))

theorem continuous_facePoint (M : BarycentricModel K)
    (σ : Face M.complex.toPreAbstractSimplicialComplex) : Continuous (M.facePoint σ) :=
  M.homeomorph.continuous.comp ((continuous_faceInclusion M.complex σ).comp
    (Finset.standardSimplexHomeomorph σ.1).symm.continuous)

/-- A parametrized fine face stays in every original face carrying all
its shared vertices. This is the geometric form of the chain carrier. -/
theorem facePoint_support_subset (M : BarycentricModel K)
    (ρ : Face M.complex.toPreAbstractSimplicialComplex) (σ : Finset V)
    (hσ : ∀ q ∈ ρ.1, (M.vertexPoint q).1.support ⊆ σ) (w : Simplex ρ.1) :
    (M.facePoint ρ w).1.support ⊆ σ := by
  apply M.homeomorph_support_subset
  intro q hq
  have hqρ : q ∈ ρ.1 := by
    rw [faceInclusion_val] at hq
    exact StandardSimplex.support_subset ((Finset.standardSimplexHomeomorph ρ.1).symm w) hq
  exact hσ q hqρ

theorem interpolation_facePoint (M : BarycentricModel K) (y : M.Vertex → E)
    (σ : Face M.complex.toPreAbstractSimplicialComplex) (w : Simplex σ.1) :
    M.interpolation y (M.facePoint σ w) = ∑ q : σ.1, w.weights q • y q := by
  rw [facePoint, interpolation_map]
  change Finsupp.linearCombination ℝ y
    (faceInclusion M.complex σ ((Finset.standardSimplexHomeomorph σ.1).symm w)).1 = _
  rw [faceInclusion_val, Finset.standardSimplexHomeomorph_symm_val,
    Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

theorem linearMap_facePoint (M : BarycentricModel K)
    (L : (V →₀ ℝ) →ₗ[ℝ] E)
    (σ : Face M.complex.toPreAbstractSimplicialComplex) (w : Simplex σ.1) :
    L (M.facePoint σ w).1 = ∑ q : σ.1, w.weights q • L (M.vertexPoint q).1 := by
  rw [← M.interpolation_linearMap L, M.interpolation_facePoint]

end BarycentricModel

/-- Every continuous map on the original finite complex has a uniformly close
continuous affine interpolation on one coherent iterated barycentric subdivision. -/
theorem exists_barycentric_interpolation_approx [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (d : ℕ) (hd : ∀ σ ∈ K, σ.card ≤ d + 1)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Realization → E) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ x : K.Realization,
      ‖(barycentricModel K j).interpolation
        (fun q => f ((barycentricModel K j).vertexPoint q)) x - f x‖ < ε := by
  classical
  let e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  let : CompactSpace (Set.range fun x : K.Realization => (x.1 : V → ℝ)) := e.compactSpace
  let F : (Set.range fun x : K.Realization => (x.1 : V → ℝ)) → E := f ∘ e.symm
  have hF : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous (hf.comp e.symm.continuous)
  obtain ⟨δ, hδ, hsmall⟩ := hF.exists_pos_forall_norm_sum_smul_sub_lt hε
  have hfactor : (d : ℝ) / (d + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ hfactor
  let M := barycentricModel K j
  have hmesh : M.HasMesh (((d : ℝ) / (d + 1)) ^ j) := barycentricModel_mesh K d hd j
  refine ⟨j, fun q => ?_⟩
  obtain ⟨x, rfl⟩ := M.homeomorph.surjective q
  rw [M.interpolation_map]
  let p : x.1.support → Set.range (fun x : K.Realization => (x.1 : V → ℝ)) :=
    fun u => e (M.vertexPoint u.1)
  let w : x.1.support → ℝ := fun u => x.1 u.1
  have hw₀ : ∀ u, 0 ≤ w u := fun u => Realization.nonneg _ x u.1
  have hw₁ : ∑ u, w u = 1 := by
    simpa only [w, Finset.sum_coe_sort, Finsupp.sum] using Realization.sum_eq_one M.complex x
  have hp : ∀ u v, ‖(p u : V → ℝ) - p v‖ ≤ δ := by
    intro u v
    simp only [p, e, coe_realizationHomeomorphRange_apply]
    exact (hmesh x.1.support (support_mem M.complex x) u.1 u.2 v.1 v.2).trans hj.le
  have hq : (e (M.homeomorph x) : V → ℝ) = ∑ u, w u • (p u : V → ℝ) := by
    ext v
    simp only [p, e, coe_realizationHomeomorphRange_apply, w]
    rw [M.homeomorph_val_sum]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finset.sum_apply, Pi.smul_apply]
    exact (Finset.sum_coe_sort x.1.support (fun u => x.1 u * (M.vertexPoint u).1 v)).symm
  have h := hsmall p w hw₀ hw₁ hp (e (M.homeomorph x)) hq
  have hsum : (∑ u : x.1.support, w u • F (p u)) =
      Geometry.interpolate M.complex (fun u => f (M.vertexPoint u)) x := by
    simp only [w, F, p, Function.comp_apply, Homeomorph.symm_apply_apply,
      Geometry.interpolate, Finsupp.sum]
    exact Finset.sum_coe_sort x.1.support (fun u : M.Vertex => x.1 u • f (M.vertexPoint u))
  rw [hsum] at h
  simpa only [F, Function.comp_apply, Homeomorph.symm_apply_apply] using h

/-- A continuous physical placement of the original realization has uniformly
small pairwise vertex distances on all faces of a sufficiently fine actual
barycentric subdivision. -/
theorem exists_barycentric_vertex_image_mesh_lt [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (d : ℕ) (hd : ∀ σ ∈ K, σ.card ≤ d + 1)
    {Y : Type*} [PseudoMetricSpace Y] (f : K.Realization → Y) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ ρ ∈ (barycentricModel K j).complex,
      ∀ q ∈ ρ, ∀ r ∈ ρ,
        dist (f ((barycentricModel K j).vertexPoint q))
          (f ((barycentricModel K j).vertexPoint r)) < ε := by
  let e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  let : CompactSpace (Set.range fun x : K.Realization => (x.1 : V → ℝ)) := e.compactSpace
  let F : (Set.range fun x : K.Realization => (x.1 : V → ℝ)) → Y := f ∘ e.symm
  have hF : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous (hf.comp e.symm.continuous)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuous_iff.mp hF ε hε
  have hfactor : (d : ℝ) / (d + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ hfactor
  refine ⟨j, fun ρ hρ q hq r hr => ?_⟩
  let M := barycentricModel K j
  have hdist : dist (e (M.vertexPoint q)) (e (M.vertexPoint r)) < δ := by
    simp only [Subtype.dist_eq, e, coe_realizationHomeomorphRange_apply]
    exact (barycentricModel_mesh K d hd j ρ hρ q hq r hr).trans_lt hj
  have h := hsmall hdist
  simpa only [F, Function.comp_apply, Homeomorph.symm_apply_apply] using h

/-- The whole physical convex hull of each fine cell has small diameter.
This supplies the target mesh requirement in Appendix A, Step 2. -/
theorem exists_barycentric_hull_image_mesh_lt [Fintype V] [LinearOrder V]
    (K : AbstractSimplicialComplex V) (d : ℕ) (hd : ∀ σ ∈ K, σ.card ≤ d + 1)
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Realization → E) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ ρ ∈ (barycentricModel K j).complex,
      ∀ x ∈ convexHull ℝ
        ((fun q => f ((barycentricModel K j).vertexPoint q)) '' (ρ : Set _)),
      ∀ y ∈ convexHull ℝ
        ((fun q => f ((barycentricModel K j).vertexPoint q)) '' (ρ : Set _)),
        dist x y < ε := by
  obtain ⟨j, hj⟩ := exists_barycentric_vertex_image_mesh_lt K d hd f hf hε
  refine ⟨j, fun ρ hρ x hx y hy => ?_⟩
  obtain ⟨u, ⟨q, hq, rfl⟩, v, ⟨r, hr, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans_lt (hj ρ hρ q hq r hr)

end SharpTopologicalOverlap.Geometry
