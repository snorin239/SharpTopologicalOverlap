module

public import SharpTopologicalOverlap.Simplex
public import SharpTopologicalOverlap.Simplicial
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Indexed affine subdivision of source faces

Children are indexed by their ordered tuples of points of the source probability
simplex.  In particular different source simplices are not identified merely
because their images under a later map agree.  The integral affine subdivision
and its boundary identity are reused from TauCeti; the paper-facing fundamental
chains below reduce their coefficients modulo two.
-/

@[expose] public noncomputable section

open Convexity Finsupp

namespace SharpTopologicalOverlap.Geometry

variable {V : Type*} {k : ℕ}

/-- An ordered affine simplex in the source probability simplex. -/
abbrev AffineCell (V : Type*) (k : ℕ) := Fin (k + 1) → Simplex V

/-- Integral affine chains, before reducing orientation signs modulo two. -/
abbrev IntegralAffineChain (V : Type*) (k : ℕ) := AffineCell V k →₀ ℤ

/-- Affine chains with the coefficients of the manuscript. -/
abbrev AffineChain (V : Type*) (k : ℕ) := AffineCell V k →₀ Simplicial.Coeff

/-- Iterated barycentric subdivision on indexed affine chains. -/
def subdivide (j k : ℕ) (c : IntegralAffineChain V k) : IntegralAffineChain V k :=
  (TauCeti.AffineChain.subdivision (Simplex V) k)^[j] c

theorem subdivide_eq_pow (j k : ℕ) (c : IntegralAffineChain V k) :
    subdivide j k c = (TauCeti.AffineChain.subdivision (Simplex V) k ^ j) c := by
  rw [pow_apply_eq_iterate]
  rfl

@[simp] theorem subdivide_zero (c : IntegralAffineChain V k) : subdivide 0 k c = c := rfl

theorem subdivide_succ (j : ℕ) (c : IntegralAffineChain V k) :
    subdivide (j + 1) k c =
      TauCeti.AffineChain.subdivision (Simplex V) k (subdivide j k c) :=
  Function.iterate_succ_apply' _ _ _

/-- Subdivision commutes with boundary in every successor degree. -/
theorem boundary_subdivide (j k : ℕ) (c : IntegralAffineChain V (k + 1)) :
    TauCeti.AffineChain.boundary (Simplex V) k (subdivide j (k + 1) c) =
      subdivide j k (TauCeti.AffineChain.boundary (Simplex V) k c) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [subdivide_succ, subdivide_succ]
    exact (LinearMap.congr_fun (TauCeti.AffineChain.boundary_subdivision k)
      (subdivide j (k + 1) c)).trans (congrArg _ ih)

/-- No subdivision changes a degree-zero chain. -/
@[simp] theorem subdivide_degree_zero (j : ℕ) (c : IntegralAffineChain V 0) :
    subdivide j 0 c = c := by
  simp [subdivide, TauCeti.AffineChain.subdivision_zero]

/-- The affine interpolation of vertices in a closed source face stays in it. -/
theorem affineMapMk_mem_closedFace (σ : Finset V) (v : AffineCell V k)
    (hv : ∀ i, v i ∈ closedFace σ) (w : Simplex (Fin (k + 1))) :
    StdSimplex.affineMapMk (R := ℝ) v w ∈ closedFace σ := by
  classical
  intro x hx
  by_contra hxs
  have hz (i : Fin (k + 1)) : (v i).weights x = 0 := by
    by_contra hn
    exact hxs (hv i (Finsupp.mem_support_iff.mpr hn))
  have hzero : (StdSimplex.affineMapMk (R := ℝ) v w).weights x = 0 := by
    simp [StdSimplex.weights_affineMapMk_apply, hz]
  exact (Finsupp.mem_support_iff.mp hx) hzero

/-- All vertices of every nonzero child remain in the same original closed face. -/
theorem subdivision_carried (σ : Finset V) (c : IntegralAffineChain V k)
    (hc : ∀ v ∈ c.support, ∀ i, v i ∈ closedFace σ)
    {u : AffineCell V k}
    (hu : u ∈ (TauCeti.AffineChain.subdivision (Simplex V) k c).support) :
    ∀ i, u i ∈ closedFace σ := by
  classical
  rw [← c.sum_single, map_finsuppSum] at hu
  obtain ⟨v, hv, hu⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hu)
  rw [TauCeti.AffineChain.subdivision_single] at hu
  obtain ⟨π, -, hπ⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hu)
  obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hπ)
  intro i
  exact affineMapMk_mem_closedFace σ v (hc v hv) _

theorem subdivide_carried (j : ℕ) (σ : Finset V) (c : IntegralAffineChain V k)
    (hc : ∀ v ∈ c.support, ∀ i, v i ∈ closedFace σ)
    {u : AffineCell V k} (hu : u ∈ (subdivide j k c).support) :
    ∀ i, u i ∈ closedFace σ := by
  induction j generalizing u with
  | zero => exact hc u hu
  | succ j ih =>
    rw [subdivide_succ] at hu
    exact subdivision_carried σ _ (fun v hv => ih hv) hu

section Mesh

variable [Fintype V]

/-- The mesh factor depends on simplex dimension rather than ambient dimension. -/
theorem subdivide_vertex_dist_le (j : ℕ) (c : IntegralAffineChain V k)
    {u : AffineCell V k} (hu : u ∈ (subdivide j k c).support)
    (i l : Fin (k + 1)) :
    dist (⇑(u i).weights) (⇑(u l).weights) ≤ ((k : ℝ) / (k + 1)) ^ j := by
  exact TauCeti.AffineChain.dist_weights_le_of_mem_support_subdivision_iterate hu i l

/-- The same mesh bound controls every two points of a child, not just its vertices. -/
theorem subdivide_dist_le (j : ℕ) (c : IntegralAffineChain V k)
    {u : AffineCell V k} (hu : u ∈ (subdivide j k c).support)
    (a b : Simplex (Fin (k + 1))) :
    dist (⇑(StdSimplex.affineMapMk (R := ℝ) u a).weights)
      (⇑(StdSimplex.affineMapMk (R := ℝ) u b).weights) ≤ ((k : ℝ) / (k + 1)) ^ j := by
  apply StdSimplex.dist_weights_affineMapMk_le
  intro i
  rw [dist_comm]
  exact StdSimplex.dist_weights_affineMapMk_le u
    (fun l => subdivide_vertex_dist_le j c hu l i) b

/-- Every chain has a subdivision all of whose indexed children have small diameter. -/
theorem exists_subdivide_dist_lt (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ (c : IntegralAffineChain V k) (u : AffineCell V k),
      u ∈ (subdivide j k c).support →
      ∀ a b : Simplex (Fin (k + 1)),
        dist (⇑(StdSimplex.affineMapMk (R := ℝ) u a).weights)
          (⇑(StdSimplex.affineMapMk (R := ℝ) u b).weights) < ε := by
  have hlt : (k : ℝ) / (k + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε hlt
  exact ⟨j, fun c u hu a b => (subdivide_dist_le j c hu a b).trans_lt hj⟩

end Mesh

/-- Forget orientation signs by reducing integral coefficients modulo two. -/
def reduceModTwo (k : ℕ) : IntegralAffineChain V k →+ AffineChain V k :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom Simplicial.Coeff)

@[simp] theorem reduceModTwo_apply (c : IntegralAffineChain V k) (u : AffineCell V k) :
    reduceModTwo k c u = (c u : Simplicial.Coeff) := rfl

@[simp] theorem reduceModTwo_single (u : AffineCell V k) (r : ℤ) :
    reduceModTwo k (Finsupp.single u r) = Finsupp.single u (r : Simplicial.Coeff) := by
  simp [reduceModTwo]

theorem reduceModTwo_surjective (k : ℕ) :
    Function.Surjective (reduceModTwo (V := V) k) :=
  Finsupp.mapRange_surjective _ (Int.cast_zero) ZMod.intCast_surjective

theorem support_reduceModTwo_subset (c : IntegralAffineChain V k) :
    (reduceModTwo k c).support ⊆ c.support := by
  intro u hu
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact (Finsupp.mem_support_iff.mp hu) (by simp [hz])

/-- Unsigned simplicial boundary of indexed affine simplices over `𝔽₂`. -/
def affineBoundary (k : ℕ) : AffineChain V (k + 1) →ₗ[Simplicial.Coeff] AffineChain V k :=
  Finsupp.linearCombination Simplicial.Coeff
    (fun v => ∑ i : Fin (k + 2), Finsupp.single (v ∘ i.succAbove) 1)

@[simp] theorem affineBoundary_single (v : AffineCell V (k + 1)) (r : Simplicial.Coeff) :
    affineBoundary k (Finsupp.single v r) =
      ∑ i : Fin (k + 2), Finsupp.single (v ∘ i.succAbove) r := by
  simp [affineBoundary, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]

/-- Reduction modulo two changes the alternating integral boundary into the unsigned boundary. -/
theorem affineBoundary_reduceModTwo (c : IntegralAffineChain V (k + 1)) :
    affineBoundary k (reduceModTwo (k + 1) c) =
      reduceModTwo k (TauCeti.AffineChain.boundary (Simplex V) k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he => simp only [map_add, hc, he]
  | single v r =>
    simp [show (-1 : Simplicial.Coeff) = 1 by decide]

/-- The square of the unsigned affine boundary is zero. -/
theorem affineBoundary_affineBoundary_reduced (c : IntegralAffineChain V (k + 2)) :
    affineBoundary k (affineBoundary (k + 1) (reduceModTwo (k + 2) c)) = 0 := by
  rw [affineBoundary_reduceModTwo, affineBoundary_reduceModTwo]
  have h := LinearMap.congr_fun (TauCeti.AffineChain.boundary_boundary (E := Simplex V) k) c
  simpa using congrArg (reduceModTwo k) h

theorem affineBoundary_affineBoundary (c : AffineChain V (k + 2)) :
    affineBoundary k (affineBoundary (k + 1) c) = 0 := by
  obtain ⟨c, rfl⟩ := reduceModTwo_surjective (k + 2) c
  exact affineBoundary_affineBoundary_reduced c

section FundamentalChain

variable [LinearOrder V] {K : AbstractSimplicialComplex V}

/-- The ordered coordinate vertices of a source face. -/
def sourceVertices (s : Simplicial.Cell K k) : AffineCell V k :=
  vertex ∘ s.vertexEmbedding

@[simp] theorem sourceVertices_face (s : Simplicial.Cell K (k + 1)) (i : Fin (k + 2)) :
    sourceVertices (s.face i) = sourceVertices s ∘ i.succAbove := by
  simp [sourceVertices, Function.comp_assoc]

/-- The subdivided fundamental chain of a source face, with coefficients modulo two. -/
def fundamentalChain (j : ℕ) (s : Simplicial.Cell K k) : AffineChain V k :=
  reduceModTwo k (subdivide j k (Finsupp.single (sourceVertices s) 1))

@[simp] theorem fundamentalChain_zero (s : Simplicial.Cell K k) :
    fundamentalChain 0 s = Finsupp.single (sourceVertices s) 1 := by
  simp [fundamentalChain]

/-- Lemma A.1 for the indexed affine fundamental chains, in every subdivision. -/
theorem boundary_fundamentalChain (j : ℕ) (s : Simplicial.Cell K (k + 1)) :
    affineBoundary k (fundamentalChain j s) =
      ∑ i : Fin (k + 2), fundamentalChain j (s.face i) := by
  rw [fundamentalChain, affineBoundary_reduceModTwo, boundary_subdivide]
  simp only [TauCeti.AffineChain.boundary_single, one_mul, subdivide_eq_pow, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [fundamentalChain, subdivide_eq_pow, sourceVertices_face]
  rw [show Finsupp.single (sourceVertices s ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ)) =
    ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (sourceVertices s ∘ i.succAbove) 1 by simp]
  rw [map_smul]
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul Simplicial.Coeff]
  simp [show (-1 : Simplicial.Coeff) = 1 by decide]

/-- Original source vertices are preserved exactly. -/
@[simp] theorem fundamentalChain_degree_zero (j : ℕ) (s : Simplicial.Cell K 0) :
    fundamentalChain j s = Finsupp.single (sourceVertices s) 1 := by
  simp [fundamentalChain]

/-- Every nonzero child of an original face is carried by that very closed face. -/
theorem fundamentalChain_carried (j : ℕ) (s : Simplicial.Cell K k)
    {u : AffineCell V k} (hu : u ∈ (fundamentalChain j s).support) :
    ∀ a : Simplex (Fin (k + 1)),
      StdSimplex.affineMapMk (R := ℝ) u a ∈ closedFace s.1.1 := by
  have hu' : u ∈ (subdivide j k (Finsupp.single (sourceVertices s) 1)).support := by
    exact support_reduceModTwo_subset _ hu
  apply affineMapMk_mem_closedFace
  exact subdivide_carried j s.1.1 _ (by
    intro v hv
    have heq : v = sourceVertices s := by simpa using hv
    subst v
    intro i
    simp only [sourceVertices, Function.comp_apply, closedFace, Set.mem_ofPred_eq, support_vertex]
    exact Finset.singleton_subset_iff.mpr (s.vertexEmbedding_mem i)) hu'

/-- Every two points of a nonzero fundamental-chain child satisfy the mesh bound. -/
theorem fundamentalChain_dist_le [Fintype V] (j : ℕ) (s : Simplicial.Cell K k)
    {u : AffineCell V k} (hu : u ∈ (fundamentalChain j s).support)
    (a b : Simplex (Fin (k + 1))) :
    dist (⇑(StdSimplex.affineMapMk (R := ℝ) u a).weights)
      (⇑(StdSimplex.affineMapMk (R := ℝ) u b).weights) ≤ ((k : ℝ) / (k + 1)) ^ j :=
  subdivide_dist_le j _ (support_reduceModTwo_subset _ hu) a b

/-- One subdivision depth works for all original source faces of dimension at most `d`. -/
theorem exists_fundamentalChain_dist_lt [Fintype V] (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, ∀ (k : ℕ) (_ : k ≤ d) (s : Simplicial.Cell K k) (u : AffineCell V k),
      u ∈ (fundamentalChain j s).support →
      ∀ a b : Simplex (Fin (k + 1)),
        dist (⇑(StdSimplex.affineMapMk (R := ℝ) u a).weights)
          (⇑(StdSimplex.affineMapMk (R := ℝ) u b).weights) < ε := by
  have hlt : (d : ℝ) / (d + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨j, fun k hkd s u hu a b => (fundamentalChain_dist_le j s hu a b).trans_lt ?_⟩
  apply lt_of_le_of_lt _ hj
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
  nlinarith

end FundamentalChain

end SharpTopologicalOverlap.Geometry
