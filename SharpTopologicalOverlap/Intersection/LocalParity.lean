module

public import SharpTopologicalOverlap.Intersection.Indicators
public import SharpTopologicalOverlap.Geometry.SimplexParity

/-! # Geometric facet parity on the actual abstract source and target cells -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open SharpTopologicalOverlap.Simplicial
open AbstractSimplicialComplex Set Module

variable {Q W E : Type*} [LinearOrder Q] [LinearOrder W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : AbstractSimplicialComplex Q} {T : AbstractSimplicialComplex W}

omit [FiniteDimensional ℝ E] in
theorem placed_cell_affineIndependent {k : ℕ} (y : Q → E) (u : Cell L k)
    (h : AffineIndependent ℝ (fun q : u.1.1 => y q)) :
    AffineIndependent ℝ (y ∘ u.vertexEmbedding) := by
  let e : Fin (k + 1) ↪ u.1.1 :=
    ⟨fun i => ⟨u.vertexEmbedding i, u.vertexEmbedding_mem i⟩,
      fun i j hij => u.vertexEmbedding.injective (congrArg Subtype.val hij)⟩
  exact h.comp_embedding e

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem range_placed_vertices {k : ℕ} (y : Q → E) (u : Cell L k) :
    Set.range (y ∘ u.vertexEmbedding) = y '' (u.1.1 : Set Q) := by
  have h := congrArg (fun s : Finset Q => (s : Set Q)) u.image_vertexEmbedding
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at h
  rw [Set.range_comp, h]

/-- G3 and G4 on actual vertex subsets give the local cochain identity on the
actual simplicial cell indices, with no change of subdivision representation. -/
theorem localIndicator_coboundary
    {p q : ℕ} (u : Cell L (q + 1)) (τ : Cell T (p + 1))
    (y : Q → E) (z : W → E)
    (hy : AffineIndependent ℝ (y ∘ u.vertexEmbedding))
    (hz : AffineIndependent ℝ (z ∘ τ.vertexEmbedding))
    (hdim : (q + 1) + (p + 1) = finrank ℝ E + 1)
    (havoid : ∀ (A : Finset Q) (B : Finset W), A ⊆ u.1.1 → B ⊆ τ.1.1 →
      A.card + B.card ≤ finrank ℝ E + 1 →
        Disjoint (convexHull ℝ (y '' (A : Set Q))) (convexHull ℝ (z '' (B : Set W))))
    (hspan : ∀ (A : Finset Q) (B : Finset W), A ⊆ u.1.1 → B ⊆ τ.1.1 →
      finrank ℝ E + 2 ≤ A.card + B.card →
        (affineSpan ℝ (y '' (A : Set Q))).direction ⊔
          (affineSpan ℝ (z '' (B : Set W))).direction = ⊤) :
    coboundary (localIndicator y (convexHull ℝ (z '' (τ.1.1 : Set W)))) u =
      ∑ j : Fin (p + 2),
        localIndicator y (convexHull ℝ (z '' ((τ.face j).1.1 : Set W))) u := by
  classical
  let s : Affine.Simplex ℝ E (q + 1) := ⟨y ∘ u.vertexEmbedding, hy⟩
  let t : Affine.Simplex ℝ E (p + 1) := ⟨z ∘ τ.vertexEmbedding, hz⟩
  have hsource (A : Finset (Fin (q + 2))) :
      u.vertexEmbedding '' (A : Set (Fin (q + 2))) =
        (A.map u.vertexEmbedding : Set Q) := (Finset.coe_map _ _).symm
  have htarget (B : Finset (Fin (p + 2))) :
      τ.vertexEmbedding '' (B : Set (Fin (p + 2))) =
        (B.map τ.vertexEmbedding : Set W) := (Finset.coe_map _ _).symm
  have hA (A : Finset (Fin (q + 2))) : A.map u.vertexEmbedding ⊆ u.1.1 := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
    exact u.vertexEmbedding_mem i
  have hB (B : Finset (Fin (p + 2))) : B.map τ.vertexEmbedding ⊆ τ.1.1 := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
    exact τ.vertexEmbedding_mem i
  have havoid' : SimplexParity.LowerFaceAvoidance s t := by
    intro A B hcard
    have h := havoid (A.map u.vertexEmbedding) (B.map τ.vertexEmbedding) (hA A) (hB B)
      (by simpa only [Finset.card_map] using hcard)
    simpa only [SimplexParity.vertexHull, s, t, Set.image_comp, hsource, htarget] using h
  have hspan' : SimplexParity.FaceSpanning s t := by
    intro A B hcard
    have h := hspan (A.map u.vertexEmbedding) (B.map τ.vertexEmbedding) (hA A) (hB B)
      (by simpa only [Finset.card_map] using hcard)
    simpa only [s, t, Set.image_comp, hsource, htarget] using h
  have hparity := SimplexParity.facet_intersection_parity_succAbove s t hdim havoid' hspan'
  have huface (i : Fin (q + 2)) :
      Set.range (s.points ∘ i.succAbove) = y '' ((u.face i).1.1 : Set Q) := by
    rw [← range_placed_vertices y (u.face i), RealizationCell.vertexEmbedding_face]
    rfl
  have hτface (j : Fin (p + 2)) :
      Set.range (t.points ∘ j.succAbove) = z '' ((τ.face j).1.1 : Set W) := by
    rw [← range_placed_vertices z (τ.face j), RealizationCell.vertexEmbedding_face]
    rfl
  simp only [huface, hτface, s, t, range_placed_vertices] at hparity
  have hzero : coboundary (localIndicator y (convexHull ℝ (z '' (τ.1.1 : Set W)))) u +
      (∑ j : Fin (p + 2),
        localIndicator y (convexHull ℝ (z '' ((τ.face j).1.1 : Set W))) u) = 0 := by
    simpa only [coboundary_apply, localIndicator] using hparity
  have htwo : ∀ a : Coeff, a + a = 0 := by decide
  exact add_right_cancel (hzero.trans (htwo _).symm)

end SharpTopologicalOverlap.Geometry
