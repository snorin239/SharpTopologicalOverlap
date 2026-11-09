module

public import SharpTopologicalOverlap.Geometry.TargetGeometry
public import SharpTopologicalOverlap.Geometry.TargetCycle

/-! # Outer target carriers lie in a proper face of the enclosing simplex -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.TargetGeometry

open AbstractSimplicialComplex Set
open scoped BigOperators

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineMap_mem_target_face (D : Affine.Simplex ℝ E d)
    (μ : Fin (d + 2) →₀ ℝ) (hn : ∀ v, 0 ≤ μ v)
    (hsum : μ.sum (fun _ r => r) = 1) (hlast : μ (Fin.last (d + 1)) = 0)
    (i : Fin (d + 1)) (hi : μ i.castSucc = 0) :
    affineMap D μ ∈ convexHull ℝ (D.points '' (↑(Finset.univ.erase i) : Set (Fin (d + 1)))) := by
  classical
  obtain ⟨c⟩ := SimplexParity.exists_coordinates D.independent
  have hweights := sum_castSucc_eq_one hsum hlast
  have hfull : affineMap D μ ∈ convexHull ℝ (range D.points) := by
    rw [affineMap_eq_sum]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hn j.castSucc) hweights
      (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))
  apply (c.mem_erased_face_hull_iff hfull i).mpr
  have hmap : affineMap D μ = Finset.univ.affineCombination ℝ D.points
      (fun j : Fin (d + 1) => μ j.castSucc) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hweights, affineMap_eq_sum]
  rw [hmap, c.read _ hweights i]
  exact hi

/-- All inside vertices of one outer target cell lie in the same proper face
of `D`, so their convex hull remains in the boundary rather than crossing its
interior. -/
theorem targetCells_subset_target_face_of_not_inPatch (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (σ : TauCeti.SetLike.Face M.complex)
    (hσ : ¬InPatch M σ.1) :
    ∃ i : Fin (d + 1), targetCells D M σ.1 ⊆
      convexHull ℝ (D.points '' (↑(Finset.univ.erase i) : Set (Fin (d + 1)))) := by
  classical
  obtain ⟨θ, hθ⟩ := M.exists_originalFace_carrier σ
  have hnot : ¬θ.1 ⊆ patch d := by
    intro hsub
    exact hσ (fun q hq => (hθ q hq).trans hsub)
  have hInf : Fin.last (d + 1) ∈ θ.1 := by
    by_contra hlast
    apply hnot
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    exact hlast (h ▸ hv)
  have hproper := (AbstractSimplicialComplex.mem_standardSuccSimplexBoundary_iff.mp θ.2).2
  have hne : θ.1 ≠ Finset.univ := (Finset.ssubset_iff_subset_ne.mp hproper).2
  have hmissing : ∃ v : Fin (d + 2), v ∉ θ.1 := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_iff_forall.mpr h)
  have hmissing' : ∃ i : Fin (d + 1), i.castSucc ∉ θ.1 := by
    obtain ⟨v, hv⟩ := hmissing
    have hrec : ∀ v : Fin (d + 2), v ∉ θ.1 → ∃ i : Fin (d + 1), i.castSucc ∉ θ.1 := by
      intro v
      refine Fin.lastCases ?_ (fun i => ?_) v
      · intro h
        exact (h hInf).elim
      · intro h
        exact ⟨i, h⟩
    exact hrec v hv
  obtain ⟨i, hi⟩ := hmissing'
  refine ⟨i, ?_⟩
  apply convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨q, hq, rfl⟩
  have hqσ := (mem_patchVertices.mp hq).1
  have hqP := (mem_patchVertices.mp hq).2
  apply affineMap_mem_target_face D (M.vertexPoint q).1
    (Realization.nonneg _ _) (Realization.sum_eq_one _ _)
    (last_eq_zero_of_support_subset_patch hqP) i
  apply Finsupp.notMem_support_iff.mp
  intro h
  exact hi (hθ q hqσ h)

theorem target_face_disjoint_interior (D : Affine.Simplex ℝ E d) (i : Fin (d + 1)) :
    Disjoint (convexHull ℝ (D.points '' (↑(Finset.univ.erase i) : Set (Fin (d + 1)))))
      (interior (convexHull ℝ (range D.points))) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxface hxint
  have heq := D.independent.eq_univ_of_mem_intrinsicInterior_convexHull
    (interior_subset_intrinsicInterior (𝕜 := ℝ) hxint) hxface
  have hi : i ∈ (↑(Finset.univ.erase i) : Set (Fin (d + 1))) := by
    rw [heq]
    exact Set.mem_univ i
  simp at hi

/-- The carrier of every outer target cell misses the interior of the
enclosing simplex, as required for its cochain to vanish. -/
theorem targetCells_disjoint_interior_of_not_inPatch (D : Affine.Simplex ℝ E d)
    (M : BarycentricModel (sphere d)) (σ : TauCeti.SetLike.Face M.complex)
    (hσ : ¬InPatch M σ.1) :
    Disjoint (targetCells D M σ.1) (interior (convexHull ℝ (range D.points))) := by
  obtain ⟨i, hi⟩ := targetCells_subset_target_face_of_not_inPatch D M σ hσ
  exact (target_face_disjoint_interior D i).mono_left hi

theorem refinedInfinity_point (d j : ℕ) :
    (TargetCycle.model d j).vertexPoint (TargetCycle.refinedInfinity d j) =
      AbstractSimplicialComplex.vertex (sphere d) (Fin.last (d + 1)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (TargetCycle.model d j).step.vertexPoint
      ((TargetCycle.model d j).singletonVertex (TargetCycle.refinedInfinity d j)) = _
    rw [BarycentricModel.singletonVertex_point, ih]

/-- The zero anchor is an actual outside vertex at every target depth. -/
theorem targetCells_refinedInfinity_eq_empty (D : Affine.Simplex ℝ E d) (j : ℕ) :
    targetCells D (TargetCycle.model d j) {TargetCycle.refinedInfinity d j} = ∅ := by
  classical
  have hnot : ¬((TargetCycle.model d j).vertexPoint (TargetCycle.refinedInfinity d j)).1.support ⊆
      patch d := by
    intro h
    have hz := last_eq_zero_of_support_subset_patch h
    rw [refinedInfinity_point, AbstractSimplicialComplex.vertex_val,
      Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  have heq : patchVertices (TargetCycle.model d j) {TargetCycle.refinedInfinity d j} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hq' := mem_patchVertices.mp hq
    have hqeq : q = TargetCycle.refinedInfinity d j := Finset.mem_singleton.mp hq'.1
    subst q
    exact hnot hq'.2
  rw [targetCells, heq]
  simp

end SharpTopologicalOverlap.Geometry.TargetGeometry
