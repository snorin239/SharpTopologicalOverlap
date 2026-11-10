module

public import SharpTopologicalOverlap.Simplex

/-! # A closed face as the probability simplex on its actual vertices -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

variable {V : Type*} [Fintype V] [DecidableEq V]

def faceInclusion (S : Finset V) : C(Simplex S, Simplex V) :=
  ⟨fun μ => μ.map Subtype.val, Convexity.StdSimplex.continuous_map ℝ _⟩

@[simp] theorem faceInclusion_coordinate (S : Finset V) (μ : Simplex S) (i : S) :
    (faceInclusion S μ).weights i.1 = μ.weights i := by
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective μ.weights i

theorem faceInclusion_coordinate_zero (S : Finset V) (μ : Simplex S) {i : V} (hi : i ∉ S) :
    (faceInclusion S μ).weights i = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, rfl⟩
  exact hi j.property

theorem faceInclusion_mem_closedFace (S : Finset V) (μ : Simplex S) :
    faceInclusion S μ ∈ closedFace S := by
  intro i hi
  by_contra hiS
  exact (mem_support.mp hi) (faceInclusion_coordinate_zero S μ hiS)

theorem sum_coordinates_on_face (S : Finset V) (μ : closedFace S) :
    (∑ i : S, μ.1.weights i.1) = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    (∑ i ∈ S, μ.1.weights i) = ∑ i, μ.1.weights i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      by_contra hne
      exact hi (μ.2 (mem_support.mpr hne))
    _ = 1 := sum_coordinates μ.1

def faceRestriction (S : Finset V) (μ : closedFace S) : Simplex S :=
  coordinateHomeomorph.symm ⟨fun i : S => μ.1.weights i.1,
    fun i => coordinate_nonneg μ.1 i.1, sum_coordinates_on_face S μ⟩

@[simp] theorem faceRestriction_coordinate (S : Finset V) (μ : closedFace S) (i : S) :
    (faceRestriction S μ).weights i = μ.1.weights i.1 := by
  change (coordinateHomeomorph (faceRestriction S μ)).1 i = _
  simp only [faceRestriction, Homeomorph.apply_symm_apply]

def faceHomeomorph (S : Finset V) : Simplex S ≃ₜ closedFace S where
  toFun μ := ⟨faceInclusion S μ, faceInclusion_mem_closedFace S μ⟩
  invFun := faceRestriction S
  left_inv μ := by
    apply (coordinateHomeomorph (V := S)).injective
    apply Subtype.ext
    funext i
    exact (faceRestriction_coordinate S _ i).trans (faceInclusion_coordinate S μ i)
  right_inv μ := by
    apply Subtype.ext
    apply (coordinateHomeomorph (V := V)).injective
    apply Subtype.ext
    funext i
    change (faceInclusion S (faceRestriction S μ)).weights i = μ.1.weights i
    by_cases hi : i ∈ S
    · exact (faceInclusion_coordinate S _ ⟨i, hi⟩).trans (faceRestriction_coordinate S μ ⟨i, hi⟩)
    · rw [faceInclusion_coordinate_zero S _ hi]
      symm
      by_contra hne
      exact hi (μ.2 (mem_support.mpr hne))
  continuous_toFun := (faceInclusion S).continuous.subtype_mk _
  continuous_invFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ S).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun μ : closedFace S => (faceRestriction S μ).weights i)
    simp_rw [faceRestriction_coordinate]
    exact (continuous_coordinate i.1).comp continuous_subtype_val

end SharpTopologicalOverlap
