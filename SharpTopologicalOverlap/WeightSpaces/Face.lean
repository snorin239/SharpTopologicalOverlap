module

public import SharpTopologicalOverlap.WeightSpaces
public import SharpTopologicalOverlap.Simplex.Face
public import SharpTopologicalOverlap.Sublevel.Definitions
public import SharpTopologicalOverlap.Spectral.FaceRestriction.Family

/-! # Reindexing the remaining-face sublevel pair -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

open Simplicial WeightPolynomial
open CategoryTheory CategoryTheory.Limits

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}

namespace IntersectionData

variable (I : IntersectionData T f)

theorem mem_remainingFamily_image_iff {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (s : Finset (I.remainingVertices τ)) :
    s ∈ I.remainingFamily τ ↔ s.image Subtype.val ∈ I.restrictedFamily τ := by
  classical
  rw [← I.remainingFamily_image τ hd]
  constructor
  · exact Finset.mem_image_of_mem _
  · intro hs
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs
    have hts' : t = s := Finset.image_injective Subtype.val_injective hts
    exact hts' ▸ ht

theorem remainingFamily_eq_faceFamily {p : ℕ} (τ : Cell T p) (hd : 0 < d) :
    I.remainingFamily τ = Spectral.faceFamily (I.remainingVertices τ) (upwardSupport I.cochain τ) := by
  classical
  ext s
  rw [I.mem_remainingFamily_image_iff τ hd, I.mem_restrictedFamily, Spectral.mem_faceFamily]
  have hsub : s.image Subtype.val ⊆ I.remainingVertices τ := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  simp only [and_iff_left hsub, Finset.map_eq_image]
  rfl

theorem remaining_polynomial_faceInclusion {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (ν : Simplex (I.remainingVertices τ)) :
    weightPolynomial (d + 1) (I.remainingFamily τ) (ν.weights : I.remainingVertices τ → ℝ) =
      weightPolynomial (d + 1) (upwardSupport I.cochain τ)
        ((faceInclusion (I.remainingVertices τ) ν).weights : Fin n → ℝ) := by
  rw [I.remainingFamily_eq_faceFamily τ hd,
    Spectral.weightPolynomial_faceFamily (upwardSupport_uniform I.cochain τ)]
  congr 1
  funext i
  by_cases hi : i ∈ I.remainingVertices τ
  · exact (Spectral.extendCoordinates_apply_mem _ _ ⟨i, hi⟩).trans
      (faceInclusion_coordinate _ ν ⟨i, hi⟩).symm
  · rw [Spectral.extendCoordinates_apply_notMem _ _ hi,
      faceInclusion_coordinate_zero _ ν hi]

theorem mem_independentSpace_iff_ambient {p : ℕ} (τ : Cell T p) (μ : Simplex (Fin n)) :
    μ ∈ I.independentSpace τ ↔ support μ ⊆ I.remainingVertices τ ∧
      weightPolynomial (d + 1) (upwardSupport I.cochain τ) (μ.weights : Fin n → ℝ) = 0 := by
  rw [I.mem_independentSpace_iff]
  constructor
  · rintro ⟨hrem, hz⟩
    exact ⟨hrem, (I.polynomial_restrict_remaining τ μ hrem).symm.trans hz⟩
  · rintro ⟨hrem, hz⟩
    exact ⟨hrem, (I.polynomial_restrict_remaining τ μ hrem).trans hz⟩

theorem mem_weightSpace_faceInclusion_iff {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (ν : Simplex (I.remainingVertices τ)) :
    faceInclusion (I.remainingVertices τ) ν ∈ I.weightSpace τ ↔
      ν ∈ Sublevel.strictSublevel d (I.remainingFamily τ) := by
  have hrem := faceInclusion_mem_closedFace (I.remainingVertices τ) ν
  change _ < _ ↔ _ < _
  rw [I.exceptionalMass_eq_zero_of_remaining τ _ hrem,
    ← I.remaining_polynomial_faceInclusion τ hd ν]
  simp

theorem mem_independentSpace_faceInclusion_iff {p : ℕ} (τ : Cell T p) (hd : 0 < d)
    (ν : Simplex (I.remainingVertices τ)) :
    faceInclusion (I.remainingVertices τ) ν ∈ I.independentSpace τ ↔
      ν ∈ Sublevel.zeroSet d (I.remainingFamily τ) := by
  rw [I.mem_independentSpace_iff_ambient, and_iff_right
    (show support (faceInclusion (I.remainingVertices τ) ν) ⊆ I.remainingVertices τ from
      faceInclusion_mem_closedFace (I.remainingVertices τ) ν),
    ← I.remaining_polynomial_faceInclusion τ hd ν]
  rfl

def remainingWeightSpace {p : ℕ} (τ : Cell T p) : Set (Simplex (Fin n)) :=
  I.weightSpace τ ∩ closedFace (I.remainingVertices τ)

theorem independentSpace_subset_remainingWeightSpace {p : ℕ} (τ : Cell T p) :
    I.independentSpace τ ⊆ I.remainingWeightSpace τ := by
  intro μ hμ
  exact ⟨I.independentSpace_subset_weightSpace τ hμ, ((I.mem_independentSpace_iff τ μ).mp hμ).1⟩

def remainingSublevelHomeomorph {p : ℕ} (τ : Cell T p) (hd : 0 < d) :
    Sublevel.strictSublevel d (I.remainingFamily τ) ≃ₜ I.remainingWeightSpace τ where
  toFun ν := ⟨faceInclusion (I.remainingVertices τ) ν.1,
    (I.mem_weightSpace_faceInclusion_iff τ hd ν.1).mpr ν.2,
    faceInclusion_mem_closedFace _ ν.1⟩
  invFun μ := ⟨faceRestriction (I.remainingVertices τ) ⟨μ.1, μ.2.2⟩, by
    apply (I.mem_weightSpace_faceInclusion_iff τ hd _).mp
    have h := congrArg Subtype.val ((faceHomeomorph (I.remainingVertices τ)).apply_symm_apply
      ⟨μ.1, μ.2.2⟩)
    change faceInclusion (I.remainingVertices τ) (faceRestriction _ ⟨μ.1, μ.2.2⟩) = μ.1 at h
    rw [h]
    exact μ.2.1⟩
  left_inv ν := Subtype.ext ((faceHomeomorph (I.remainingVertices τ)).symm_apply_apply ν.1)
  right_inv μ := by
    apply Subtype.ext
    change faceInclusion (I.remainingVertices τ) (faceRestriction _ ⟨μ.1, μ.2.2⟩) = μ.1
    exact congrArg (fun v : closedFace (I.remainingVertices τ) => v.1)
      ((faceHomeomorph (I.remainingVertices τ)).apply_symm_apply ⟨μ.1, μ.2.2⟩)
  continuous_toFun := by
    exact ((faceInclusion (I.remainingVertices τ)).continuous.comp
      (continuous_subtype_val : Continuous (fun ν : Sublevel.strictSublevel d (I.remainingFamily τ) => ν.1))).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun μ : I.remainingWeightSpace τ =>
        (⟨μ.1, μ.2.2⟩ : closedFace (I.remainingVertices τ))) := continuous_subtype_val.subtype_mk _
    exact ((faceHomeomorph (I.remainingVertices τ)).symm.continuous.comp hc).subtype_mk _

def remainingZeroHomeomorph {p : ℕ} (τ : Cell T p) (hd : 0 < d) :
    Sublevel.zeroSet d (I.remainingFamily τ) ≃ₜ I.independentSpace τ where
  toFun ν := ⟨faceInclusion (I.remainingVertices τ) ν.1,
    (I.mem_independentSpace_faceInclusion_iff τ hd ν.1).mpr ν.2⟩
  invFun μ := ⟨faceRestriction (I.remainingVertices τ)
      ⟨μ.1, ((I.mem_independentSpace_iff τ μ.1).mp μ.2).1⟩, by
    apply (I.mem_independentSpace_faceInclusion_iff τ hd _).mp
    have h := congrArg Subtype.val ((faceHomeomorph (I.remainingVertices τ)).apply_symm_apply
      ⟨μ.1, ((I.mem_independentSpace_iff τ μ.1).mp μ.2).1⟩)
    change faceInclusion (I.remainingVertices τ) (faceRestriction _ _) = μ.1 at h
    rw [h]
    exact μ.2⟩
  left_inv ν := Subtype.ext ((faceHomeomorph (I.remainingVertices τ)).symm_apply_apply ν.1)
  right_inv μ := by
    apply Subtype.ext
    change faceInclusion (I.remainingVertices τ) (faceRestriction _ _) = μ.1
    exact congrArg (fun v : closedFace (I.remainingVertices τ) => v.1)
      ((faceHomeomorph (I.remainingVertices τ)).apply_symm_apply
        ⟨μ.1, ((I.mem_independentSpace_iff τ μ.1).mp μ.2).1⟩)
  continuous_toFun := by
    exact ((faceInclusion (I.remainingVertices τ)).continuous.comp
      (continuous_subtype_val : Continuous (fun ν : Sublevel.zeroSet d (I.remainingFamily τ) => ν.1))).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun μ : I.independentSpace τ =>
        (⟨μ.1, ((I.mem_independentSpace_iff τ μ.1).mp μ.2).1⟩ : closedFace (I.remainingVertices τ))) :=
      continuous_subtype_val.subtype_mk _
    exact ((faceHomeomorph (I.remainingVertices τ)).symm.continuous.comp hc).subtype_mk _

set_option backward.isDefEq.respectTransparency false in
/-- The actual sublevel pair on `Y_τ` is the remaining-face pair in the
ambient simplex, including both of its subspace inclusions. -/
def remainingSublevelPairIso {p : ℕ} (τ : Cell T p) (hd : 0 < d) :
    Sublevel.sublevelPair d (I.remainingFamily τ) ≅
      TopPair.ofInclusion (X := TopCat.of (Simplex (Fin n)))
        (I.independentSpace_subset_remainingWeightSpace τ) where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨I.remainingSublevelHomeomorph τ hd, (I.remainingSublevelHomeomorph τ hd).continuous⟩)
    (TopCat.ofHom ⟨I.remainingZeroHomeomorph τ hd, (I.remainingZeroHomeomorph τ hd).continuous⟩) (by ext; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(I.remainingSublevelHomeomorph τ hd).symm, (I.remainingSublevelHomeomorph τ hd).symm.continuous⟩)
    (TopCat.ofHom ⟨(I.remainingZeroHomeomorph τ hd).symm, (I.remainingZeroHomeomorph τ hd).symm.continuous⟩) (by ext; rfl)
  hom_inv_id := by
    ext μ : 2
    · exact (I.remainingZeroHomeomorph τ hd).symm_apply_apply μ
    · exact (I.remainingSublevelHomeomorph τ hd).symm_apply_apply μ
  inv_hom_id := by
    ext μ : 2
    · exact (I.remainingZeroHomeomorph τ hd).apply_symm_apply μ
    · exact (I.remainingSublevelHomeomorph τ hd).apply_symm_apply μ

theorem isZero_remainingFace_of_sublevel {p : ℕ} (τ : Cell T p) (hd : 0 < d) (j : ℕ)
    (hH : IsZero ((Sublevel.sublevelPair d (I.remainingFamily τ)).singularHomology
      (ModuleCat.of Coeff Coeff) j)) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of (Simplex (Fin n)))
      (I.independentSpace_subset_remainingWeightSpace τ)).singularHomology
        (ModuleCat.of Coeff Coeff) j) := by
  let e := (TopPair.singularHomologyFunctor (ModuleCat.of Coeff Coeff) j).mapIso
    (I.remainingSublevelPairIso τ hd)
  have h0 : IsZero ((TopPair.singularHomologyFunctor (ModuleCat.of Coeff Coeff) j).obj
      (Sublevel.sublevelPair d (I.remainingFamily τ))) := by
    simpa only [TopPair.singularHomologyFunctor_obj] using hH
  have ht := h0.of_iso e.symm
  simpa only [TopPair.singularHomologyFunctor_obj] using ht

end IntersectionData

end SharpTopologicalOverlap
