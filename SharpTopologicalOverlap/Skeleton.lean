module

public import SharpTopologicalOverlap.Simplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Skeleton

/-! # The realized skeleton of the full simplex

The coordinate model is identified with TauCeti's weak geometric realization.
The identification preserves the actual barycentric coordinates and therefore
every closed face, including its boundary.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap

variable {V : Type*}

attribute [local instance] Classical.decEq

/-- The coordinate realization of the `d`-skeleton of the full simplex. -/
abbrev Skeleton (V : Type*) (d : ℕ) :=
  {μ : Simplex V // (support μ).card ≤ d + 1}

/-- The full abstract simplex restricted to faces of dimension at most `d`. -/
abbrev skeletonComplex (V : Type*) (d : ℕ) : AbstractSimplicialComplex V :=
  (⊤ : AbstractSimplicialComplex V).skeleton d

@[simp] theorem mem_skeletonComplex {d : ℕ} {σ : Finset V} :
    σ ∈ skeletonComplex V d ↔ σ.Nonempty ∧ σ.card ≤ d + 1 := by
  rw [AbstractSimplicialComplex.mem_skeleton, TauCeti.AbstractSimplicialComplex.mem_top_iff]

/-- A closed source face, considered inside the realized skeleton. -/
def skeletonFace (d : ℕ) (σ : Finset V) : Set (Skeleton V d) :=
  Subtype.val ⁻¹' closedFace σ

@[simp] theorem mem_skeletonFace {d : ℕ} {σ : Finset V} {μ : Skeleton V d} :
    μ ∈ skeletonFace d σ ↔ support μ.1 ⊆ σ := Iff.rfl

/-- Every point of a face with at most `d + 1` vertices belongs to the skeleton. -/
def faceToSkeleton {d : ℕ} {σ : Finset V} (hσ : σ.card ≤ d + 1) :
    closedFace σ → Skeleton V d :=
  fun μ => ⟨μ.1, (Finset.card_le_card μ.2).trans hσ⟩

theorem continuous_faceToSkeleton {d : ℕ} {σ : Finset V} (hσ : σ.card ≤ d + 1) :
    Continuous (faceToSkeleton hσ) :=
  continuous_subtype_val.subtype_mk _

@[simp] theorem range_faceToSkeleton {d : ℕ} {σ : Finset V} (hσ : σ.card ≤ d + 1) :
    Set.range (faceToSkeleton hσ) = skeletonFace d σ := by
  ext μ
  constructor
  · rintro ⟨ν, rfl⟩
    exact ν.2
  · intro hμ
    exact ⟨⟨μ.1, hμ⟩, Subtype.ext rfl⟩

/-- The weights-preserving equivalence from the abstract to the coordinate skeleton. -/
def skeletonRealizationEquiv (d : ℕ) :
    (skeletonComplex V d).Realization ≃ Skeleton V d where
  toFun x :=
    ⟨⟨x.1, AbstractSimplicialComplex.Realization.nonneg _ x,
      AbstractSimplicialComplex.Realization.sum_eq_one _ x⟩,
      (AbstractSimplicialComplex.mem_skeleton.mp
        (AbstractSimplicialComplex.support_mem _ x)).2⟩
  invFun μ := ⟨μ.1.weights, by
    apply AbstractSimplicialComplex.mem_realization_iff.mpr
    refine ⟨support μ.1, ?_, ?_⟩
    · exact mem_skeletonComplex.mpr ⟨support_nonempty μ.1, μ.2⟩
    · rw [Finset.coe_image]
      exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
        ⟨μ.1.nonneg, μ.1.total, Finset.Subset.refl _⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Convexity.StdSimplex.ext rfl)

theorem continuous_skeletonRealizationEquiv [Finite V] (d : ℕ) :
    Continuous (skeletonRealizationEquiv (V := V) d) := by
  apply Continuous.subtype_mk
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous_iff.mpr
  exact AbstractSimplicialComplex.continuous_realization_coe _

/-- The coordinate skeleton and TauCeti's realization carry the same topology. -/
def skeletonRealizationHomeomorph [Finite V] (d : ℕ) :
    (skeletonComplex V d).Realization ≃ₜ Skeleton V d :=
  (skeletonRealizationEquiv d).toHomeomorphOfContinuousClosed
    (continuous_skeletonRealizationEquiv d)
    (continuous_skeletonRealizationEquiv d).isClosedMap

instance [Finite V] (d : ℕ) : CompactSpace (Skeleton V d) :=
  (skeletonRealizationHomeomorph (V := V) d).compactSpace

theorem isClosed_skeletonFace (d : ℕ) (σ : Finset V) :
    IsClosed (skeletonFace d σ) :=
  (isClosed_closedFace σ).preimage continuous_subtype_val

theorem isCompact_skeletonFace [Finite V] (d : ℕ) (σ : Finset V) :
    IsCompact (skeletonFace d σ) :=
  (isClosed_skeletonFace d σ).isCompact

@[simp] theorem weights_skeletonRealizationHomeomorph [Finite V] (d : ℕ)
    (x : (skeletonComplex V d).Realization) :
    (skeletonRealizationHomeomorph d x).1.weights = x.1 := rfl

@[simp] theorem mem_face_skeletonRealizationHomeomorph [Finite V] {d : ℕ}
    (x : (skeletonComplex V d).Realization) (σ : Finset V) :
    skeletonRealizationHomeomorph d x ∈ skeletonFace d σ ↔ x.1.support ⊆ σ := Iff.rfl

/-- The identification carries each abstract closed face to the same coordinate closed face. -/
theorem image_faceInclusion_skeletonRealizationHomeomorph [Finite V] {d : ℕ}
    (σ : TauCeti.SetLike.Face (skeletonComplex V d)) :
    skeletonRealizationHomeomorph d ''
      Set.range (AbstractSimplicialComplex.faceInclusion (skeletonComplex V d) σ) =
        skeletonFace d σ.1 := by
  classical
  ext μ
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    change (AbstractSimplicialComplex.faceInclusion (skeletonComplex V d) σ x).1.support ⊆ σ.1
    simpa only [AbstractSimplicialComplex.faceInclusion_val] using
      AbstractSimplicialComplex.StandardSimplex.support_subset x
  · intro hμ
    let x : AbstractSimplicialComplex.StandardSimplex σ.1 := ⟨μ.1.weights, by
      rw [Finset.coe_image]
      exact AbstractSimplicialComplex.mem_standardSimplex_iff.mpr
        ⟨μ.1.nonneg, μ.1.total, hμ⟩⟩
    refine ⟨AbstractSimplicialComplex.faceInclusion (skeletonComplex V d) σ x,
      ⟨x, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Convexity.StdSimplex.ext
    exact AbstractSimplicialComplex.faceInclusion_val _ _ _

end SharpTopologicalOverlap
