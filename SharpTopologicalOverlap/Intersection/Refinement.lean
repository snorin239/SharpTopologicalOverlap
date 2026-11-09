module

public import SharpTopologicalOverlap.Simplicial
public import SharpTopologicalOverlap.Skeleton

/-! # Pulling intersection cochains through an actual simplicial refinement

The refinement may use any checked triangulation. Only its chain map, carriers,
and degree-zero values matter; no identification with a particular integral
affine-chain implementation is needed.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Simplicial

variable {V Q : Type*} {K : AbstractSimplicialComplex V}
  {L : AbstractSimplicialComplex Q} {k : ℕ}

/-- The cochain dual of a linear map on chains. -/
def pullbackCochain (R : Chain K k →ₗ[Coeff] Chain L k) (a : Cochain L k) : Cochain K k :=
  fun s => evaluation a (R (Finsupp.single s 1))

theorem evaluation_pullbackCochain (R : Chain K k →ₗ[Coeff] Chain L k)
    (a : Cochain L k) (c : Chain K k) :
    evaluation (pullbackCochain R a) c = evaluation a (R c) := by
  have he : evaluation (pullbackCochain R a) = (evaluation a).comp R := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [pullbackCochain]
  exact LinearMap.congr_fun he c

theorem coboundary_pullbackCochain [LinearOrder V] [LinearOrder Q]
    (R₀ : Chain K k →ₗ[Coeff] Chain L k)
    (R₁ : Chain K (k + 1) →ₗ[Coeff] Chain L (k + 1))
    (hR : ∀ c, boundary k (R₁ c) = R₀ (boundary k c)) (a : Cochain L k) :
    coboundary (pullbackCochain R₀ a) = pullbackCochain R₁ (coboundary a) := by
  funext s
  rw [coboundary, evaluation_pullbackCochain]
  unfold pullbackCochain
  rw [evaluation_coboundary, hR]

theorem exists_supported_cell_of_pullbackCochain_ne_zero
    (R : Chain K k →ₗ[Coeff] Chain L k) (a : Cochain L k) (s : Cell K k)
    (hs : pullbackCochain R a s ≠ 0) :
    ∃ u ∈ (R (Finsupp.single s 1)).support, a u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hs
  change (R (Finsupp.single s 1)).sum (fun u r => r • a u) = 0
  apply Finset.sum_eq_zero
  intro u hu
  simp [h u hu]

variable [LinearOrder V] {d : ℕ}

/-- Source cells in the full simplex and its skeleton have the same indices
in every degree used by the geometric intersection construction. -/
def skeletonCellEquiv (hk : k ≤ d) :
    Cell (⊤ : AbstractSimplicialComplex V) k ≃ Cell (skeletonComplex V d) k where
  toFun s := ⟨⟨s.1.1, mem_skeletonComplex.mpr
    ⟨Finset.card_pos.mp (by rw [s.2]; omega), by rw [s.2]; omega⟩⟩, s.2⟩
  invFun s := ⟨⟨s.1.1, by
    change s.1.1.Nonempty
    exact (mem_skeletonComplex.mp s.1.2).1⟩, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [LinearOrder V] in
@[simp] theorem skeletonCellEquiv_vertices (hk : k ≤ d)
    (s : Cell (⊤ : AbstractSimplicialComplex V) k) :
    (skeletonCellEquiv hk s).1.1 = s.1.1 := rfl

@[simp] theorem skeletonCellEquiv_face (hk : k + 1 ≤ d)
    (s : Cell (⊤ : AbstractSimplicialComplex V) (k + 1)) (i : Fin (k + 2)) :
    skeletonCellEquiv (by omega : k ≤ d) (s.face i) =
      (skeletonCellEquiv hk s).face i := by
  apply cell_vertices_injective
  have h₁ : ⇑s.vertexEmbedding = s.1.1.orderEmbOfFin s.2 :=
    Finset.orderEmbOfFin_unique s.2 s.vertexEmbedding_mem s.strictMono_vertexEmbedding
  have h₂ : ⇑(skeletonCellEquiv hk s).vertexEmbedding = s.1.1.orderEmbOfFin s.2 :=
    Finset.orderEmbOfFin_unique s.2 (skeletonCellEquiv hk s).vertexEmbedding_mem
      (skeletonCellEquiv hk s).strictMono_vertexEmbedding
  simp only [skeletonCellEquiv_vertices, AbstractSimplicialComplex.RealizationCell.face_val]
  rw [congrFun h₁ i, congrFun h₂ i]

/-- Regard a skeleton cochain in degree at most `d` as a full-simplex cochain. -/
def extendSkeletonCochain (hk : k ≤ d) (a : Cochain (skeletonComplex V d) k) :
    Cochain (⊤ : AbstractSimplicialComplex V) k := a ∘ skeletonCellEquiv hk

theorem coboundary_extendSkeletonCochain (hk : k + 1 ≤ d)
    (a : Cochain (skeletonComplex V d) k) :
    coboundary (extendSkeletonCochain (by omega : k ≤ d) a) =
      extendSkeletonCochain hk (coboundary a) := by
  funext s
  simp only [coboundary_apply, extendSkeletonCochain, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg a (skeletonCellEquiv_face hk s i)

end SharpTopologicalOverlap.Simplicial
