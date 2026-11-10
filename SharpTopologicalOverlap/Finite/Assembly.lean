module

public import SharpTopologicalOverlap.WeightSpaces.Fillings
public import SharpTopologicalOverlap.Comparison.Induction
public import SharpTopologicalOverlap.Intersection.Existence
public import SharpTopologicalOverlap.Descending
public import SharpTopologicalOverlap.Singular.Points

/-! # Assembly from the two remaining providers

The proof here uses the exact overlap, constant and source map of Theorem
1.2. Its remaining hypotheses are the canonical comparison provider and
actual sublevel relative vanishing; they are discharged only in `Finite`.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace SharpTopologicalOverlap

open _root_.SharpTopologicalOverlap.Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}

namespace IntersectionData

def fillingInputs_of_sublevel [NeZero n] (I : IntersectionData T f) (hd : 0 < d)
    (hn : deletionBound d < n) (x : Fin n) (ρ : Comparison.SupportedComparison (Fin n) x)
    (hsmall : (overlap f : ℝ) < (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1))
    (hH : ∀ p q, p + q = d → ∀ τ : Cell T p,
      IsZero ((Sublevel.sublevelPair d (I.remainingFamily τ)).singularHomology
        (ModuleCat.of Coeff Coeff) q)) :
    Descending.FillingInputs I
      (TauCeti.pointChain Coeff (uniform : Simplex (Fin n))) x where
  B p τ := I.weightSpace τ
  J p τ := I.independentSpace τ
  B_mono _ _ _ _ h := I.weightSpace_mono h
  J_mono _ _ _ _ h := I.independentSpace_mono h
  fills p q h τ := I.weightSpace_fills_of_sublevel τ hd q (hH p q h τ)
  top_carried τ := Singular.carriedBy_pointChain (I.uniform_mem_weightSpace τ hn hsmall)
  rho := ρ.rho
  rho_boundary k c := (ρ.boundary_rho k c).symm
  rho_top := by
    rw [ρ.uniform]
    apply congrArg (fun v => Finsupp.single v (1 : Coeff))
    apply cell_vertices_injective
    simp only [Comparison.vertexCell_vertices, AbstractSimplicialComplex.RealizationCell.vertex_val]
  annihilates p q h τ b hb :=
    I.evaluation_eq_zero_on_independence τ h hd
      (ρ.carried (I.independenceSubcomplex τ) q b hb)

end IntersectionData

/-- The exact finite bound, conditional only on the separately constructed
comparison and analytic sublevel providers. This is not the unconditional
Theorem 1.2. -/
theorem finite_overlap_bound_of_providers {n d : ℕ} (hd : 2 ≤ d)
    (hn : deletionBound d < n)
    (f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)))
    (cmp : Comparison.CanonicalHomologyComparison (Fin n))
    (hV : ∀ (V : Type) [Fintype V] [LinearOrder V] [Nonempty V]
      (G : Finset (Finset V)), IsUniform (d + 1) G → HasCocycleParity (d + 1) G →
      ∀ j, j ≤ d → IsZero ((Sublevel.sublevelPair d G).singularHomology
        (ModuleCat.of Coeff Coeff) j)) :
    (((n : ℝ) - deletionBound d) / (d + 1 : ℝ)) ^ (d + 1) ≤ (overlap f : ℝ) := by
  classical
  by_contra hbound
  have hsmall := lt_of_not_ge hbound
  have hnpos : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  let x : Fin n := ⟨0, hnpos⟩
  let ρ := Comparison.supportedComparison_of_canonicalHomology cmp x
  obtain ⟨w⟩ := exists_intersectionData hd
    (Nat.le_of_lt (add_one_lt_of_deletionBound_lt hd hn)) f
  let I := w.data
  have hH : ∀ p q, p + q = d → ∀ τ : Cell w.complex p,
      IsZero ((Sublevel.sublevelPair d (I.remainingFamily τ)).singularHomology
        (ModuleCat.of Coeff Coeff) q) := by
    intro p q h τ
    obtain ⟨i, hi⟩ := I.remainingVertices_nonempty τ hn
    let : Nonempty (I.remainingVertices τ) := ⟨⟨i, hi⟩⟩
    exact hV (I.remainingVertices τ) (I.remainingFamily τ)
      (I.remainingFamily_uniform τ) (I.remainingFamily_hasCocycleParity τ) q (by omega)
  exact (I.fillingInputs_of_sublevel (by omega) hn x ρ hsmall hH).false

end SharpTopologicalOverlap
