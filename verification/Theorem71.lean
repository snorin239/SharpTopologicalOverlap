import SharpTopologicalOverlap

/-! Root-import-only statement and axiom audits for Theorem 7.1. -/

noncomputable section

open SharpTopologicalOverlap

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Theorem71Verification

/-- The manuscript's geometric statement, with a uniform explicit error. -/
theorem manuscript_bound {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin d),
      Function.Injective p ∧ ConvexIndependent ℝ p ∧
      (∀ σ : Finset (Fin n), σ.card = d + 1 →
        AffineIndependent ℝ (fun i : σ => p i)) ∧
      ∀ r, (((Finset.univ.powersetCard (d + 1)).filter
          (fun σ : Finset (Fin n) => r ∈ convexHull ℝ (p '' (σ : Set (Fin n))))).card : ℝ) ≤
        ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) + (2 * d : ℝ) * (n : ℝ) ^ d := by
  obtain ⟨p, hc, hi, hb⟩ := BMN.exists_configuration_polynomial_error hd n
  refine ⟨p, hc.injective, hc, hi, ?_⟩
  simpa only [BMN.hullCount, BMN.hullFacesAt] using hb

/-- The uniform geometric bound applies to a continuous source map. -/
theorem continuous_bound {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
      (overlap f : ℝ) ≤ ((n : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
        (2 * d : ℝ) * ((n - 1).choose d : ℝ) :=
  BMN.exists_continuous_overlap_bound hd n

/-- The normalization is by binomial coefficients, with its factorial. -/
theorem normalized_upper_bound {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d)),
        (overlap f : ℝ) / (n.choose (d + 1) : ℝ) <
          ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) + ε :=
  BMN.eventually_exists_normalized_overlap_lt hd hε

example : overlapThreshold 2 = (2 : ℝ) / 9 := by norm_num [overlapThreshold]
example : overlapThreshold 3 = (3 : ℝ) / 32 := by norm_num [overlapThreshold]

/-- The geometric theorem includes empty point sets. -/
example {d : ℕ} (hd : 2 ≤ d) :
    ∃ p : Fin 0 → EuclideanSpace ℝ (Fin d), ConvexIndependent ℝ p := by
  obtain ⟨p, hc, _, _⟩ := BMN.exists_configuration hd 0
  exact ⟨p, hc⟩

#print axioms BMN.det_sign_of_dominantPermutation
#print axioms BMN.type_of_mem_convexHull
#print axioms BMN.hullCount_le_of_separated
#print axioms BMN.exists_configuration
#print axioms BMN.exists_configuration_polynomial_error
#print axioms BMN.exists_affine_overlap_bound
#print axioms BMN.exists_continuous_overlap_bound
#print axioms BMN.convexHull_injective_of_convexIndependent
#print axioms BMN.tendsto_normalized_bmn_bound
#print axioms BMN.eventually_exists_normalized_overlap_lt
#print axioms manuscript_bound
#print axioms continuous_bound
#print axioms normalized_upper_bound

end Theorem71Verification
