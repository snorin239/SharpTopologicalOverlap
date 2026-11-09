module

public import SharpTopologicalOverlap.Geometry.Subdivision
public import SharpTopologicalOverlap.Intersection

/-! # From local intersection contributions to source cochains

Local intersection parity is evaluated on the indexed fundamental chain of
each original source face. Boundary compatibility transports a local parity
identity to the coboundary identity of Lemma 3.1(a). The hypotheses here remain
explicit until the geometric point and segment constructions establish them.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry

open SharpTopologicalOverlap.Simplicial

variable {V : Type*} {k : ℕ}

/-- Linear evaluation of contributions assigned to indexed affine simplices. -/
def affineEvaluation (I : AffineCell V k → Coeff) : AffineChain V k →ₗ[Coeff] Coeff :=
  Finsupp.linearCombination Coeff I

@[simp] theorem affineEvaluation_single (I : AffineCell V k → Coeff)
    (u : AffineCell V k) (r : Coeff) :
    affineEvaluation I (Finsupp.single u r) = r * I u := by
  simp [affineEvaluation, smul_eq_mul]

/-- Boundary-dual of a contribution, with unsigned facets over `𝔽₂`. -/
def affineCoboundary (I : AffineCell V k → Coeff) : AffineCell V (k + 1) → Coeff :=
  fun u => ∑ i : Fin (k + 2), I (u ∘ i.succAbove)

theorem affineEvaluation_coboundary (I : AffineCell V k → Coeff)
    (c : AffineChain V (k + 1)) :
    affineEvaluation (affineCoboundary I) c = affineEvaluation I (affineBoundary k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he => simp only [map_add, hc, he]
  | single u r => simp [affineCoboundary, Finset.mul_sum]

variable [LinearOrder V] {K : AbstractSimplicialComplex V}

/-- The source cochain obtained by evaluating local contributions on each
subdivided fundamental chain. -/
def intersectionCochain (j : ℕ) (I : AffineCell V k → Coeff) : Cochain K k :=
  fun s => affineEvaluation I (fundamentalChain j s)

/-- Pulling back the affine boundary-dual is exactly simplicial coboundary. -/
theorem coboundary_intersectionCochain (j : ℕ) (I : AffineCell V k → Coeff) :
    coboundary (intersectionCochain (K := K) j I) =
      intersectionCochain j (affineCoboundary I) := by
  funext s
  rw [coboundary_apply]
  change (∑ i : Fin (k + 2), affineEvaluation I (fundamentalChain j (s.face i))) =
    affineEvaluation (affineCoboundary I) (fundamentalChain j s)
  rw [affineEvaluation_coboundary, boundary_fundamentalChain, map_sum]

/-- The parity identity on one source child and all target facets passes
through the fundamental-chain sum. -/
theorem coboundary_intersectionCochain_of_local_identity
    {m : ℕ} (j : ℕ) (I : AffineCell V k → Coeff)
    (J : Fin m → AffineCell V (k + 1) → Coeff)
    (hlocal : ∀ (s : Cell K (k + 1)) u, u ∈ (fundamentalChain j s).support →
      affineCoboundary I u = ∑ i : Fin m, J i u) :
    coboundary (intersectionCochain (K := K) j I) =
      ∑ i : Fin m, intersectionCochain j (J i) := by
  rw [coboundary_intersectionCochain]
  funext s
  simp only [Finset.sum_apply]
  change affineEvaluation (affineCoboundary I) (fundamentalChain j s) =
    ∑ i : Fin m, affineEvaluation (J i) (fundamentalChain j s)
  simp only [affineEvaluation, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hlocal s u hu, Finset.mul_sum]

/-- A nonzero intersection cochain value has a nonzero local contribution
at an actually supported child of the original source face. -/
theorem exists_supported_child_of_intersectionCochain_ne_zero
    (j : ℕ) (I : AffineCell V k → Coeff) (s : Cell K k)
    (hs : intersectionCochain j I s ≠ 0) :
    ∃ u ∈ (fundamentalChain j s).support, I u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hs
  change (fundamentalChain j s).sum (fun u r => r • I u) = 0
  apply Finset.sum_eq_zero
  intro u hu
  change (fundamentalChain j s) u • I u = 0
  rw [h u hu, smul_zero]

/-- In degree zero, subdivision contributes the original coordinate vertex
once, so normalization reduces to the local target-cell count. -/
@[simp] theorem intersectionCochain_degree_zero (j : ℕ)
    (I : AffineCell V 0 → Coeff) (s : Cell K 0) :
    intersectionCochain j I s = I (sourceVertices s) := by
  simp [intersectionCochain]

/-- A local normalization over finitely many target cells gives normalization
of the degree-zero source cochains. -/
theorem sum_intersectionCochain_degree_zero {ι : Type*} [Fintype ι]
    (j : ℕ) (c : ι → Coeff) (I : ι → AffineCell V 0 → Coeff)
    (hnorm : ∀ s : Cell K 0, ∑ τ : ι, c τ * I τ (sourceVertices s) = 1) :
    ∑ τ : ι, c τ • intersectionCochain (K := K) j (I τ) = oneCochain K := by
  funext s
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    intersectionCochain_degree_zero, oneCochain_apply] using hnorm s

/-- The unique target simplex containing each source vertex image supplies
the preceding normalization hypothesis, after zero cone contributions. -/
theorem sum_intersectionCochain_degree_zero_of_unique {ι : Type*} [Fintype ι]
    (j : ℕ) (c : ι → Coeff) (I : ι → AffineCell V 0 → Coeff)
    (hunique : ∀ s : Cell K 0, ∃ τ : ι,
      c τ * I τ (sourceVertices s) = 1 ∧
        ∀ η : ι, η ≠ τ → c η * I η (sourceVertices s) = 0) :
    ∑ τ : ι, c τ • intersectionCochain (K := K) j (I τ) = oneCochain K := by
  classical
  apply sum_intersectionCochain_degree_zero
  intro s
  obtain ⟨τ, hτ, hother⟩ := hunique s
  rw [Finset.sum_eq_single τ (fun η _ hη => hother η hη)
    (fun hτ' => (hτ' (Finset.mem_univ τ)).elim)]
  exact hτ

section Family

variable {W : Type} [LinearOrder W] {T : AbstractSimplicialComplex W} {n d : ℕ}

/-- Local contributions with the same additive degree indexing as Lemma 3.1. -/
abbrev LocalIntersectionFamily (T : AbstractSimplicialComplex W) (n d : ℕ) :=
  ∀ p q : ℕ, p + q = d → Cell T p → AffineCell (Fin n) q → Coeff

/-- Sum each local target contribution on subdivided original source faces. -/
def intersectionCochainFamily (j : ℕ) (I : LocalIntersectionFamily T n d) :
    IntersectionCochainFamily T n d :=
  fun p q h τ => intersectionCochain j (I p q h τ)

/-- The precise field Lemma 3.1(a) follows from segment parity on supported
children. All geometric parity obligations are explicit in `hlocal`. -/
theorem facet_coboundary_intersectionCochainFamily
    (j : ℕ) (I : LocalIntersectionFamily T n d)
    (hlocal : ∀ p q (h : (p + 1) + q = d) (τ : Cell T (p + 1))
      (s : Cell (⊤ : AbstractSimplicialComplex (Fin n)) (q + 1)) u,
      u ∈ (fundamentalChain j s).support →
        affineCoboundary (I (p + 1) q h τ) u =
          ∑ i : Fin (p + 2), I p (q + 1) (by omega) (τ.face i) u) :
    ∀ p q (h : (p + 1) + q = d) (τ : Cell T (p + 1)),
      coboundary (intersectionCochainFamily j I (p + 1) q h τ) =
        ∑ i : Fin (p + 2),
          intersectionCochainFamily j I p (q + 1) (by omega) (τ.face i) := by
  intro p q h τ
  exact coboundary_intersectionCochain_of_local_identity j _ _ (hlocal p q h τ)

end Family

end SharpTopologicalOverlap.Geometry
