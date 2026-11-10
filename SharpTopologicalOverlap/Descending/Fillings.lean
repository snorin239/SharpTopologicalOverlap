module

public import SharpTopologicalOverlap.Descending.Algebra
public import SharpTopologicalOverlap.Singular.Relative

/-! # Constructing the descending filling chains

This is the descending induction in §6.3. Every provider is explicit:
nested carriers, relative fillers, a chain map and carrier annihilation.
The final assembly must construct those providers from the continuous map.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace SharpTopologicalOverlap.Descending

open SharpTopologicalOverlap.Simplicial

variable {n d : ℕ} {W : Type} [Fintype W] [LinearOrder W]
  {T : AbstractSimplicialComplex W}
  {f : C(Skeleton (Fin n) d, EuclideanSpace ℝ (Fin d))}

abbrev SourceSingular (n k : ℕ) := Singular.Chain (TopCat.of (Simplex (Fin n))) k

/-- Exact inputs from the comparison and nested weight-space branches. -/
structure FillingInputs (I : IntersectionData T f) (u : SourceSingular n 0) (x : Fin n) where
  B : ∀ p, Cell T p → Set (Simplex (Fin n))
  J : ∀ p, Cell T p → Set (Simplex (Fin n))
  B_mono : ∀ p r (σ : Cell T p) (τ : Cell T r), σ.1.1 ⊆ τ.1.1 → B r τ ⊆ B p σ
  J_mono : ∀ p r (σ : Cell T p) (τ : Cell T r), σ.1.1 ⊆ τ.1.1 → J r τ ⊆ J p σ
  fills : ∀ p q, p + q = d → ∀ τ : Cell T p,
    Singular.Fills (X := TopCat.of (Simplex (Fin n))) (B p τ) (J p τ) q
  top_carried : ∀ τ : Cell T d, Singular.CarriedBy (B d τ) u
  rho : ∀ k, SourceSingular n k →ₗ[Coeff] SourceChain n k
  rho_boundary : ∀ k (c : SourceSingular n (k + 1)),
    rho k (Singular.boundary k c) = boundary k (rho (k + 1) c)
  rho_top : rho 0 u = Finsupp.single
    (AbstractSimplicialComplex.RealizationCell.vertex
      (⊤ : AbstractSimplicialComplex (Fin n)) x) 1
  annihilates : ∀ p q (h : p + q = d) (τ : Cell T p) (b : SourceSingular n q),
    Singular.CarriedBy (J p τ) b → evaluation (I.cochain p q h τ) (rho q b) = 0

namespace FillingInputs

variable {I : IntersectionData T f} {u : SourceSingular n 0} {x : Fin n}
  (F : FillingInputs I u x)

theorem cofaceSum_carried {p k : ℕ} (c : Cell T (p + 1) → SourceSingular n k)
    (hc : ∀ τ, Singular.CarriedBy (F.B (p + 1) τ) (c τ)) (σ : Cell T p) :
    Singular.CarriedBy (F.B p σ) (cofaceSum c σ) := by
  classical
  rw [cofaceSum_eq]
  apply Submodule.sum_mem
  intro τ _
  split_ifs with h
  · exact Singular.carriedBy_mono (F.B_mono _ _ σ τ h) (hc τ)
  · exact Singular.carriedBy_zero _

theorem cofaceSum_carried_J {p k : ℕ} (c : Cell T (p + 1) → SourceSingular n k)
    (hc : ∀ τ, Singular.CarriedBy (F.J (p + 1) τ) (c τ)) (σ : Cell T p) :
    Singular.CarriedBy (F.J p σ) (cofaceSum c σ) := by
  classical
  rw [cofaceSum_eq]
  apply Submodule.sum_mem
  intro τ _
  split_ifs with h
  · exact Singular.carriedBy_mono (F.J_mono _ _ σ τ h) (hc τ)
  · exact Singular.carriedBy_zero _

/-- One source degree of the descent. Quantifying over the complementary
target degree avoids transporting whole stages across subtraction casts. -/
structure Layer (q : ℕ) where
  z : ∀ p, p + q = d → Cell T p → SourceSingular n q
  c : ∀ p, p + q = d → Cell T p → SourceSingular n (q + 1)
  b : ∀ p, p + q = d → Cell T p → SourceSingular n q
  z_carried : ∀ p h τ, Singular.CarriedBy (F.B p τ) (z p h τ)
  c_carried : ∀ p h τ, Singular.CarriedBy (F.B p τ) (c p h τ)
  b_carried : ∀ p h τ, Singular.CarriedBy (F.J p τ) (b p h τ)
  eq_filling : ∀ p h τ, z p h τ = Singular.boundary q (c p h τ) + b p h τ
  cycle : ∀ p (h : (p + 1) + q = d) (σ : Cell T p), cofaceSum (z (p + 1) h) σ = 0

theorem exists_layer (q : ℕ) (z : ∀ p, p + q = d → Cell T p → SourceSingular n q)
    (hz : ∀ p h τ, Singular.CarriedBy (F.B p τ) (z p h τ))
    (hrel : ∀ p h τ, Singular.IsRelativeCycle (F.J p τ) q (z p h τ))
    (hcycle : ∀ p (h : (p + 1) + q = d) σ, cofaceSum (z (p + 1) h) σ = 0) :
    ∃ s : F.Layer q, s.z = z := by
  classical
  have hf := fun p h τ => F.fills p q h τ (z p h τ) (hz p h τ) (hrel p h τ)
  choose c b hc hb heq using hf
  exact ⟨⟨z, c, b, hz, hc, hb, heq, hcycle⟩, rfl⟩

def initialZ (p : ℕ) (h : p + 0 = d) (τ : Cell T p) : SourceSingular n 0 :=
  I.zeta ((show p = d by omega) ▸ τ) • u

theorem exists_initialLayer : ∃ s : F.Layer 0, s.z = initialZ (I := I) (u := u) := by
  apply F.exists_layer
  · intro p h τ
    have hp : p = d := by omega
    subst p
    exact Singular.carriedBy_smul _ (F.top_carried τ)
  · intros
    trivial
  · intro p h σ
    have hd : d = p + 1 := by omega
    subst d
    exact cofaceSum_cycle I.zeta (I.cycle p rfl) u σ

def initialLayer : F.Layer 0 := F.exists_initialLayer.choose

theorem initialLayer_z : F.initialLayer.z = initialZ (I := I) (u := u) :=
  F.exists_initialLayer.choose_spec

set_option maxHeartbeats 1200000 in
theorem exists_nextLayer {q : ℕ} (s : F.Layer q) : ∃ s' : F.Layer (q + 1),
    s'.z = fun p h => cofaceSum (s.c (p + 1) (by omega)) := by
  apply F.exists_layer (q + 1) (fun p h => cofaceSum (s.c (p + 1) (by omega)))
  · intro p h
    exact F.cofaceSum_carried _ (s.c_carried (p + 1) (by omega))
  · intro p h σ
    change Singular.CarriedBy (X := TopCat.of (Simplex (Fin n))) (F.J p σ)
      (Singular.boundary (X := TopCat.of (Simplex (Fin n))) q
        (cofaceSum (s.c (p + 1) (by omega)) σ))
    rw [map_cofaceSum (Singular.boundary (X := TopCat.of (Simplex (Fin n))) q)]
    have hbd : ∀ τ, Singular.boundary q (s.c (p + 1) (by omega) τ) =
        s.z (p + 1) (by omega) τ + s.b (p + 1) (by omega) τ := by
      intro τ
      have heq := congrArg (fun a => a + s.b (p + 1) (by omega) τ)
        (s.eq_filling (p + 1) (by omega) τ)
      symm
      simpa only [add_assoc, Singular.add_self, add_zero] using heq
    simp_rw [hbd]
    rw [cofaceSum_add, s.cycle p (by omega) σ, zero_add]
    exact F.cofaceSum_carried_J _ (s.b_carried (p + 1) (by omega)) σ
  · intro p h σ
    exact cofaceSum_cofaceSum _ σ

def nextLayer {q : ℕ} (s : F.Layer q) : F.Layer (q + 1) := (F.exists_nextLayer s).choose

theorem nextLayer_z {q : ℕ} (s : F.Layer q) :
    (F.nextLayer s).z = fun p h => cofaceSum (s.c (p + 1) (by omega)) :=
  (F.exists_nextLayer s).choose_spec

/-- Ordinary natural induction implements descent in target dimension. -/
def layerAt (q : ℕ) : F.Layer q := Nat.rec F.initialLayer (fun _ s => F.nextLayer s) q

@[simp] theorem layerAt_zero : F.layerAt 0 = F.initialLayer := rfl

@[simp] theorem layerAt_succ (q : ℕ) : F.layerAt (q + 1) = F.nextLayer (F.layerAt q) := rfl

/-- Apply the supported comparison to the constructed singular fillings. -/
def toSimplicialDescent : SimplicialDescent I x where
  z p q h τ := F.rho q ((F.layerAt q).z p h τ)
  c p q h τ := F.rho (q + 1) ((F.layerAt q).c p h τ)
  top τ := by
    rw [layerAt_zero, initialLayer_z]
    change F.rho 0 (I.zeta τ • u) = _
    rw [map_smul, F.rho_top]
  descend p q h σ := by
    rw [layerAt_succ, nextLayer_z]
    exact map_cofaceSum (F.rho (q + 1)) ((F.layerAt q).c (p + 1) h) σ
  filling_eval p q h τ := by
    rw [(F.layerAt q).eq_filling p h τ, map_add, F.rho_boundary, map_add,
      F.annihilates p q h τ _ ((F.layerAt q).b_carried p h τ), add_zero,
      evaluation_coboundary]

include F in
/-- The complete descending argument from explicit nested filling data. -/
theorem false : False := F.toSimplicialDescent.false

end FillingInputs

end SharpTopologicalOverlap.Descending
