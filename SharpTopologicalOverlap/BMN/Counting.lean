module

public import SharpTopologicalOverlap.BMN.Basic
public import SharpTopologicalOverlap.Spectral.Partite
public import Mathlib.Analysis.MeanInequalities

/-! # Finite counting for the BMN upper construction

The geometric input is only an exceptional vertex set and a coloring that
is injective on each containing source face avoiding that set.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V]

/-- The number of uniform source faces incident with one fixed vertex. -/
theorem card_incident_faces (d : ℕ) (v : V) :
    ((Finset.univ.powersetCard (d + 1)).filter (fun σ : Finset V => v ∈ σ)).card =
      (Fintype.card V - 1).choose d := by
  classical
  simpa using Finset.card_filter_powersetCard_subset ({v} : Finset V)
    Finset.univ (d + 1) (by simp) (by simp)

/-- A union bound for faces touching an exceptional set. -/
theorem card_bad_faces_le (d : ℕ) (G : Finset (Finset V))
    (hG : ∀ σ ∈ G, σ.card = d + 1) (D : Finset V) :
    (G.filter (fun σ => ¬ Disjoint σ D)).card ≤
      D.card * (Fintype.card V - 1).choose d := by
  classical
  have hsub : G.filter (fun σ => ¬ Disjoint σ D) ⊆
      D.biUnion (fun v => (Finset.univ.powersetCard (d + 1)).filter
        (fun σ : Finset V => v ∈ σ)) := by
    intro σ hσ
    obtain ⟨hσG, hσD⟩ := Finset.mem_filter.mp hσ
    obtain ⟨v, hvσ, hvD⟩ := Finset.not_disjoint_iff.mp hσD
    exact Finset.mem_biUnion.mpr ⟨v, hvD,
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by simp, hG σ hσG⟩, hvσ⟩⟩
  calc
    (G.filter (fun σ => ¬ Disjoint σ D)).card ≤
        (D.biUnion (fun v => (Finset.univ.powersetCard (d + 1)).filter
          (fun σ : Finset V => v ∈ σ))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ D, ((Finset.univ.powersetCard (d + 1)).filter
          (fun σ : Finset V => v ∈ σ)).card := Finset.card_biUnion_le
    _ = D.card * (Fintype.card V - 1).choose d := by simp [card_incident_faces]

/-- The usual AM--GM inequality with a natural exponent. -/
theorem prod_le_mean_pow {k : ℕ} (hk : 0 < k) (b : Fin k → ℝ)
    (hb : ∀ a, 0 ≤ b a) :
    ∏ a, b a ≤ ((∑ a, b a) / (k : ℝ)) ^ k := by
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin k => (1 : ℝ)) b
    (by simp) (by simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < k)) (by simpa)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun a _ => hb a)) _) h k
  simpa only [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun a _ => hb a))
    (Nat.ne_of_gt hk)] using hp

/-- Uniform faces on which a coloring is injective are bounded by the product
of its color-class sizes. -/
theorem card_colored_faces_le_prod {k : ℕ} (G : Finset (Finset V))
    (color : V → Fin k) (hG : ∀ σ ∈ G,
      σ.card = k ∧ Set.InjOn color (σ : Set V)) :
    G.card ≤ ∏ a, (Finset.univ.filter (fun v : V => color v = a)).card := by
  classical
  let T : Finset (Finset V) := (Finset.univ.powersetCard k).filter
    (fun σ : Finset V => Set.InjOn color (σ : Set V))
  have hT : ∀ σ : Finset V, σ ∈ T ↔
      σ.card = k ∧ Set.InjOn color (σ : Set V) := by
    intro σ
    simp [T]
  have hsub : G ⊆ T := fun σ hσ => (hT σ).mpr (hG σ hσ)
  have hcard : T.card = ∏ a, (Finset.univ.filter (fun v : V => color v = a)).card := by
    have he := Fintype.card_congr (Spectral.transversalChoiceEquiv hT)
    simpa [Spectral.TransversalChoice, Fintype.card_pi, Fintype.card_subtype] using he.symm
  exact (Finset.card_le_card hsub).trans_eq hcard

/-- A uniform injectively colored family has size at most the equal-class
product, expressed using the total number of vertices. -/
theorem card_colored_faces_le_mean_pow {k : ℕ} (hk : 0 < k)
    (G : Finset (Finset V)) (color : V → Fin k)
    (hG : ∀ σ ∈ G, σ.card = k ∧ Set.InjOn color (σ : Set V)) :
    (G.card : ℝ) ≤ ((Fintype.card V : ℝ) / (k : ℝ)) ^ k := by
  classical
  let b : Fin k → ℝ := fun a => ((Finset.univ.filter (fun v : V => color v = a)).card : ℝ)
  have hsum : ∑ a, b a = (Fintype.card V : ℝ) := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset V) (Finset.univ : Finset (Fin k)) color
    have hn : (∑ a, (Finset.univ.filter (fun v : V => color v = a)).card) =
        Fintype.card V := by simpa using h
    dsimp [b]
    exact_mod_cast hn
  calc
    (G.card : ℝ) ≤ ∏ a, b a := by
      dsimp [b]
      exact_mod_cast card_colored_faces_le_prod G color hG
    _ ≤ ((∑ a, b a) / (k : ℝ)) ^ k := prod_le_mean_pow hk b (by intro; positivity)
    _ = ((Fintype.card V : ℝ) / (k : ℝ)) ^ k := by rw [hsum]

/-- The abstract finite estimate used by the BMN construction. -/
theorem card_faces_le_of_color (d : ℕ) (G : Finset (Finset V))
    (hG : ∀ σ ∈ G, σ.card = d + 1) (D : Finset V)
    (color : V → Fin (d + 1)) (hD : D.card ≤ 2 * d)
    (hcolor : ∀ σ ∈ G, Disjoint σ D → Set.InjOn color (σ : Set V)) :
    (G.card : ℝ) ≤ ((Fintype.card V : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
      (2 * d : ℝ) * ((Fintype.card V - 1).choose d : ℝ) := by
  classical
  have hgood := card_colored_faces_le_mean_pow (Nat.zero_lt_succ d)
    (G.filter (fun σ => Disjoint σ D)) color (by
      intro σ hσ
      obtain ⟨hσG, hσD⟩ := Finset.mem_filter.mp hσ
      exact ⟨hG σ hσG, hcolor σ hσG hσD⟩)
  have hbad := card_bad_faces_le d G hG D
  have hbad' : ((G.filter (fun σ => ¬ Disjoint σ D)).card : ℝ) ≤
      (2 * d : ℝ) * ((Fintype.card V - 1).choose d : ℝ) := by
    exact_mod_cast hbad.trans (Nat.mul_le_mul_right _ hD)
  have hsplit := G.card_filter_add_card_filter_not (fun σ => Disjoint σ D)
  have hsplit' : (G.card : ℝ) =
      ((G.filter (fun σ => Disjoint σ D)).card : ℝ) +
      ((G.filter (fun σ => ¬ Disjoint σ D)).card : ℝ) := by exact_mod_cast hsplit.symm
  rw [hsplit']
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using add_le_add hgood hbad'

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- BMN's overlap estimate from the exceptional-set/type input. -/
theorem hullCount_le_of_color (d : ℕ) (p : V → E) (r : E)
    (D : Finset V) (color : V → Fin (d + 1)) (hD : D.card ≤ 2 * d)
    (hcolor : ∀ σ ∈ hullFacesAt d p r,
      Disjoint σ D → Set.InjOn color (σ : Set V)) :
    (hullCount d p r : ℝ) ≤ ((Fintype.card V : ℝ) / (d + 1 : ℝ)) ^ (d + 1) +
      (2 * d : ℝ) * ((Fintype.card V - 1).choose d : ℝ) := by
  exact card_faces_le_of_color d (hullFacesAt d p r)
    (fun σ hσ => (mem_hullFacesAt.mp hσ).1) D color hD hcolor

end SharpTopologicalOverlap.BMN
