module

public import SharpTopologicalOverlap.Spectral.FaceRestriction.Coordinates

/-! # Families restricted and reindexed on a vertex subset -/

@[expose] public noncomputable section

open scoped BigOperators
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restrict a family and reindex its actual vertices on the subtype `S`. -/
def faceFamily (S : Finset V) (G : Finset (Finset V)) : Finset (Finset S) :=
  Finset.univ.filter fun e => e.map (Function.Embedding.subtype (· ∈ S)) ∈ G

@[simp] theorem mem_faceFamily (S : Finset V) (G : Finset (Finset V)) (e : Finset S) :
    e ∈ faceFamily S G ↔ e.map (Function.Embedding.subtype (· ∈ S)) ∈ G := by
  simp [faceFamily]

theorem faceFamily_uniform {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (S : Finset V) :
    Simplicial.IsUniform k (faceFamily S G) := by
  intro e he
  simpa only [Finset.card_map] using hG _ ((mem_faceFamily S G e).mp he)

theorem map_subtype_subset_face (S : Finset V) (e : Finset S) :
    e.map (Function.Embedding.subtype (· ∈ S)) ⊆ S := by
  intro i hi
  exact Finset.property_of_mem_map_subtype e hi

theorem subtype_map_eq_of_subset {S e : Finset V} (he : e ⊆ S) :
    (e.subtype (· ∈ S)).map (Function.Embedding.subtype (· ∈ S)) = e :=
  Finset.subtype_map_of_mem he

theorem faceFamily_subset_count (S : Finset V) (G : Finset (Finset V)) (s : Finset S) :
    ((faceFamily S G).filter (· ⊆ s)).card =
      (G.filter (· ⊆ s.map (Function.Embedding.subtype (· ∈ S)))).card := by
  apply Finset.card_bij (fun e _ => e.map (Function.Embedding.subtype (· ∈ S)))
  · intro e he
    obtain ⟨he, hes⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(mem_faceFamily S G e).mp he, Finset.map_subset_map.mpr hes⟩
  · intro e he f hf hef
    exact Finset.map_injective _ hef
  · intro e he
    obtain ⟨he, hes⟩ := Finset.mem_filter.mp he
    have heS : e ⊆ S := hes.trans (map_subtype_subset_face S s)
    refine ⟨e.subtype (· ∈ S), Finset.mem_filter.mpr ⟨?_, ?_⟩, subtype_map_eq_of_subset heS⟩
    · rw [mem_faceFamily, subtype_map_eq_of_subset heS]
      exact he
    · apply Finset.map_subset_map.mp
      rwa [subtype_map_eq_of_subset heS]

theorem faceFamily_parity {W : Type*} [Fintype W] [LinearOrder W]
    {k : ℕ} {G : Finset (Finset W)}
    (hG : Simplicial.HasCocycleParity k G) (S : Finset W) :
    Simplicial.HasCocycleParity k (faceFamily S G) := by
  intro s hs
  have hp := hG (s.map (Function.Embedding.subtype (· ∈ S)))
    (by simpa only [Finset.card_map] using hs)
  have hcount := faceFamily_subset_count S G s
  convert (Eq.mp (congrArg Even hcount.symm) hp) using 1
  congr 1
  ext t
  simp

theorem monomial_map_extend (S : Finset V) (e : Finset S) (x : S → ℝ) :
    monomial (e.map (Function.Embedding.subtype (· ∈ S))) (extendCoordinates S x) = monomial e x := by
  unfold monomial
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  exact extendCoordinates_apply_mem S x i

theorem weightPolynomial_faceFamily {k : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform k G) (S : Finset V) (x : S → ℝ) :
    weightPolynomial k (faceFamily S G) x = weightPolynomial k G (extendCoordinates S x) := by
  have hrestricted : Simplicial.IsUniform k (restrictFamily S G) := by
    intro e he
    exact hG e (Finset.mem_filter.mp he).1
  rw [weightPolynomial_of_uniform (faceFamily_uniform hG S)]
  have hs : (∑ e ∈ faceFamily S G, monomial e x) =
      ∑ e ∈ restrictFamily S G, monomial e (extendCoordinates S x) := by
    apply Finset.sum_bij (fun e _ => e.map (Function.Embedding.subtype (· ∈ S)))
    · intro e he
      exact Finset.mem_filter.mpr ⟨(mem_faceFamily S G e).mp he, map_subtype_subset_face S e⟩
    · intro e he f hf hef
      exact Finset.map_injective _ hef
    · intro e he
      obtain ⟨he, heS⟩ := Finset.mem_filter.mp he
      refine ⟨e.subtype (· ∈ S), ?_, subtype_map_eq_of_subset heS⟩
      rw [mem_faceFamily, subtype_map_eq_of_subset heS]
      exact he
    · intro e _
      exact (monomial_map_extend S e x).symm
  rw [hs, ← weightPolynomial_of_uniform hrestricted]
  exact restrict_eq k S G (fun i hi => extendCoordinates_apply_notMem S x hi)

theorem weightPolynomial_supportPoint {d : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform (d + 1) G) (μ : Simplex V) :
    weightPolynomial (d + 1) (faceFamily (support μ) G)
      ((supportPoint μ).weights : support μ → ℝ) =
        weightPolynomial (d + 1) G (μ.weights : V → ℝ) := by
  rw [weightPolynomial_faceFamily hG, extend_supportPoint]

end SharpTopologicalOverlap.Spectral
