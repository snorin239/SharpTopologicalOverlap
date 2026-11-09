module

public import SharpTopologicalOverlap.Spectral.Equality
public import SharpTopologicalOverlap.Spectral.Index
public import SharpTopologicalOverlap.Polynomial.Threshold

/-! # Complete partite families and the equality value

A transversal chooses one vertex from each color fibre. The equivalence below
keeps the source faces as indices and gives the exact product-of-masses formula.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix
open SharpTopologicalOverlap.WeightPolynomial

namespace SharpTopologicalOverlap.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- A choice of one vertex in each color class. -/
abbrev TransversalChoice (color : V → Fin k) := ∀ a : Fin k, {i : V // color i = a}

def choiceFace {color : V → Fin k} (f : TransversalChoice color) : Finset V :=
  Finset.univ.image fun a => (f a).1

theorem choice_injective {color : V → Fin k} (f : TransversalChoice color) :
    Function.Injective (fun a => (f a).1) := by
  intro a b hab
  have h := congrArg color hab
  simpa only [(f a).2, (f b).2] using h

theorem choiceFace_card {color : V → Fin k} (f : TransversalChoice color) :
    (choiceFace f).card = k := by
  rw [choiceFace, Finset.card_image_of_injective _ (choice_injective f),
    Finset.card_univ, Fintype.card_fin]

theorem choiceFace_injOn_color {color : V → Fin k} (f : TransversalChoice color) :
    Set.InjOn color (choiceFace f : Set V) := by
  intro i hi j hj hij
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hj
  have hab : a = b := by simpa only [(f a).2, (f b).2] using hij
  rw [hab]

theorem colorImage_eq_univ {color : V → Fin k} {e : Finset V}
    (hcard : e.card = k) (hinj : Set.InjOn color (e : Set V)) :
    e.image color = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_fin]

def choiceToEdge {color : V → Fin k} {G : Finset (Finset V)}
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V))
    (f : TransversalChoice color) : {e : Finset V // e ∈ G} :=
  ⟨choiceFace f, (hG _).mpr ⟨choiceFace_card f, choiceFace_injOn_color f⟩⟩

theorem choiceToEdge_bijective {color : V → Fin k} {G : Finset (Finset V)}
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V)) :
    Function.Bijective (choiceToEdge hG) := by
  constructor
  · intro f g hfg
    have hface : choiceFace f = choiceFace g := congrArg Subtype.val hfg
    funext a
    apply Subtype.ext
    have ha : (f a).1 ∈ choiceFace g := by
      rw [← hface]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    obtain ⟨b, _, hba⟩ := Finset.mem_image.mp ha
    have hab : b = a := by
      have h := congrArg color hba
      simpa only [(g b).2, (f a).2] using h
    subst b
    exact hba.symm
  · intro e
    obtain ⟨hcard, hinj⟩ := (hG _).mp e.2
    have himage := colorImage_eq_univ hcard hinj
    have hex : ∀ a : Fin k, ∃ i : V, i ∈ e.1 ∧ color i = a := by
      intro a
      have ha : a ∈ e.1.image color := by rw [himage]; exact Finset.mem_univ _
      exact Finset.mem_image.mp ha
    choose f hfmem hfcolor using hex
    let c : TransversalChoice color := fun a => ⟨f a, hfcolor a⟩
    refine ⟨c, Subtype.ext ?_⟩
    change choiceFace c = e.1
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      exact hfmem a
    · intro i hi
      apply Finset.mem_image.mpr
      refine ⟨color i, Finset.mem_univ _, ?_⟩
      exact hinj (hfmem _) hi (hfcolor _)

def transversalChoiceEquiv {color : V → Fin k} {G : Finset (Finset V)}
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V)) :
    TransversalChoice color ≃ {e : Finset V // e ∈ G} :=
  Equiv.ofBijective (choiceToEdge hG) (choiceToEdge_bijective hG)

theorem monomial_choiceFace {color : V → Fin k} (f : TransversalChoice color) (x : V → ℝ) :
    monomial (choiceFace f) x = ∏ a, x (f a).1 := by
  rw [monomial, choiceFace, Finset.prod_image]
  exact fun _ _ _ _ h => choice_injective f h

def classMass (color : V → Fin k) (x : V → ℝ) (a : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (color · = a), x i

theorem classMass_eq_sum_subtype (color : V → Fin k) (x : V → ℝ) (a : Fin k) :
    classMass color x a = ∑ i : {i : V // color i = a}, x i.1 := by
  exact Finset.sum_subtype _ (by simp) _

theorem sum_monomial_eq_prod_classMass {color : V → Fin k} {G : Finset (Finset V)}
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V)) (x : V → ℝ) :
    (∑ e ∈ G, monomial e x) = ∏ a, classMass color x a := by
  classical
  calc
    (∑ e ∈ G, monomial e x) = ∑ e : {e : Finset V // e ∈ G}, monomial e.1 x :=
      (Finset.sum_coe_sort G (fun e => monomial e x)).symm
    _ = ∑ f : TransversalChoice color, monomial (choiceFace f) x :=
      (Equiv.sum_comp (transversalChoiceEquiv hG) (fun e => monomial e.1 x)).symm
    _ = ∑ f : TransversalChoice color, ∏ a, x (f a).1 := by
      apply Finset.sum_congr rfl
      intro f _
      exact monomial_choiceFace f x
    _ = ∏ a, ∑ i : {i : V // color i = a}, x i.1 :=
      (Fintype.prod_sum (fun (a : Fin k) (i : {i : V // color i = a}) => x i.1)).symm
    _ = ∏ a, classMass color x a := by simp_rw [classMass_eq_sum_subtype]

theorem weightPolynomial_eq_prod_classMass {color : V → Fin k} {G : Finset (Finset V)}
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V)) (x : V → ℝ) :
    weightPolynomial k G x = (k.factorial : ℝ) * ∏ a, classMass color x a := by
  have hunif : Simplicial.IsUniform k G := fun e he => ((hG e).mp he).1
  rw [weightPolynomial_of_uniform hunif, sum_monomial_eq_prod_classMass hG]

theorem transversal_color_count {color : V → Fin k} {e : Finset V}
    (hcard : e.card = k) (hinj : Set.InjOn color (e : Set V)) (a : Fin k) :
    (e.filter (color · = a)).card = 1 := by
  have himage := colorImage_eq_univ hcard hinj
  have ha : a ∈ e.image color := by rw [himage]; exact Finset.mem_univ _
  obtain ⟨i, hie, hia⟩ := Finset.mem_image.mp ha
  have hf : e.filter (color · = a) = {i} := by
    ext j
    constructor
    · intro hj
      obtain ⟨hje, hja⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_singleton.mpr (hinj hje hie (hja.trans hia.symm))
    · intro hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact Finset.mem_filter.mpr ⟨hie, hia⟩
  rw [hf, Finset.card_singleton]

theorem classMass_stationary {color : V → Fin k} {G : Finset (Finset V)}
    (hk : 0 < k)
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V))
    (μ : Simplex V) (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) (a : Fin k) :
    classMass color (μ.weights : V → ℝ) a = (k : ℝ)⁻¹ := by
  have hs : (∑ i ∈ Finset.univ.filter (color · = a),
      ∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) = 1 := by
    have hfilter : ∀ i : V,
        (∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) =
          ∑ e ∈ homogeneousPart k G, if i ∈ e then edgeWeight k G μ e else 0 := by
      intro i
      rw [Finset.sum_filter]
    simp_rw [hfilter]
    rw [Finset.sum_comm]
    have hinner : ∀ e ∈ homogeneousPart k G,
        (∑ i ∈ Finset.univ.filter (color · = a), if i ∈ e then edgeWeight k G μ e else 0) =
          edgeWeight k G μ e := by
      intro e he
      have hset : (Finset.univ.filter (color · = a)).filter (· ∈ e) = e.filter (color · = a) := by
        ext i
        simp [and_comm]
      rw [← Finset.sum_filter, hset, Finset.sum_const,
        transversal_color_count ((hG e).mp (mem_homogeneousPart.mp he).1).1
          ((hG e).mp (mem_homogeneousPart.mp he).1).2 a, one_nsmul]
    rw [Finset.sum_congr rfl hinner]
    exact sum_edgeWeight k G μ hp
  have hmem : ∀ i : V,
      (∑ e ∈ (homogeneousPart k G).filter (i ∈ ·), edgeWeight k G μ e) =
        (k : ℝ) * μ.weights i := by
    intro i
    rw [edgeWeight_mem_sum, stationary_partial μ hc i]
    field_simp
  simp_rw [hmem] at hs
  rw [← Finset.mul_sum] at hs
  have hkn : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  apply (mul_left_cancel₀ hkn)
  rw [mul_inv_cancel₀ hkn]
  exact hs

theorem weightPolynomial_stationary_partite {color : V → Fin k} {G : Finset (Finset V)}
    (hk : 0 < k)
    (hG : ∀ e : Finset V, e ∈ G ↔ e.card = k ∧ Set.InjOn color (e : Set V))
    (μ : Simplex V) (hp : weightPolynomial k G (μ.weights : V → ℝ) ≠ 0)
    (hc : IsSimplexCritical k G (μ.weights : V → ℝ)) :
    weightPolynomial k G (μ.weights : V → ℝ) = (k.factorial : ℝ) / (k : ℝ) ^ k := by
  rw [weightPolynomial_eq_prod_classMass hG]
  simp_rw [classMass_stationary hk hG μ hp hc]
  simp [div_eq_mul_inv, inv_pow]

section Cocycle

variable [LinearOrder V]

theorem exists_partite_of_tangentIndex_eq (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G) (hne : G.Nonempty)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ))
    (hindex : sigNeg (tangentHessianForm d G μ) = d) :
    ∃ color : V → Fin (d + 1), Function.Surjective color ∧
      (∀ e : Finset V, e ∈ G ↔ e.card = d + 1 ∧ Set.InjOn color (e : Set V)) ∧
      (∀ a, classMass color (μ.weights : V → ℝ) a = (d + 1 : ℝ)⁻¹) ∧
      weightPolynomial (d + 1) G (μ.weights : V → ℝ) =
        ((d + 1).factorial : ℝ) / (d + 1 : ℝ) ^ (d + 1) := by
  have hspec := projected_eigenvalues_eq_of_tangentIndex_eq d G μ hμ hp hc hindex
  have hpoly := square_eq_neg_smul_of_two_value_spectrum (projectedHessian_isHermitian d G μ)
    ((d + 1 : ℝ) * weightPolynomial (d + 1) G (μ.weights : V → ℝ)) hspec
  have hid := equalityProjection_mul_self d G μ (ne_of_gt hp) hpoly
  obtain ⟨color, hsurj, _, hcolor⟩ := exists_partite_coloring hG hne hpar
    (equalityLabel d G μ)
    (fun _ he => equalityLabel_injOn_edge d G hG μ hμ (ne_of_gt hp) hid he)
    (fun _ he => equalityLabel_sum_edge d G hG μ hμ hp hc hid he)
  refine ⟨color, hsurj, hcolor, ?_, ?_⟩
  · intro a
    simpa only [Nat.cast_add, Nat.cast_one] using
      classMass_stationary (by omega) hcolor μ (ne_of_gt hp) hc a
  · simpa only [Nat.cast_add, Nat.cast_one] using
      weightPolynomial_stationary_partite (by omega) hcolor μ (ne_of_gt hp) hc

theorem weightPolynomial_pos_of_nonempty {d : ℕ} {G : Finset (Finset V)}
    (hG : Simplicial.IsUniform (d + 1) G) (hne : G.Nonempty)
    (μ : Simplex V) (hμ : ∀ i, 0 < μ.weights i) :
    0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ) := by
  rw [weightPolynomial_of_uniform hG]
  apply mul_pos (Nat.cast_pos.mpr (d + 1).factorial_pos)
  apply Finset.sum_pos'
  · exact fun _ _ => monomial_nonneg (coordinate_nonneg μ)
  · obtain ⟨e, he⟩ := hne
    exact ⟨e, he, (monomial_pos_iff (coordinate_nonneg μ)).mpr fun i _ => hμ i⟩

/-- Lemma 4.1, including the actual partite partition and the exact equality value. -/
theorem spectral_index_rigidity (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G) (hne : G.Nonempty)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    d ≤ sigNeg (tangentHessianForm d G μ) ∧
      (sigNeg (tangentHessianForm d G μ) = d →
        ∃ color : V → Fin (d + 1), Function.Surjective color ∧
          (∀ e : Finset V, e ∈ G ↔ e.card = d + 1 ∧ Set.InjOn color (e : Set V)) ∧
          (∀ a, classMass color (μ.weights : V → ℝ) a = (d + 1 : ℝ)⁻¹) ∧
          weightPolynomial (d + 1) G (μ.weights : V → ℝ) = overlapThreshold d) := by
  have hp := weightPolynomial_pos_of_nonempty hG hne μ hμ
  exact ⟨tangentNegativeIndex_ge d G μ hμ hp hc,
    exists_partite_of_tangentIndex_eq d G hG hne hpar μ hμ hp hc⟩

/-- The strict index bound at a critical point having full support. The
support-restricted version is obtained by transporting this to the active face. -/
theorem fullSupportCritical_index_ge (d : ℕ) (G : Finset (Finset V))
    (hG : Simplicial.IsUniform (d + 1) G)
    (hpar : Simplicial.HasCocycleParity (d + 1) G) (μ : Simplex V)
    (hμ : ∀ i, 0 < μ.weights i)
    (hp : 0 < weightPolynomial (d + 1) G (μ.weights : V → ℝ))
    (hθ : weightPolynomial (d + 1) G (μ.weights : V → ℝ) < overlapThreshold d)
    (hc : IsSimplexCritical (d + 1) G (μ.weights : V → ℝ)) :
    d + 1 ≤ sigNeg (tangentHessianForm d G μ) := by
  have hne : G.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    rw [h, weightPolynomial_empty] at hp
    exact lt_irrefl _ hp
  obtain ⟨hge, heq⟩ := spectral_index_rigidity d G hG hne hpar μ hμ hc
  by_contra h
  have hindex : sigNeg (tangentHessianForm d G μ) = d := by omega
  obtain ⟨_, _, _, _, hvalue⟩ := heq hindex
  exact (ne_of_lt hθ) hvalue

end Cocycle

end SharpTopologicalOverlap.Spectral
