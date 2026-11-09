module

public import SharpTopologicalOverlap.Singular
public import TauCeti.AlgebraicTopology.Singular.Relative
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TauCeti.Topology.Category.TopPair

/-! # Relative homology as a concrete filling criterion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace SharpTopologicalOverlap.Singular

/-- Vanishing homology fills cycles on the actual degree modules, including
degree zero with its zero outgoing differential. -/
theorem complex_cycle_fills (K : ChainComplex (ModuleCat.{0} Coeff) ℕ) (k : ℕ)
    (hK : IsZero (K.homology k)) (c : K.X k)
    (hc : K.d k ((ComplexShape.down ℕ).next k) c = 0) :
    ∃ w : K.X (k + 1), K.d (k + 1) k w = c := by
  have he := (K.exactAt_iff_isZero_homology k).mpr hK
  have hsc : (K.sc' (k + 1) k ((ComplexShape.down ℕ).next k)).Exact :=
    (K.exactAt_iff' (k + 1) k _ (by simp) rfl).mp he
  exact (ShortComplex.moduleCat_exact_iff _).mp hsc c hc

/-- A short exact sequence of chain complexes converts a relative homology
vanishing statement into a boundary plus a chain from the subcomplex. -/
theorem shortExact_relative_fills
    (S : ShortComplex (ChainComplex (ModuleCat.{0} Coeff) ℕ))
    (hS : S.ShortExact) (k : ℕ) (hH : IsZero (S.X₃.homology k))
    (c : S.X₂.X k)
    (hc : (S.g.f ((ComplexShape.down ℕ).next k))
      (S.X₂.d k ((ComplexShape.down ℕ).next k) c) = 0) :
    ∃ (w : S.X₂.X (k + 1)) (b : S.X₁.X k),
      c = S.X₂.d (k + 1) k w + S.f.f k b := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  have hcycle : S.X₃.d k ((ComplexShape.down ℕ).next k) (S.g.f k c) = 0 := by
    rw [← ConcreteCategory.comp_apply,
      S.g.comm k ((ComplexShape.down ℕ).next k), ConcreteCategory.comp_apply]
    exact hc
  obtain ⟨v, hv⟩ := complex_cycle_fills S.X₃ k hH (S.g.f k c) hcycle
  obtain ⟨w, hw⟩ := (hdeg (k + 1)).moduleCat_surjective_g v
  change S.g.f (k + 1) w = v at hw
  have hker : S.g.f k (c - S.X₂.d (k + 1) k w) = 0 := by
    rw [map_sub]
    have hcomm := ConcreteCategory.congr_hom (S.g.comm (k + 1) k) w
    simp only [ModuleCat.comp_apply] at hcomm
    rw [← hcomm, hw, hv, sub_self]
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hdeg k).exact _ hker
  refine ⟨w, b, ?_⟩
  change S.f.f k b = c - S.X₂.d (k + 1) k w at hb
  rw [hb]
  abel

set_option backward.isDefEq.respectTransparency.types false in
/-- The homology definition of a pair gives the concrete filling criterion
of §2.3, in the one ambient singular chain module. -/
theorem relative_cycle_fills {X : TopCat.{0}} (A : Set X) (k : ℕ)
    (hH : IsZero ((TopPair.ofSubset A).singularHomology (ModuleCat.of Coeff Coeff) k))
    (c : Chain X k) (hc : IsRelativeCycle A k c) :
    ∃ (w : Chain X (k + 1)) (b : Chain X k),
      CarriedBy A b ∧ c = boundary k w + b := by
  let P := TopPair.ofSubset A
  let S := P.singularChainComplexShortComplex (ModuleCat.of Coeff Coeff)
  have hS : S.ShortExact := P.shortExact_singularChainComplexShortComplex _
  have hproj : ∀ (j : ℕ) (b : Chain (TopCat.of A) j), S.g.f j (pushforward (inclusion A) j b) = 0 := by
    intro j b
    have h := ConcreteCategory.congr_hom (congrArg (fun f => f.f j) S.zero) b
    exact h
  have hcycle : (S.g.f ((ComplexShape.down ℕ).next k))
      (S.X₂.d k ((ComplexShape.down ℕ).next k) c) = 0 := by
    cases k with
    | zero =>
      have hd : S.X₂.d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
        HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down_Rel])
      rw [hd]
      exact map_zero _
    | succ j =>
      obtain ⟨b, hb⟩ := hc
      have hnext : (ComplexShape.down ℕ).next (j + 1) = j := ChainComplex.next_nat_succ j
      rw [hnext]
      change S.g.f j (boundary j c) = 0
      exact (congrArg (fun a : Chain X j => S.g.f j a) hb).symm.trans (hproj j b)
  obtain ⟨w, b, hb⟩ := shortExact_relative_fills S hS k hH c hcycle
  exact ⟨w, pushforward (inclusion A) k b, ⟨b, rfl⟩, hb⟩

/-- Concrete relative fillings in a pair of subsets of one ambient space. -/
def Fills {X : TopCat.{0}} (B J : Set X) (k : ℕ) : Prop :=
  ∀ c : Chain X k, CarriedBy B c → IsRelativeCycle J k c →
    ∃ (w : Chain X (k + 1)) (b : Chain X k),
      CarriedBy B w ∧ CarriedBy J b ∧ c = boundary k w + b

set_option backward.isDefEq.respectTransparency.types false in
/-- Homology vanishing gives fillings with both carriers retained in the
original ambient space, rather than merely in an isomorphic chain module. -/
theorem fills_of_isZero_homology {X : TopCat.{0}} {J B : Set X} (hJB : J ⊆ B) (k : ℕ)
    (hH : IsZero ((TopPair.ofInclusion hJB).singularHomology (ModuleCat.of Coeff Coeff) k)) :
    Fills B J k := by
  intro c hc hcJ
  obtain ⟨cB, hcB⟩ := hc
  let P := TopPair.ofInclusion hJB
  let S := P.singularChainComplexShortComplex (ModuleCat.of Coeff Coeff)
  have hS : S.ShortExact := P.shortExact_singularChainComplexShortComplex _
  have hproj : ∀ (j : ℕ) (b : Chain (TopCat.of J) j),
      S.g.f j (pushforward P.map j b) = 0 := by
    intro j b
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.f j) S.zero) b
  have hcycle : (S.g.f ((ComplexShape.down ℕ).next k))
      (S.X₂.d k ((ComplexShape.down ℕ).next k) cB) = 0 := by
    cases k with
    | zero =>
      have hd : S.X₂.d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
        HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down_Rel])
      rw [hd]
      exact map_zero _
    | succ j =>
      obtain ⟨b, hb⟩ := hcJ
      have hbd : boundary j cB = pushforward P.map j b := by
        apply inclusion_injective B
        calc
          pushforward (inclusion B) j (boundary j cB) = boundary j c := by
            rw [← boundary_pushforward, hcB]
          _ = pushforward (inclusion J) j b := hb.symm
          _ = pushforward (inclusion B) j (pushforward P.map j b) :=
            pushforward_comp P.map (inclusion B) b
      rw [ChainComplex.next_nat_succ]
      change S.g.f j (boundary j cB) = 0
      exact (congrArg (fun a : Chain (TopCat.of B) j => S.g.f j a) hbd).trans (hproj j b)
  obtain ⟨w, b, hb⟩ := shortExact_relative_fills S hS k hH cB hcycle
  change cB = boundary (X := TopCat.of B) k w +
    pushforward (X := TopCat.of J) (Y := TopCat.of B) P.map k b at hb
  refine ⟨pushforward (inclusion B) (k + 1) w, pushforward (inclusion J) k b,
    ⟨w, rfl⟩, ⟨b, rfl⟩, ?_⟩
  calc
    c = pushforward (inclusion B) k cB := hcB.symm
    _ = pushforward (inclusion B) k (boundary (X := TopCat.of B) k w +
        pushforward (X := TopCat.of J) (Y := TopCat.of B) P.map k b) :=
      congrArg (pushforward (inclusion B) k) hb
    _ = boundary k (pushforward (inclusion B) (k + 1) w) +
        pushforward (inclusion J) k b := by
      rw [map_add, boundary_pushforward, ← pushforward_comp]
      rfl

theorem isRelativeCycle_mono {X : TopCat.{0}} {J A : Set X} (hJA : J ⊆ A)
    {k : ℕ} {c : Chain X k} (hc : IsRelativeCycle J k c) : IsRelativeCycle A k c := by
  cases k with
  | zero => trivial
  | succ k => exact carriedBy_mono hJA hc

theorem remainder_isRelativeCycle {X : TopCat.{0}} {J : Set X} {k : ℕ}
    {c b : Chain X k} {w : Chain X (k + 1)} (hc : IsRelativeCycle J k c)
    (heq : c = boundary k w + b) : IsRelativeCycle J k b := by
  cases k with
  | zero => trivial
  | succ j =>
    have hb : boundary j b = boundary j c := by
      rw [heq, map_add, boundary_boundary, zero_add]
    change CarriedBy J (boundary j b)
    rw [hb]
    exact hc

theorem fills_refl {X : TopCat.{0}} (B : Set X) (k : ℕ) : Fills B B k := by
  intro c hc _
  exact ⟨0, c, carriedBy_zero B, hc, by simp⟩

/-- The concrete nested-pair argument of Lemma 2.2(c). -/
theorem fills_trans {X : TopCat.{0}} {J A B : Set X} (hJA : J ⊆ A) (hAB : A ⊆ B)
    {k : ℕ} (hBA : Fills B A k) (hAJ : Fills A J k) : Fills B J k := by
  intro c hcB hcJ
  obtain ⟨w, b, hwB, hbA, heq⟩ := hBA c hcB (isRelativeCycle_mono hJA hcJ)
  obtain ⟨w', b', hw'A, hb'J, heq'⟩ := hAJ b hbA (remainder_isRelativeCycle hcJ heq)
  refine ⟨w + w', b', carriedBy_add hwB (carriedBy_mono hAB hw'A), hb'J, ?_⟩
  rw [map_add, heq, heq']
  abel

theorem fills_chain {X : TopCat.{0}} (Y : ℕ → Set X) (hY : Monotone Y) (k l : ℕ)
    (hF : ∀ i < l, Fills (Y (i + 1)) (Y i) k) : Fills (Y l) (Y 0) k := by
  induction l with
  | zero => exact fills_refl _ _
  | succ l ih =>
    exact fills_trans (hY (Nat.zero_le l)) (hY (Nat.le_succ l))
      (hF l (Nat.lt_succ_self l)) (ih (fun i hi => hF i (Nat.lt_succ_of_lt hi)))

end SharpTopologicalOverlap.Singular
