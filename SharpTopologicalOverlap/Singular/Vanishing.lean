module

public import SharpTopologicalOverlap.Singular.Relative

/-! # Concrete fillings imply relative homology vanishing -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace SharpTopologicalOverlap.Singular

theorem shortExact_isZero_homology_of_relative_fills
    (S : ShortComplex (ChainComplex (ModuleCat.{0} Coeff) ℕ)) (hS : S.ShortExact) (k : ℕ)
    (hfill : ∀ c : S.X₂.X k,
      S.g.f ((ComplexShape.down ℕ).next k) (S.X₂.d k ((ComplexShape.down ℕ).next k) c) = 0 →
      ∃ (w : S.X₂.X (k + 1)) (b : S.X₁.X k), c = S.X₂.d (k + 1) k w + S.f.f k b) :
    IsZero (S.X₃.homology k) := by
  apply (S.X₃.exactAt_iff_isZero_homology k).mp
  apply (S.X₃.exactAt_iff' (k + 1) k _ (by simp) rfl).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  obtain ⟨c, hc⟩ := (hdeg k).moduleCat_surjective_g z
  change S.g.f k c = z at hc
  have hcycle : S.g.f ((ComplexShape.down ℕ).next k)
      (S.X₂.d k ((ComplexShape.down ℕ).next k) c) = 0 := by
    have heq := ConcreteCategory.congr_hom (S.g.comm k ((ComplexShape.down ℕ).next k)) c
    simp only [ModuleCat.comp_apply] at heq
    rw [← heq, hc]
    exact hz
  obtain ⟨w, b, heq⟩ := hfill c hcycle
  refine ⟨S.g.f (k + 1) w, ?_⟩
  change S.X₃.d (k + 1) k (S.g.f (k + 1) w) = z
  have hcomm := ConcreteCategory.congr_hom (S.g.comm (k + 1) k) w
  simp only [ModuleCat.comp_apply] at hcomm
  have hzero : S.g.f k (S.f.f k b) = 0 :=
    ConcreteCategory.congr_hom (congrArg (fun f => f.f k) S.zero) b
  rw [heq, map_add, hzero, add_zero] at hc
  exact hcomm.trans hc

set_option backward.isDefEq.respectTransparency.types false in
/-- The converse of the ambient filling criterion, used to turn the
explicit sublevel chain construction into the stated homology theorem. -/
theorem isZero_homology_of_fills {X : TopCat.{0}} {J B : Set X} (hJB : J ⊆ B) (k : ℕ)
    (hF : Fills B J k) :
    IsZero ((TopPair.ofInclusion hJB).singularHomology (ModuleCat.of Coeff Coeff) k) := by
  let P := TopPair.ofInclusion hJB
  let S := P.singularChainComplexShortComplex (ModuleCat.of Coeff Coeff)
  have hS : S.ShortExact := P.shortExact_singularChainComplexShortComplex _
  apply shortExact_isZero_homology_of_relative_fills S hS k
  intro c hc
  have hrel : IsRelativeCycle J k (pushforward (inclusion B) k c) := by
    cases k with
    | zero => trivial
    | succ j =>
      have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
      have hzero : S.g.f j (boundary (X := TopCat.of B) j c) = 0 := by
        rw [ChainComplex.next_nat_succ] at hc
        exact hc
      obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hdeg j).exact _ hzero
      change pushforward P.map j b = boundary j c at hb
      refine ⟨b, ?_⟩
      calc
        pushforward (inclusion J) j b =
            pushforward (inclusion B) j (pushforward P.map j b) :=
          pushforward_comp P.map (inclusion B) b
        _ = pushforward (inclusion B) j (boundary j c) := congrArg (pushforward (inclusion B) j) hb
        _ = boundary j (pushforward (inclusion B) (j + 1) c) := (boundary_pushforward _ _).symm
  obtain ⟨w, b, hw, hb, heq⟩ := hF _ ⟨c, rfl⟩ hrel
  obtain ⟨wB, hwB⟩ := hw
  obtain ⟨bJ, hbJ⟩ := hb
  refine ⟨wB, bJ, ?_⟩
  change c = boundary (X := TopCat.of B) k wB + pushforward (X := TopCat.of J) (Y := TopCat.of B) P.map k bJ
  apply inclusion_injective B
  rw [map_add, ← boundary_pushforward, hwB, ← pushforward_comp]
  exact heq.trans (congrArg (fun a => boundary k w + a) hbJ.symm)

end SharpTopologicalOverlap.Singular
