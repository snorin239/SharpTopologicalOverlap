module

public import SharpTopologicalOverlap.Simplicial
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Concrete element consequences of a homology isomorphism -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

section ShortComplex

variable (S : ShortComplex (ModuleCat.{0} Coeff))

/-- The homology class of a concrete cycle. -/
def cycleClass (c : S.X₂) (hc : S.g c = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨c, hc⟩)

theorem cycleClass_iota (c : S.X₂) (hc : S.g c = 0) :
    S.homologyι (cycleClass S c hc) = S.pOpcycles c := by
  have h := ConcreteCategory.congr_hom S.homology_π_ι (S.moduleCatCyclesIso.inv ⟨c, hc⟩)
  have hi := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨c, hc⟩
  exact h.trans (congrArg S.pOpcycles hi)

theorem cycleClass_eq_zero_iff (c : S.X₂) (hc : S.g c = 0) :
    cycleClass S c hc = 0 ↔ ∃ b : S.X₁, S.f b = c := by
  have hinj : Function.Injective S.homologyι :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_zero_iff c).mp
    rw [← cycleClass_iota S c hc, h, map_zero]
  · intro h
    apply hinj
    rw [cycleClass_iota, map_zero]
    exact (S.moduleCat_pOpcycles_eq_zero_iff c).mpr h

theorem exists_cycleClass (h : S.homology) :
    ∃ (c : S.X₂) (hc : S.g c = 0), cycleClass S c hc = h := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance h
  let c := S.moduleCatCyclesIso.hom a
  refine ⟨c.1, c.2, ?_⟩
  have hi : S.moduleCatCyclesIso.inv (S.moduleCatCyclesIso.hom a) = a :=
    ConcreteCategory.congr_hom S.moduleCatCyclesIso.hom_inv_id a
  exact (congrArg S.homologyπ hi).trans ha

variable {S} {T : ShortComplex (ModuleCat.{0} Coeff)} (φ : S ⟶ T)

theorem shortMap_cycle (c : S.X₂) (hc : S.g c = 0) : T.g (φ.τ₂ c) = 0 := by
  have h := ConcreteCategory.congr_hom φ.comm₂₃ c
  simp only [ModuleCat.comp_apply] at h
  exact h.trans (by rw [hc, map_zero])

theorem cycleClass_natural (c : S.X₂) (hc : S.g c = 0) :
    ShortComplex.homologyMap φ (cycleClass S c hc) =
      cycleClass T (φ.τ₂ c) (shortMap_cycle φ c hc) := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  have hn := ConcreteCategory.congr_hom (ShortComplex.homologyι_naturality φ) (cycleClass S c hc)
  have ho := ConcreteCategory.congr_hom (ShortComplex.p_opcyclesMap φ) c
  exact hn.trans ((congrArg (ShortComplex.opcyclesMap φ) (cycleClass_iota S c hc)).trans
    (ho.trans (cycleClass_iota T _ _).symm))

theorem shortMap_cycle_fills_of_mono_homologyMap [Mono (ShortComplex.homologyMap φ)]
    (c : S.X₂) (hc : S.g c = 0) (hw : ∃ w : T.X₁, T.f w = φ.τ₂ c) :
    ∃ b : S.X₁, S.f b = c := by
  apply (cycleClass_eq_zero_iff S c hc).mp
  apply (ModuleCat.mono_iff_injective (ShortComplex.homologyMap φ)).mp inferInstance
  rw [cycleClass_natural, map_zero]
  exact (cycleClass_eq_zero_iff T _ _).mpr hw

theorem shortMap_cycle_surjective_of_epi_homologyMap [Epi (ShortComplex.homologyMap φ)]
    (z : T.X₂) (hz : T.g z = 0) :
    ∃ (b : S.X₂) (_hb : S.g b = 0) (q : T.X₁), T.f q = z - φ.τ₂ b := by
  obtain ⟨h, hh⟩ := (ModuleCat.epi_iff_surjective (ShortComplex.homologyMap φ)).mp inferInstance
    (cycleClass T z hz)
  obtain ⟨b, hb, hclass⟩ := exists_cycleClass S h
  have heq : cycleClass T (φ.τ₂ b) (shortMap_cycle φ b hb) = cycleClass T z hz := by
    rw [← cycleClass_natural φ b hb, hclass]
    exact hh
  have hop : T.pOpcycles z = T.pOpcycles (φ.τ₂ b) := by
    simpa only [cycleClass_iota] using (congrArg T.homologyι heq).symm
  obtain ⟨q, hq⟩ := (T.moduleCat_pOpcycles_eq_iff z (φ.τ₂ b)).mp hop
  exact ⟨b, hb, q, hq⟩

end ShortComplex

section ChainComplex

variable {K L : ChainComplex (ModuleCat.{0} Coeff) ℕ} (f : K ⟶ L) (k : ℕ)

/-- A cycle whose image bounds has a filling whenever the induced homology
map is injective. Degree zero uses the actual zero outgoing differential. -/
theorem homologyMap_cycle_injective [Mono (HomologicalComplex.homologyMap f k)]
    (c : K.X k) (hc : K.d k ((ComplexShape.down ℕ).next k) c = 0)
    (hw : ∃ w : L.X (k + 1), L.d (k + 1) k w = f.f k c) :
    ∃ b : K.X (k + 1), K.d (k + 1) k b = c := by
  have hprev : (ComplexShape.down ℕ).prev k = k + 1 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} Coeff) (ComplexShape.down ℕ) k).map f
  letI : Mono (ShortComplex.homologyMap φ) := by
    change Mono (HomologicalComplex.homologyMap f k)
    infer_instance
  have hw' : ∃ w : (L.sc k).X₁, (L.sc k).f w = φ.τ₂ c := by
    change ∃ w : L.X ((ComplexShape.down ℕ).prev k),
      L.d ((ComplexShape.down ℕ).prev k) k w = f.f k c
    rw [hprev]
    exact hw
  have h := shortMap_cycle_fills_of_mono_homologyMap φ c hc hw'
  change ∃ b : K.X ((ComplexShape.down ℕ).prev k), K.d ((ComplexShape.down ℕ).prev k) k b = c at h
  rw [hprev] at h
  exact h

/-- Every target cycle is homologous to the image of an actual source cycle
when the induced homology map is surjective. -/
theorem homologyMap_cycle_surjective [Epi (HomologicalComplex.homologyMap f k)]
    (z : L.X k) (hz : L.d k ((ComplexShape.down ℕ).next k) z = 0) :
    ∃ (b : K.X k) (_hb : K.d k ((ComplexShape.down ℕ).next k) b = 0) (q : L.X (k + 1)),
      L.d (k + 1) k q = z - f.f k b := by
  have hprev : (ComplexShape.down ℕ).prev k = k + 1 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} Coeff) (ComplexShape.down ℕ) k).map f
  letI : Epi (ShortComplex.homologyMap φ) := by
    change Epi (HomologicalComplex.homologyMap f k)
    infer_instance
  have h := shortMap_cycle_surjective_of_epi_homologyMap φ z hz
  change ∃ (b : K.X k) (_hb : K.d k ((ComplexShape.down ℕ).next k) b = 0)
    (q : L.X ((ComplexShape.down ℕ).prev k)), L.d ((ComplexShape.down ℕ).prev k) k q = z - f.f k b at h
  rw [hprev] at h
  exact h

end ChainComplex

end SharpTopologicalOverlap.Comparison
