module

public import SharpTopologicalOverlap.WeightSpaces.DeletionHomotopy

/-! # Deforming polynomial carriers into their remaining face -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.WeightDeletion

open WeightPolynomial
open CategoryTheory CategoryTheory.Limits

variable {V : Type} [Fintype V] [DecidableEq V]

def carrier (S : Finset V) (k : ℕ) (G : Finset (Finset V)) (θ : ℝ) : Set (Simplex V) :=
  {μ | weightPolynomial k G (μ.weights : V → ℝ) < θ * (1 - mass S μ) ^ k}

def faceCarrier (S : Finset V) (k : ℕ) (G : Finset (Finset V)) (θ : ℝ) : Set (Simplex V) :=
  carrier S k G θ ∩ closedFace Sᶜ

theorem carrier_mass_lt_one (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) (μ : carrier S k G θ) : mass S μ.1 < 1 := by
  have ht := mass_le_one S μ.1
  by_contra h
  have heq : mass S μ.1 = 1 := le_antisymm ht (le_of_not_gt h)
  have hμ := μ.2
  change _ < _ at hμ
  rw [heq, sub_self, zero_pow (by omega), mul_zero] at hμ
  exact (not_lt_of_ge (nonneg k G (coordinate_nonneg μ.1))) hμ

theorem homotopyPoint_mem_carrier (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) (μ : carrier S k G θ) (r : unitInterval) :
    homotopyPoint S μ.1 (carrier_mass_lt_one S k hk G θ μ) r ∈ carrier S k G θ :=
  polynomial_homotopyPoint_lt S μ.1 _ r k G θ μ.2

def carrierDomain (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) : C(carrier S k G θ, Domain S) where
  toFun μ := ⟨μ.1, carrier_mass_lt_one S k hk G θ μ⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The deformation on the carrier as a genuine continuous map. -/
def carrierHomotopyMap (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) :
    C(unitInterval × carrier S k G θ, carrier S k G θ) where
  toFun p := ⟨homotopyPoint S p.2.1 (carrier_mass_lt_one S k hk G θ p.2) p.1,
    homotopyPoint_mem_carrier S k hk G θ p.2 p.1⟩
  continuous_toFun := by
    exact ((continuous_homotopyPoint S).comp
      (((carrierDomain S k hk G θ).continuous.comp continuous_snd).prodMk continuous_fst)).subtype_mk _

def carrierRetraction (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) : C(carrier S k G θ, faceCarrier S k G θ) where
  toFun μ := ⟨normalize S μ.1 (carrier_mass_lt_one S k hk G θ μ), by
    rw [← homotopyPoint_one S μ.1 (carrier_mass_lt_one S k hk G θ μ)]
    exact ⟨homotopyPoint_mem_carrier S k hk G θ μ 1,
      support_homotopyPoint_one S μ.1 _⟩⟩
  continuous_toFun := by
    exact ((continuous_normalize S).comp (carrierDomain S k hk G θ).continuous).subtype_mk _

/-- The homotopy starts at the identity and ends at the face retraction. -/
def carrierHomotopy (S : Finset V) (k : ℕ) (hk : 0 < k) (G : Finset (Finset V)) (θ : ℝ) :
    (ContinuousMap.id (carrier S k G θ)).Homotopy
      ((ContinuousMap.inclusion (Set.inter_subset_left : faceCarrier S k G θ ⊆ carrier S k G θ)).comp
        (carrierRetraction S k hk G θ)) where
  toContinuousMap := carrierHomotopyMap S k hk G θ
  map_zero_left μ := by
    apply Subtype.ext
    exact homotopyPoint_zero S μ.1 _
  map_one_left μ := by
    apply Subtype.ext
    exact homotopyPoint_one S μ.1 _

theorem carrierHomotopy_fixed (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) (μ : carrier S k G θ)
    (hμ : μ.1 ∈ faceCarrier S k G θ) (r : unitInterval) :
    carrierHomotopy S k hk G θ (r, μ) = μ := by
  apply Subtype.ext
  exact homotopyPoint_fixed S μ.1 _ hμ.2 r

def carrierHomotopyRel (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) :
    (ContinuousMap.id (carrier S k G θ)).HomotopyRel
      ((ContinuousMap.inclusion (Set.inter_subset_left : faceCarrier S k G θ ⊆ carrier S k G θ)).comp
        (carrierRetraction S k hk G θ))
      {μ | (μ : Simplex V) ∈ faceCarrier S k G θ} where
  toHomotopy := carrierHomotopy S k hk G θ
  prop' r μ hμ := carrierHomotopy_fixed S k hk G θ μ hμ r

/-- Transfer actual relative homology vanishing from the remaining face to
the whole polynomial carrier using the strong deformation retraction. -/
theorem fills_carrier_of_face_homology (S : Finset V) (k : ℕ) (hk : 0 < k)
    (G : Finset (Finset V)) (θ : ℝ) (J : Set (Simplex V))
    (hJA : J ⊆ faceCarrier S k G θ) (j : ℕ)
    (hH : IsZero ((TopPair.ofInclusion (X := TopCat.of (Simplex V)) hJA).singularHomology
      (ModuleCat.of Simplicial.Coeff Simplicial.Coeff) j)) :
    Singular.Fills (X := TopCat.of (Simplex V)) (carrier S k G θ) J j := by
  let hAB : faceCarrier S k G θ ⊆ carrier S k G θ := Set.inter_subset_left
  let r := carrierRetraction S k hk G θ
  haveI := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of (Simplex V)) hJA hAB r (carrierHomotopyRel S k hk G θ).symm
    (ModuleCat.of Simplicial.Coeff Simplicial.Coeff) j
  let φ := (TopPair.ofInclusion (X := TopCat.of (Simplex V)) hJA).singularHomologyMap
    (TopPair.ofInclusionMap hJA (hJA.trans hAB) (ContinuousMap.inclusion hAB)
      (fun _ hx => by simpa using hx))
    (ModuleCat.of Simplicial.Coeff Simplicial.Coeff) j
  exact Singular.fills_of_isZero_homology (hJA.trans hAB) j (hH.of_iso (asIso φ).symm)

end SharpTopologicalOverlap.WeightDeletion
