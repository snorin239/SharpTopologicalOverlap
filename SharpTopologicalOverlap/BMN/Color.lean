module

public import SharpTopologicalOverlap.BMN.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Find

/-! # Prefix types for the BMN construction -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.BMN

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A failed coordinate comparison, with `d` as the terminal sentinel. -/
def typeStop {d : ℕ} (x r : Fin d → ℝ) (k : ℕ) : Prop :=
  k = d ∨ ∃ j : Fin d, j.val = k ∧ x j ≤ r j

theorem exists_typeStop {d : ℕ} (x r : Fin d → ℝ) :
    ∃ k, typeStop x r k := ⟨d, Or.inl rfl⟩

/-- The length of the initial coordinate segment strictly above the query.
The value is `d` if every coordinate is strictly above it. -/
def pointType {d : ℕ} (x r : Fin d → ℝ) : Fin (d + 1) :=
  ⟨Nat.find (exists_typeStop x r), Nat.lt_succ_of_le
    (Nat.find_min' (exists_typeStop x r) (show typeStop x r d from Or.inl rfl))⟩

/-- Characterize a prefix type by all earlier successes and the first failure. -/
theorem pointType_eq {d : ℕ} (x r : Fin d → ℝ) (k : Fin (d + 1))
    (hprefix : ∀ j : Fin d, j.val < k.val → r j < x j)
    (hfailure : ∀ j : Fin d, j.val = k.val → x j ≤ r j) :
    pointType x r = k := by
  apply Fin.ext
  change Nat.find (exists_typeStop x r) = k.val
  apply (Nat.find_eq_iff (exists_typeStop x r)).mpr
  constructor
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ k.isLt) with hk | hk
    · exact Or.inr ⟨⟨k.val, hk⟩, rfl, hfailure ⟨k.val, hk⟩ rfl⟩
    · exact Or.inl hk
  · intro m hm
    rintro (hmd | ⟨j, hjm, hjle⟩)
    · omega
    · exact (not_lt_of_ge hjle) (hprefix j (by omega))

/-- Interleaving rows have consecutive prefix types. -/
theorem pointType_eq_of_interleaves {d : ℕ}
    (q : Fin (d + 1) → Fin d → ℝ) (r : Fin d → ℝ)
    (hmono : ∀ j, Monotone (fun k => q k j))
    (hinter : ∀ j : Fin d, q j.castSucc j < r j ∧ r j < q j.succ j) :
    ∀ k : Fin (d + 1), pointType (q k) r = k := by
  intro k
  apply pointType_eq
  · intro j hj
    exact (hinter j).2.trans_le (hmono j (show j.succ ≤ k by
      change j.val + 1 ≤ k.val
      omega))
  · intro j hj
    have hkj : k = j.castSucc := Fin.ext hj.symm
    rw [hkj]
    exact (hinter j).1.le

/-- The interleaving property of a sorted source face supplies the injective
coloring needed by the finite counting theorem. -/
theorem injOn_pointType_of_interleaves {d n : ℕ}
    (p : Fin n → Fin d → ℝ) (r : Fin d → ℝ)
    (σ : Finset (Fin n)) (hσ : σ.card = d + 1)
    (hmono : ∀ j, Monotone (fun i => p i j))
    (hinter : ∀ j : Fin d,
      p (σ.orderEmbOfFin hσ j.castSucc) j < r j ∧
        r j < p (σ.orderEmbOfFin hσ j.succ) j) :
    Set.InjOn (fun i => pointType (p i) r) (σ : Set (Fin n)) := by
  let e := σ.orderEmbOfFin hσ
  have htypes : ∀ k, pointType (p (e k)) r = k :=
    pointType_eq_of_interleaves (fun k => p (e k)) r
      (fun j => (hmono j).comp e.monotone) hinter
  intro i hi i' hi' heq
  have hiRange : i ∈ Set.range e := by
    simpa only [e, Finset.range_orderEmbOfFin] using hi
  have hiRange' : i' ∈ Set.range e := by
    simpa only [e, Finset.range_orderEmbOfFin] using hi'
  obtain ⟨a, rfl⟩ := hiRange
  obtain ⟨b, rfl⟩ := hiRange'
  have hab : a = b := by simpa only [htypes] using heq
  exact congrArg e hab

end SharpTopologicalOverlap.BMN
