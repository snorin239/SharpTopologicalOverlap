module

public import SharpTopologicalOverlap.Geometry.Segments
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # A proper scalar parameterization of an affine line -/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Geometry.SimplexParity

open Set Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A base point and a nonzero spanning direction of an affine line. -/
structure Line (L : AffineSubspace ℝ E) where
  base : E
  base_mem : base ∈ L
  vector : E
  vector_mem : vector ∈ L.direction
  vector_ne : vector ≠ 0
  direction_eq : L.direction = Submodule.span ℝ {vector}

theorem exists_line (L : AffineSubspace ℝ E) (hne : (L : Set E).Nonempty)
    (hrank : finrank ℝ L.direction = 1) : Nonempty (Line L) := by
  obtain ⟨x, hx⟩ := hne
  have hnonbot : L.direction ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hrank
    omega
  obtain ⟨v, hv, hvne⟩ := L.direction.ne_bot_iff.mp hnonbot
  exact ⟨⟨x, hx, v, hv, hvne, eq_span_singleton_of_mem_of_finrank_eq_one
    hrank hv hvne⟩⟩

namespace Line

variable {L : AffineSubspace ℝ E} (l : Line L)

def point (t : ℝ) : E := l.base + t • l.vector

theorem point_mem (t : ℝ) : l.point t ∈ L := by
  rw [point, add_comm]
  exact L.vadd_mem_of_mem_direction (L.direction.smul_mem t l.vector_mem) l.base_mem

theorem point_surjective {x : E} (hx : x ∈ L) : ∃ t : ℝ, l.point t = x := by
  have hdir := L.vsub_mem_direction hx l.base_mem
  rw [l.direction_eq] at hdir
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdir
  refine ⟨t, ?_⟩
  change l.base + t • l.vector = x
  rw [ht]
  simp

theorem isClosedEmbedding_point : Topology.IsClosedEmbedding l.point := by
  exact (Homeomorph.addLeft l.base).isClosedEmbedding.comp
    (isClosedEmbedding_smul_left (𝕜 := ℝ) l.vector_ne)

theorem coord_point (f : E →ᴬ[ℝ] ℝ) (t : ℝ) :
    f (l.point t) = f l.base + t * f.contLinear l.vector := by
  have h := f.map_vadd l.base (t • l.vector)
  simpa only [point, vadd_eq_add, map_smul, smul_eq_mul, add_comm] using h

def swapInf {S T : AffineSubspace ℝ E} (l : Line (S ⊓ T)) : Line (T ⊓ S) where
  base := l.base
  base_mem := by simpa only [inf_comm] using l.base_mem
  vector := l.vector
  vector_mem := by simpa only [inf_comm] using l.vector_mem
  vector_ne := l.vector_ne
  direction_eq := by simpa only [inf_comm] using l.direction_eq

end Line

end SharpTopologicalOverlap.Geometry.SimplexParity
