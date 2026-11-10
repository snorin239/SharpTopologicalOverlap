module

public import SharpTopologicalOverlap.Comparison.Provider

/-! # The supported inverse of the canonical affine comparison

This closes Lemma 2.4 using the homology isomorphism of the actual affine
generator map. Every precomplex carrier, including those omitting vertices,
is retained simultaneously.
-/

@[expose] public noncomputable section

namespace SharpTopologicalOverlap.Comparison

open SharpTopologicalOverlap.Simplicial

variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V]

/-- The supported chain map of Lemma 2.4, normalized at the uniform point. -/
def supportedComparison (x : V) : SupportedComparison V x :=
  supportedComparison_of_canonicalHomology canonicalHomologyComparison x

/-- The carrier-preserving chain homotopy from `ιρ` to the identity. -/
def supportedQ (x : V) (k : ℕ) : SingularChain V k →ₗ[Coeff] SingularChain V (k + 1) :=
  (comparisonStages canonicalHomologyComparison x k).Q

theorem supportedQ_carriedBy (x : V) (L : PreAbstractSimplicialComplex V)
    (k : ℕ) (c : SingularChain V k) (hc : Singular.CarriedBy (realizedComplex L) c) :
    Singular.CarriedBy (realizedComplex L) (supportedQ x k c) :=
  (comparisonStages canonicalHomologyComparison x k).Q_carried L c hc

theorem boundary_supportedQ_zero (x : V) (c : SingularChain V 0) :
    singularBoundary 0 (supportedQ x 0 c) =
      affineChainMap 0 ((supportedComparison x).rho 0 c) + c :=
  singularBoundary_QZero x c

theorem boundary_supportedQ_succ (x : V) (k : ℕ) (c : SingularChain V (k + 1)) :
    singularBoundary (k + 1) (supportedQ x (k + 1) c) =
      c + supportedQ x k (singularBoundary k c) +
        affineChainMap (k + 1) ((supportedComparison x).rho (k + 1) c) :=
  boundary_nextQ canonicalHomologyComparison k (comparisonStages canonicalHomologyComparison x k) c

end SharpTopologicalOverlap.Comparison
