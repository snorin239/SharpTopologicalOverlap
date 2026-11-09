# Formalization blueprint

## First target — Theorem 1.2

Let $d\ge 2$ and $n\ge d+1$ be integers. Write $X_{n,d}$ for the $d$-skeleton
of the simplex on $n$ vertices. For a continuous map
$f:|X_{n,d}|\to\mathbb R^d$, let $\operatorname{ov}(f)$ be the largest number
of closed $d$-faces whose images contain a common point. Put

$$
C_d=\sum_{p=1}^{d}\binom{d+1}{p+1}(d+1-p)\left\lfloor\frac{d}{p}\right\rfloor.
$$

If $n>C_d$, Theorem 1.2 gives

$$
\operatorname{ov}(f)\ge\left(\frac{n-C_d}{d+1}\right)^{d+1}.
$$

In Lean, $C_d$ is a natural number. The quotient in the overlap inequality
is a real quotient, whereas the quotient defining $C_d$ uses natural-number
division.

| Paper passage | Role in the proof |
| --- | --- |
| §2 | Realized skeleton, closed faces, and chains and cochains over $\mathbb F_2$ |
| §3 and Appendix A | Intersection cochains for a continuous map and control of their supports |
| §4 | Spectral estimate for the negative index of a cocycle weight polynomial |
| §5 | Relative homology vanishing via ordinary Morse theory and a logarithmic barrier |
| §6 | Exceptional vertices, weight spaces, and descending fillings yielding the finite bound |

## Second target — Theorem 1.1

Let $c_d^{\mathrm{top}}$ be the limit inferior, as $n\to\infty$, of the minimum
of $\operatorname{ov}(f)/\binom{n}{d+1}$ over all such continuous maps. For
each $d\ge 2$, Theorem 1.1 asserts

$$
c_d^{\mathrm{top}}=\frac{(d+1)!}{(d+1)^{d+1}}.
$$

Section 7 obtains the lower bound from Theorem 1.2 and the upper bound from
the affine construction of Bukh, Matoušek, and Nivasch (`thm:bmn`).

The [November 8 dependency assessment](lean_formalization_theorem_1_2_assessment_2026-11-08.md)
concerns an earlier draft. Its library leads should be checked against the
[November 9 proof](../paper/sharp_topological_overlap.pdf).
