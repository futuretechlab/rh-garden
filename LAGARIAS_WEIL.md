# Lagarias Li/Weil normalization map

This note records the next formalization target from Jeffrey C. Lagarias,
*Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007),
1689--1740, Section 3, DOI 10.5802/aif.2311. Nothing here is currently a Lean theorem.

## Hypotheses and ambient test space

Lagarias fixes an irreducible cuspidal unitary automorphic representation
`pi` of `GL(N)`, its associated `xi(s,pi)`, and the multiset `Z(pi)` of its
zeros counted with multiplicity. The ambient space `A` consists of functions
holomorphic on `0 < Re(s) < 1` satisfying, uniformly in that strip outside
`|Im(s)| <= 1`, the bound `F(s) = O(1/|s|)`.

For `F,G in A`, equation (3.1) defines

```text
<F,G>_W(pi) = sum_{rho in Z(pi)} F(rho) * conjugate(G(1-conjugate(rho))).
```

The sum is absolute under the stated growth condition, is linear in `F` and
conjugate-linear in `G`, and uses zero multiplicities. The printed PDF's
overbar on the second factor is easy to lose in text extraction.

## Li test functions and exact normalization

The Li class `L` comprises rational functions in `C(s)` which vanish at
infinity and whose polar divisor is supported on `{0,1}`. Equation (3.2) is

```text
G_n(s) = 1 - (1 - 1/s)^n,   n in Z.
```

All `G_n` except `G_0=0` form a basis of `L`, and
`lambda_n(pi)=sum'_{rho in Z(pi)} G_n(rho)` uses star convergence.
Theorem 3.1 gives (3.3)

```text
<G_n,G_m>_W(pi)
  = lambda_n(pi) + lambda_{-m}(pi) - lambda_{n-m}(pi),
```

and its diagonal specialization (3.4)

```text
||G_n||_W(pi)^2
  = lambda_n(pi) + lambda_{-n}(pi)
  = 2 * Re(lambda_n(pi)).
```

The proof uses `G_{-m}(s)=G_m(1-s)` (3.5) and
`G_n(s)G_{-m}(s)=G_n(s)+G_{-m}(s)-G_{n-m}(s)` (3.6).
Thus the diagonal normalization is `2*Re(lambda_n)`, not `lambda_n` in
general. For Riemann zeta the coefficients are real, so it is `2*lambda_n`.
RHGarden is zero-based: `classicalLiRealCoefficient k` represents
`lambda_(k+1)`, corresponding to `G_(k+1)`.

The next formal boundary is to define this test family and the zero-sum/Weil
form with its convergence convention, then specialize (3.4). Until then all
edges through `WeilLiTestFunctions` and `WeilQuadraticValues` remain
`LiteratureCertified`.

## Lean-checked finite core and remaining limits

`formal/RHGarden/WeilFinite.lean` now checks (3.5), (3.6), and the exact
finite-Multiset analogue of (3.3). `Multiset` is essential: a cutoff retains
zero multiplicities. For a reflection-stable valid cutoff it also checks the
diagonal identity with `2*Re`.

These finite theorems do not identify `finiteLiZeroValue` with the project's
derivative-defined `classicalLiRealCoefficient`. Two analytic boundaries remain:

1. Lagarias's infinite Li zero sum is conditionally star-convergent. Proving
   derivative Li equals zero-sum Li requires a precise ordered cutoff family,
   star-convergence, and the logarithmic-derivative/Hadamard argument.
2. The Weil scalar product on class `A` is absolutely convergent because both
   tests have uniform `O(1/|s|)` growth. Passing the finite (3.3) identity to
   the infinite form requires proving convergence and compatibility of the
   same cutoff family with that absolutely convergent sum.

Ordinary `tsum` is therefore not used as a common encoding for both limits.
The notation `||G_n||_W^2` also carries no unconditional positivity claim:
positive semidefiniteness of the infinite Weil form is RH-level content.

## Pinned mathlib reconnaissance

Pinned mathlib supplies useful local infrastructure:

- `Mathlib.Analysis.Analytic.IsolatedZeros`: formal-series `order`,
  `HasFPowerSeriesAt.locally_ne_zero`, and analytic isolated-zero principles;
- `Mathlib.Analysis.Meromorphic.Order`: `meromorphicOrderAt`, analytic order
  comparison, and order arithmetic;
- `Mathlib.Analysis.Meromorphic.Divisor`: `MeromorphicOn.divisor` as a
  `Function.locallyFinsuppWithin`, plus finite support on compact balls/spheres;
- `Mathlib.NumberTheory.LSeries.ZetaZeros`: `riemannZetaZeros`,
  `isClosed_riemannZetaZeros`, `isDiscrete_riemannZetaZeros`, compact
  intersection finiteness, and a cofinite-to-cocompact tendsto theorem.

What is not supplied as a ready-made object is the required multiplicity-aware
ordered enumeration/cutoff of xi zeros, Lagarias star-summation, or a Hadamard
product theorem already specialized to xi and its logarithmic derivative.
The divisor API is the strongest candidate foundation for building those.

## Canonical xi divisor and corrected height partial sums

`formal/RHGarden/XiZeroCutoff.lean` now uses `MeromorphicOn.divisor` as the
authoritative multiplicity object. Its support is exactly the xi zero set, and
its nonnegative integer value is converted to `xiMultiplicity`. Compactness of
local finiteness of divisor support produce canonical finite support sets.
`xiZeroRadialCutoff T` uses `||rho||<=T`; `xiZeroHeightCutoff T` uses
`|Im rho|<=T`. Both repeat points using analytic multiplicity and have exact
count theorems.

The definition

```text
liStarPartial T n = finiteLiZeroValue (xiZeroHeightCutoff T) n
```

is Lagarias's genuine incomplete Li coefficient ordering. Equation (6.106)
uses `|Im rho|<=T`, not a radial norm bound. Only the proposition
`LiStarConvergesTo n L := Tendsto (fun T => liStarPartial T n) atTop (nhds L)`
is introduced. No chosen limit and no convergence theorem are present.

The normalization boundary is recorded faithfully: the derivative coefficient
at zero-based index `k` first targets the negative star index `-(k+1)` via the
open proposition `ClassicalLiEqualsNegativeStar`. Positive/negative star-index
symmetry is a separate open proposition `StarLiSymmetry`.

This sign has now been re-audited directly against Lagarias's equations
(1.1)--(1.5): his derivative coefficient `tilde lambda_m` in (1.3) is
`lambda_{-m}`. For the Riemann zeta specialization the zero symmetries then
give `lambda_{-m}=lambda_m`; that second equality must not be folded into the
first identification step.

Weil reflection preserves imaginary part exactly. Lean also checks analytic
multiplicity preservation under conjugation and under `s -> 1-s`; hence the
height cutoff is exactly reflection-stable with multiplicity, and the finite
diagonal `2*Re` Weil identity applies to it unconditionally.

Radial cutoffs remain auxiliary and are not asserted reflection-stable. Lean checks only

```text
abs (||weilReflect rho|| - ||rho||) <= 1.
```

Thus reflection changes a radius-`T` cutoff only within a bounded-width shell;
no claim that the shell contribution vanishes is made. The radial object is
retained because Lagarias uses radial cutoffs in the interpolation section.

The earlier stable-mathlib-only state left star convergence open. The pinned
Zeta23 dependency now supplies the local unit-height zero bound, and RH Garden
uses it to prove `liStarConvergence` for every integer index.

## Hadamard identification boundary

Star convergence is now supplied unconditionally through the pinned Zeta23
local zero-count theorem, but convergence does not identify the limit's value.
Pinned Zeta23 has the exact local completed-zeta identities
`logDeriv_completedZeta`, `logDeriv_completedZeta_one_sub`, and
`completedZeta_zeros_strip`. Its theorem
`zeta_logDeriv_partial_fraction` is instead a finite disk approximation with
an explicit `O(log (|t|+3))` error. `zero_sum_limit` treats the absolutely
convergent transformed zero side of the Weil explicit formula. Neither is a
global Hadamard/logarithmic-derivative identity for xi.

`RHGarden.LiHadamardFinite` records the convergence-free genus-one algebra.
The remaining analytic input is a xi-specific Hadamard factorization, stated
there as `XiGenusOneFactorization`: local uniform convergence of the primary
factor product together with an exponential quotient of degree at most one.
One must then determine its linear constant (equivalently use the xi
functional equation), pass logarithmic derivatives locally uniformly near
`s=1`, and apply the checked finite Li jet identity. Mathlib supplies generic
locally uniform infinite-product and logarithmic-derivative tools, including
`logDeriv_tprod_eq_tsum`, but no theorem proving this factorization from
entire order-one growth. Consequently `ClassicalLiEqualsNegativeStar`
remains open and no garden trust edge is upgraded by the finite algebra alone.
