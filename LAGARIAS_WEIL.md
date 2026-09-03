# Lagarias Li/Weil normalization map

This note records the RH Garden specialization of Jeffrey C. Lagarias,
*Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007),
1689--1740, Section 3, DOI 10.5802/aif.2311. The finite and infinite
Li-test identities described below are now LeanChecked for Riemann xi.

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

`RHGarden.LiWeilInfinite` defines the occurrence-indexed scalar as an ordinary
`tsum`, proves its absolute convergence, and specializes both (3.3) and (3.4).
The garden node is named `WeilLiQuadraticValues` to distinguish this Li-test
diagonal from the future full Weil form.

## Lean-checked finite and infinite layers

`formal/RHGarden/WeilFinite.lean` now checks (3.5), (3.6), and the exact
finite-Multiset analogue of (3.3). `Multiset` is essential: a cutoff retains
zero multiplicities. For a reflection-stable valid cutoff it also checks the
diagonal identity with `2*Re`.

`formal/RHGarden/LiStarIdentification.lean` identifies both signed height-star
limits with the derivative-defined classical Li coefficient. Then
`formal/RHGarden/LiWeilInfinite.lean` proves `G_n(rho)=O(1/|rho|)`, absolute
summability of each product pair, exhaustion of the ordinary `tsum` by the
same height cutoffs, and the infinite identity

```text
weilLiScalar n m
  = classicalLiSigned n
  + classicalLiSigned (-m)
  - classicalLiSigned (n-m).
```

Its diagonal consequence is LeanChecked:

```text
weilLiQuadraticValue k = 2 * classicalLiRealCoefficient k.
```

Ordinary `tsum` is therefore not used as a common encoding for both limits.
The notation `||G_n||_W^2` also carries no unconditional positivity claim:
`WeilLiPositive` remains open, although Lean checks its equivalence with
`LiPositive`. Positive semidefiniteness of the full Weil form on all of `A` is
the separate future criterion `WeilFormPSD`.

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
is introduced. The pinned local zero-count theorem and subsequent Hadamard
identification now prove its limit for every integer index.

The normalization boundary is recorded faithfully: the derivative coefficient
at zero-based index `k` first targets the negative star index `-(k+1)` through
the LeanChecked theorem `classicalLiEqualsNegativeStar`; the positive-index
version is `classicalLiEqualsPositiveStar`.

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

## Current frontier

The full occurrence-indexed genus-one product, normalized affine factor,
exact logarithmic derivative, classical/star identification, and infinite
Li-test Weil identities are all LeanChecked. The remaining problem is no
longer representation or convergence: it is to prove nonnegativity.

The immediate open proposition may be stated either as `LiPositive` or as
`WeilLiPositive`; `RHGarden.liPositive_iff_weilLiPositive` proves these are
equivalent. This does not prove either one. Extending the construction from
the Li test family to Lagarias's whole space `A` and proving `WeilFormPSD`
remains a larger, distinct formalization frontier.
