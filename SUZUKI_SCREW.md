# Suzuki zero-side screw representation

This district formalizes the zero-side part of Suzuki's screw-function
framework directly from RH Garden's occurrence-indexed xi divisor. It does not
use a prime explicit formula and it does not prove RH.

## Spectral coordinate

For `a : XiZeroOccurrence`, with zero value `rho = a.value`, define

```text
xiSpectralParameter a = i * (rho - 1/2).
```

Lean checks

```text
rho = 1/2 - i * xiSpectralParameter a,
Re gamma = -Im rho,
Im gamma = Re rho - 1/2,
XiTZerosReal <-> forall a, Im gamma_a = 0.
```

The critical-strip inequalities give `|Im gamma_a| <= 1/2`. The triangle
inequality gives `|rho|/2 <= |gamma|` once `|rho| >= 1`; hence the existing
occurrence reciprocal-square theorem implies

```text
Summable (fun a => 1 / |gamma_a|^2).
```

## Zero-side function and kernel

The complex zero-side series is

```text
Psi_0(t) = sum_a (1-exp(i*gamma_a*t))/gamma_a^2.
```

For fixed real `t`, `|exp(i gamma_a t)| <= exp(|t|/2)`, so the preceding
reciprocal-square majorant proves absolute summability. Conjugation of zeros
and reflection `rho -> 1-rho` prove that `Psi_0` is real-valued and even. The
real function `Psi`, screw function `g=-Psi`, and its translation-difference
kernel are then defined from this series.

Pure absolutely convergent `tsum` algebra proves Suzuki's zero-side identity

```text
G_g(t,u) = sum_a
  ((exp(i*gamma_a*t)-1) * (exp(-i*gamma_a*u)-1))/gamma_a^2.
```

Height truncations through the genuine multiplicity-preserving xi cutoff
converge to this ordinary sum.

## Where critical-line reality enters

Under `XiTZerosReal`, each spectral parameter is fixed by conjugation. With

```text
v_a(t) = (exp(i*gamma_a*t)-1)/gamma_a,
```

the kernel term becomes `v_a(t) * conjugate(v_a(u))`. Lean checks the infinite
Gram identity, every finite-height Gram matrix is positive semidefinite, and
the limiting kernel is positive semidefinite for every finite set of sample
points and coefficients.

## The xi Nevanlinna function

`RHGarden.XiNevanlinna` defines

```text
Q_xi(z) = i * logDeriv xi (1/2-i*z)
```

and the project predicate `XiNevanlinna`: `Q_xi` is analytic on the upper
half-plane and has nonnegative imaginary part there.  Centering the exact
genus-one partial fraction at `1/2` gives the absolutely convergent identity

```text
Q_xi(z) = sum_a (1/(gamma_a-z) - 1/gamma_a).
```

Lean proves both directions

```text
XiTZerosReal <-> XiNevanlinna.
```

The forward direction takes imaginary parts of the corrected spectral sum.
For the reverse direction, upper-half-plane analyticity is incompatible with
the logarithmic-derivative pole at a spectral zero.  The proof uses Mathlib's
analytic-order factorization and therefore handles arbitrary multiplicity;
reflection `gamma -> -gamma` then excludes the lower half-plane.

## Continuity, screw axioms, and the transform

The zero series is normally summable on compact real intervals.  Consequently
`Psi_0`, `Psi`, and `riemannScrew` are continuous.  With `IsScrewFunction`
defined by continuity, normalization, Hermitian symmetry, and finite-matrix
kernel PSD, Lean proves

```text
IsScrewFunction riemannScrew <-> KernelPSD riemannScrewKernel.
```

For `Im z > 1/2`, absolute domination permits termwise integration and Lean
checks

```text
integral_0^infinity g(t) * exp(i*z*t) dt
  = (i/z^2) * Q_xi(-z).
```

The argument `-z` is forced by the conventions used here:
`gamma=i*(rho-1/2)`, `rho=1/2-i*gamma`, and the transform kernel is
`exp(+i*z*t)`, so its exponent combines as `gamma+z`.  A formula using
`Q_xi(z)` instead requires reversing either the spectral coordinate or the
Fourier sign.

Suzuki's 2023 Theorem 1.2 and equations (1.2), (1.6), (1.7), and (1.8) provide
the literature context.  The final historical implication from the screw
property to the Nevanlinna property uses Krein--Langer theory.

The pinned Mathlib revision has upper-half-plane types, complex Poisson
formulas, matrix positivity, and Riesz--Markov infrastructure, but no
Krein--Langer theorem, Bochner representation for this increment kernel, or
specialized screw-to-Nevanlinna bridge.

## Sampled positivity and integral quadratic forms

`RHGarden.KernelIntegral` now connects the two presentations of kernel
positivity used in the screw-function literature. For any jointly continuous
complex kernel, Lean checks

```text
KernelPSD K -> IntegralKernelPSD K,
```

where the right side asserts nonnegativity of the double Lebesgue integral on
every symmetric compact interval against every continuous test function.
The proof approximates the identity map of the interval by finite-range
simple functions. Their measurable fibers supply nonnegative quadrature
weights, `KernelPSD.weighted_sum_nonneg` supplies positivity of every finite
approximant, and dominated convergence on the compact rectangle passes it to
the integral.

For the Riemann screw kernel, Lean also checks joint continuity, positivity of
the whole-line Hermitian form for continuous tests with bounded support, and
the zero-mean cancellation

```text
integral integral K(t,u) phi(t) conjugate(phi(u))
  = integral integral g(t-u) phi(t) conjugate(phi(u)).
```

A concrete continuous compact cutoff and its truncated exponential test are
defined, and their Hermitian forms are LeanChecked nonnegative under sampled
kernel PSD. What is not yet checked is the limiting computation identifying
these two-variable quadratic values with `Im Q_xi`. A zero-mean correction
introduces cross terms, and the existing one-sided Fourier--Laplace transform
does not by itself evaluate that convolutional quadratic limit. This is now
the first precise Krein--Langer obstruction; no high-strip sign theorem is
claimed.

RH Garden therefore still isolates exactly

```text
ScrewToNevanlinnaBridge :=
  KernelPSD riemannScrewKernel -> XiNevanlinna
```

as literature-certified/open formalization.  It is not an axiom and is not
used to produce a Lean theorem.

## Midpoint and literal denominators

`RHGarden.XiMidpoint` proves the classical fact

```text
XiMidpointNonzero := riemannXi (1/2) != 0.
```

The proof uses the pinned `N=1` Euler--Maclaurin representation

```text
zeta(1/2) = -3/2 + J/2,    |J| <= 2.
```

It follows that `Re zeta(1/2) < 0`; therefore zeta and xi do not vanish at the
midpoint. Together with the coordinate algebra, Lean proves

```text
gamma_a != 0 <-> rho_a != 1/2,
gamma_a != 0.
```

Thus every spectral denominator in the displayed Suzuki formulas is
unconditionally and literally nonzero. No RH or zero-counting hypothesis is
used.

The next frontier is the truncated zero-mean exponential limit: construct a
normalized compact bump, evaluate the resulting convolutional Hermitian form,
and prove that its limit has the sign-correct expression in
`xiNevanlinnaQ`. The sampled-to-integral extension itself is now LeanChecked.
No Nevanlinna positivity statement or RH is proved.
