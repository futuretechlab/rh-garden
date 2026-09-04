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

The argument `-z` is forced by the raw spectral conventions used here:
`gamma=i*(rho-1/2)`, `rho=1/2-i*gamma`, and the transform kernel is
`exp(+i*z*t)`, so its exponent combines as `gamma+z`.  A formula using
`Q_xi(z)` follows from the newly LeanChecked global oddness identity

```text
Q_xi(-z) = -Q_xi(z).
```

Thus Lean now also checks the normalized Suzuki formulas

```text
integral_0^infinity g(t) exp(i*z*t) dt = -(i/z^2) Q_xi(z),
integral_0^infinity Psi(t) exp(i*z*t) dt = (i/z^2) Q_xi(z).
```

Suzuki's 2023 Theorem 1.2 and equations (1.2), (1.6), (1.7), and (1.8) provide
the literature context.  The final historical implication from the screw
property to the Nevanlinna property uses Krein--Langer theory.

The pinned Mathlib revision has upper-half-plane types, complex Poisson
formulas, matrix positivity, and Riesz--Markov infrastructure, but no
Krein--Langer theorem, Bochner representation for this increment kernel, or
specialized screw-to-Nevanlinna bridge. It also contains no Landau boundary
theorem for one-sided Laplace transforms of nonnegative continuous
functions.

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
kernel PSD. The two-variable limiting computation identifying those values
with `Im Q_xi` remains unchecked, but it is no longer the preferred route:
the pointwise diagonal and Landau argument below isolate a smaller
specialized obstruction. No high-strip sign theorem is claimed.

## Pointwise positivity and the Landau route

Suzuki 2023, Theorem 1.7 gives the shorter specialized criterion

```text
RH <-> forall t : real, 0 <= Psi(t).
```

RH Garden now defines `SuzukiPsiNonnegative` and Lean checks the diagonal
identity and its immediate consequence

```text
riemannScrewKernel(t,t) = 2 * Psi(t),
KernelPSD riemannScrewKernel -> SuzukiPsiNonnegative.
```

With the right-half-plane parameter `z=i*w`, Lean defines
`suzukiPsiLaplace` and its explicit xi continuation and proves, for
`Re w>1/2`,

```text
Laplace(Psi)(w) = -(i/w^2) Q_xi(i*w).
```

The continuation is LeanChecked meromorphic, and it is LeanChecked analytic
at every positive real `w`. The latter uses a new uniform real-axis result:
the pinned `N=1` Euler--Maclaurin bound proves `Re zeta(s)<0` for every real
`1/2<s<1`; the standard zero-free theorem handles `s>=1`, with `xi(1) != 0`
handled separately. Consequently `xi(1/2+w) != 0` for all real `w>=0`.

The elementary Laplace infrastructure is also checked: convergence is upward
closed in the real parameter, complex parameters have the decay of their
real parts, and convergence at `sigma` gives integrability of the first
exponential moment at every `tau>sigma`.

The exact remaining theorem is now isolated as

```text
NonnegativeLaplaceBoundaryPrinciple
```

in `RHGarden.SuzukiPointwise`. It is the specialized Landau statement that a
nonnegative continuous Laplace transform with a meromorphic continuation
regular on the positive real axis cannot have a positive abscissa of
convergence. The first missing formal step beyond the checked first-moment
bound is an all-orders differentiation/Taylor theorem identifying the Taylor
coefficients with nonnegative moment integrals, followed by a Tonelli passage
through the exponential power series. Mathlib has general dominated
differentiation and monotone convergence, but no theorem assembling this
Landau argument.

RH Garden therefore still isolates

```text
ScrewToNevanlinnaBridge :=
  KernelPSD riemannScrewKernel -> XiNevanlinna
```

as literature-certified/open formalization. The preferred specialized path
is now `KernelPSD -> Psi>=0 -> Landau -> XiTZerosReal -> XiNevanlinna`, not the
two-variable truncated-convolution limit. Neither open proposition is
assumed or used to produce an unconditional Lean theorem.

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

The next frontier is `NonnegativeLaplaceBoundaryPrinciple`: formalize the
all-order Laplace moment derivative formula, identify the analytic Taylor
coefficients at a putative positive convergence boundary, and use Tonelli on
the nonnegative exponential series to force convergence to the left of that
boundary. No Nevanlinna positivity statement or RH is proved.
