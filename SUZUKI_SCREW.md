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

The converse implication is not formalized. It needs the global analytic
machinery in Suzuki's criterion and is kept literature-certified.

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

The next large frontier is Suzuki's PSD converse.
