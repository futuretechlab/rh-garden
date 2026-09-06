# Suzuki prime-side and shifted representations

This district exposes two arithmetic/one-parameter representations of the
already LeanChecked zero-side function `suzukiPsi`. It does not prove a
positivity statement or the Riemann hypothesis.

## Prime-side formula

Suzuki (2023), equation (1.1), writes for `t >= 0`

```text
Psi(t) = 4 (exp(t/2) + exp(-t/2) - 2)
  - sum_{n <= exp(t)} Lambda(n)/sqrt(n) * (t - log n)
  + t/2 * (digamma(1/4) - log pi)
  + 1/4 * (pi^2 + 8 Catalan
      - exp(-t/2) Phi(exp(-2t), 2, 1/4)).
```

`RHGarden.SuzukiShifted` defines the required Catalan and real Lerch series,
the archimedean expression, the finite `Finset.Ioc` von Mangoldt sum, and its
even extension. The arithmetic sum is LeanChecked nonnegative. It is also
LeanChecked to vanish when `0 <= t < log 2`, so the defined prime-side
expression is purely archimedean on that interval.

The equality of the existing zero-side series with this prime-side expression
is **LeanChecked** as `suzukiPsi_eq_primeSide`. The proof starts from the pinned
Zeta23 theorem `Zeta23.WeilEF.EF_lit_zetaZeroConfig`, whose tests are compactly
supported and `C^2`. It convolves the triangular test
`u |-> max (t-|u|) 0` with normalized smooth bumps, proves uniform support and
Lipschitz control, and passes the zero, finite-prime, pole, and Gamma-bracket
terms to the limit. The final Gamma integral is evaluated from Zeta23's
vertical digamma series, a Cauchy-kernel Fourier integral, the Basel sum, the
series definition of Catalan's constant, and the real Lerch series. Thus the
prime-free identity `suzukiPsi_eq_archimedean_of_lt_log_two` is unconditional.

`RHGarden.SuzukiLocalPositive` now differentiates this exact archimedean
formula on `0 < t < log 2`. In the normalization of the checked formula the
derivative is

```text
2 (exp(t/2)-exp(-t/2))
  + [((Re digamma(1/4)-log pi)/2) + pi/2]
  - arctan(exp(t/2)) + artanh(exp(-t/2)).
```

The last term tends to `+infinity` as `t -> 0+`, while the other terms form a
continuous, locally bounded function. Lean therefore checks
`exists_suzukiPsi_pos_near_zero`: there is a symbolic `delta>0` for which
`Psi(t)>0` whenever `0<t<delta`. This is a genuine unconditional local
positivity theorem, not the open global statement `SuzukiPsiNonnegative`.

## Shifted family

Suzuki equation (11.1) is implemented literally, with `x=|t|`:

```text
SuzukiShift omega f t =
  exp(-omega*x) f(x)
  + 2 omega integral_0^x exp(-omega*u) f(u) du
  + omega^2 integral_0^x (x-u) exp(-omega*u) f(u) du.

suzukiPsiShifted omega = SuzukiShift omega suzukiPsi.
```

Lean checks zero parameter, value at zero, evenness, continuity, and the fact
that a nonnegative function remains nonnegative after a shift by a
nonnegative parameter. It now also checks the full semigroup law

```text
SuzukiShift eta (SuzukiShift omega f)
  = SuzukiShift (omega + eta) f.
```

The proof in `RHGarden.SuzukiShiftTransform` writes the positive-half-line
operator as `(I + omega J)^2 M_omega`. The fundamental theorem of calculus
gives the resolvent identity commuting `J` past the exponential weight; this
avoids expanding the entire nested Volterra expression. Consequently global
positivity at one parameter propagates to every larger parameter, and
`SuzukiShiftedPositivitySet` is LeanChecked upward closed.

The global and eventual positivity parameter sets are defined. Lean checks

```text
0 in SuzukiShiftedPositivitySet <-> SuzukiPsiNonnegative
RiemannHypothesis <-> 0 in SuzukiShiftedPositivitySet.
```

These are equivalences of open propositions; membership at zero is not
asserted.

## Zero-free half-planes

`XiZeroFreeRightOf omega` means every xi zero has
`Re rho <= 1/2 + omega`. Lean checks monotonicity, the unconditional safe
parameter `omega=1/2` from the critical strip, and

```text
RiemannHypothesis <-> XiZeroFreeRightOf 0.
```

The same module proves the two generic Volterra transforms and hence the exact
multiplier

```text
F_+(SuzukiShift omega f)(z)
  = ((z + i omega)^2 / z^2) F_+(f)(z + i omega).
```

Applying this to `suzukiPsi` cancels the shifted square and proves Suzuki
equation (11.2):

```text
integral_0^infinity Psi_omega(t) exp(i z t) dt
  = -(1/z^2) logDeriv xi(1/2 + omega - i z).
```

The project theorem states `0 < Im z` explicitly, which is the natural domain
of the separate Volterra transforms; for the primary Suzuki range
`omega <= 1/2`, the strip condition `1/2-omega < Im z` implies it.

Suzuki Theorem 11.1 predicts

```text
XiZeroFreeRightOf omega
  <-> suzukiPsiShifted omega is eventually nonnegative.
```

`RHGarden.SuzukiShiftedLandau` now LeanChecks the reverse direction. Given an
eventual sign threshold `T`, it translates the nonnegative tail to `[0,∞)`,
splits off the compact initial transform, and proves that this compact term is
entire. The existing nonnegative Landau boundary theorem therefore applies to
the translated tail. Meromorphic uniqueness on `Re w>0` and the genuine pole
of `xi'/xi` at every xi zero give

```text
SuzukiPsiShiftedEventuallyNonnegative omega
  -> XiZeroFreeRightOf omega.
```

Equivalently, the eventual-positivity parameter set is LeanChecked contained
in the zero-free parameter set. This is one complete direction of Suzuki
Theorem 11.1.

`RHGarden.SuzukiShiftedNevanlinna` now decomposes the forward direction. It
defines

```text
Q_omega(z) = i * logDeriv xi(1/2 + omega - i*z)
           = Q_xi(z+i*omega).
```

The exact shifted partial fraction is LeanChecked. Zero-freeness puts every
shifted spectral parameter `gamma-i*omega` on or below the real axis.
Pairing `gamma` with `-gamma` cancels the sign-indefinite genus-one
correction `-1/gamma`; the two remaining Cauchy kernels have nonnegative
imaginary part in the upper half-plane. Conversely, upper-half-plane
analyticity excludes a shifted spectral zero by the existing genuine-pole
theorem for `xi'/xi`. Hence Lean checks

```text
XiZeroFreeRightOf omega <-> XiShiftedNevanlinna omega.
```

Equation (11.2) is also normalized as

```text
integral_0^infinity Psi_omega(t) exp(i*z*t) dt
  = (i/z^2) Q_omega(z).
```

The remaining forward subedge is exactly the Herglotz-to-screw inversion

```text
XiShiftedNevanlinna omega
  -> forall t, 0 <= Psi_omega(t).
```

Suzuki obtains this stronger global statement from the classical
Nevanlinna/screw correspondence. Pinned Mathlib provides local
Herglotz--Riesz/Poisson formulas but no upper-half-plane Herglotz
representation or inverse screw-transform theorem. RH Garden therefore
isolates this theorem as `ShiftedNevanlinnaToPsiNonnegative`; its conditional
composition with the checked results discharges the full criterion.

Thus `omega=1/2` is LeanChecked safe on the xi-zero side, but eventual or
global shifted positivity at `omega=1/2` is not promoted to LeanChecked: that
would use precisely the still-open forward implication.

## Trust boundary and next frontier

- LeanChecked: zero-side = prime-side (Suzuki (1.1)), the triangular-test
  smoothing and complete Gamma evaluation, the finite cutoff and prime-free
  interval, strict positivity on some punctured neighborhood of zero,
  shifted-family definitions/basic analysis, the Volterra semigroup and
  transform equation (11.2), rightward positivity propagation, compact-tail
  Landau theory, eventual positivity implies a zero-free half-plane, and
  `XiZeroFreeRightOf omega <-> XiShiftedNevanlinna omega`.
- LiteratureCertified/OpenFormalization: only the shifted
  Nevanlinna-to-screw inversion `ShiftedNevanlinnaToPsiNonnegative`.
- Open mathematics: membership of `0` in the positivity set, equivalently RH.

Positivity through the whole interval `(0, log 2]` has not been established;
neither has the first-prime interval `[log 2, log 3)`. The next formal frontier
is the remaining Herglotz-to-screw subedge of Suzuki Theorem 11.1. The
prime-side identity also
opens symbolic or interval-certified investigations of positivity between
successive prime thresholds.
