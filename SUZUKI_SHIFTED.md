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
No local positivity theorem is claimed here.

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
nonnegative parameter. The semigroup endpoints (one shift parameter equal to
zero) are also checked. The general composition law is isolated as
`SuzukiShiftSemigroup`; proving it requires a new triangular two-variable
Fubini calculation for nested Volterra integrals.

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

Suzuki equation (11.2) and Theorem 11.1 predict

```text
XiZeroFreeRightOf omega
  <-> suzukiPsiShifted omega is eventually nonnegative.
```

The corresponding propositions `SuzukiShiftedTransformFormula` and
`SuzukiShiftedEventualCriterion` are now stated exactly, but not proved. The
first missing analytic step is the Fubini evaluation of the one-sided
Laplace transform of both Volterra terms; after that, the already formalized
Landau machinery must be adapted to ignore a compact initial interval.

Thus `omega=1/2` is LeanChecked safe on the xi-zero side, but eventual or
global shifted positivity at `omega=1/2` is not promoted to LeanChecked.

## Trust boundary and next frontier

- LeanChecked: zero-side = prime-side (Suzuki (1.1)), the triangular-test
  smoothing and complete Gamma evaluation, the finite cutoff and prime-free
  interval, shifted-family definitions/basic analysis, zero-free half-plane
  geometry, and the RH/zero-membership bookkeeping equivalence.
- LiteratureCertified: the shifted zero-free/eventual-positivity criterion
  (Suzuki Theorem 11.1).
- OpenFormalization: the full Volterra semigroup, shifted transform (11.2),
  and shifted Landau continuation.
- Open mathematics: membership of `0` in the positivity set, equivalently RH.

The next formal frontier is a generic Fubini theorem for the Volterra shift,
which should deliver both the semigroup and transform identities. The new
prime-side identity also opens symbolic or interval-certified investigations
of positivity between successive prime thresholds.
