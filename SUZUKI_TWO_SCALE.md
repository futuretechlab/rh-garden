# Anchored-integral calibration and two-scale transfer

Future Technologies Laboratory LLC — September 2026.

NO PROOF OF RH IS CLAIMED.

Later continuation: [SUZUKI_RECOVERY.md](SUZUKI_RECOVERY.md) proves qualitative
finite recovery of the actual discrepancy. It does not change the arithmetic
estimates, finite failures, or unfinished numerical endpoint reported here.

Baseline: `c95f07025015b334948b52eadb31be2f07786de8`. The checkout, not an
earlier archive, supplied the definitions. Lean, mathlib and Zeta23 pins
are unchanged. The surcharge branch, certified obstruction at 31, and
proved prefix through `log 37` are reused without extension.

## Exact normalization and information boundary

Write `E_m(y)=psi(y)-psi(m)-(y-m)`, and

```text
w_m,h(t) = (m+t)^(-3/2) * (1 + log((m+h)/(m+t))/2),
I_m(x)   = integral[m,x] E_m(y) * (1+log(x/y)/2)/y^(3/2) dy,
C_m(x)   = 4(sqrt(x)-sqrt(m)) - 2 sqrt(m) log(x/m),
T_m(x)   = C_m(x)/100 + log(x)/sqrt(m)*log(x/m).
```

The existing `anchoredIntegral_eq_logArrival_sub_main` and
`suzukiPsiRoot_eq_signed_anchoredIntegral` are unchanged. They apply at
arbitrary real finite endpoints, without an excursion or recovery premise:

```text
I_m(x) = sum_{m<q<=x} Lambda(q)/sqrt(q)*log(x/q) - C_m(x),
V(sqrt(x)) = V(sqrt(m)) + D(sqrt(m))*log(x/m) - Adef_m(x) - I_m(x).
```

The anchor is excluded and a terminal arrival has zero logarithmic weight.
The signed initial `D`, including a positive surplus, is retained.

The proposed upper target uses only `m,x`. The finite *lower* witnesses
below deliberately use explicit prime data. Those data are not inputs to
either the conditional transfer theorem or the unconditional global-PNT
corollary. No coefficients or thresholds were retuned to suppress failures.

## Corrected finite calibration

The recovery endpoints passing this target do not imply that eligible
earlier prefixes pass. The two permanent regression cases are:

| m | x | h | I (floating point) | T (floating point) | I-T |
|---:|---:|---:|---:|---:|---:|
| 324431 | 339360 | 14929 | 0.0121801702812715 | 0.00681348105419782 | 0.00536668922707367 |
| 8573249 | 8620438 | 47189 | 0.000644139043357576 | 0.000471453542709247 | 0.000172685500648330 |

Both exact integer conditions `h^3>=m^2` and `8h<=m` are proved by
`onePercent_witness1_eligible` and `onePercent_witness2_eligible`.

Both finite witnesses are kernel checked. The principal statements exported
by `SuzukiOnePercentFailures.lean` are

```text
onePercent_failure_324431:
  53/10000 < I_324431(339360) - T_324431(339360).
onePercent_failure_8573249:
  17/100000 < I_8573249(8620438) - T_8573249(8620438).
onePercent_failure1_even_without_proper_powers:
  47/10000 < sum_{324431<p<=339360, p prime}
                 Lambda(p)/sqrt(p)*log(339360/p) - C - T.
```

The generator `scripts/suzuki-one-percent-witness.mjs` proposes exact
integer/rational data, not a proof oracle. Its 1186 and 2986 prime rows
are checked with `norm_num`; order and integer totals also use ordinary
Lean proof terms, never `native_decide`. Every row certifies primality, interval
membership, a rational square-root upper bound, and a rational weight
lower bound. A two-term atanh lower polynomial bounds log ratios.
Existing rigorous log scaling and square-root lemmas enclose endpoints.
The source is split into bounded, cacheable files to control elaboration
memory. The checker does not rely on the generator being correct.

The prime lower sums are `592287163908/10^12` and `44795673551/10^12`.
For the first witness, separately checked arrivals `571^2=326041` and
`577^2=332929` contribute at least `44/100000` and `20/100000`.
Every omitted arrival is nonnegative. No completeness assertion about
the table, or composite classification across the interval, is required.
The second interval's absence of proper powers is also checked in the
numerical regression; the Lean lower proof does not need that fact.

These failures do not disprove an eventual theorem with some larger M.
They are not counterexamples to Suzuki positivity or RH.

## Kernel-checked finite two-scale transfer

For natural `m>=1`, real `0<H<=h`, and `epsilon>=0`, assume only

```text
forall t in [H,h], psi(m+t)-psi(m) <= (1+epsilon)*t.     (SI)
```

`anchoredError_le_twoScale` uses monotonicity at H to prove, for all
`0<=t<=h`,

```text
E_m(m+t) <= epsilon*t + (1+epsilon)*max(H-t,0).
```

No short-prefix slope estimate is assumed. The kernel is nonnegative
and decreasing; its continuity and interval integrability are proved,
not certificate fields. `integral_shiftedIntegratedKernel_moment` proves
`integral[0,h] t*w(t) dt=C_m(m+h)`. Integrating the triangular allowance
and bounding its kernel by `w(0)` gives

```text
anchoredIntegral_le_twoScale_explicit:
I_m(m+h) <= epsilon*C_m(m+h)
  + (1+epsilon)*H^2/(2*m^(3/2))*(1+log(1+h/m)/2).

integratedMainTerm_lower_rpow:
C_m(m+h) >= h^2/(2*(m+h)^(3/2)).
```

For `0<h<=m/8`, `anchoredIntegral_div_main_le_twoScale` proves

```text
I_m(m+h)/C_m(m+h) <= epsilon + (3/2)*(1+epsilon)*(H/h)^2.
```

The rational geometry uses `1377/1024<3/2`. At `epsilon=1/200` and
`H/h<=1/20`, `anchoredIntegral_le_onePercent_of_twoScale` proves
`I<=1403/160000*C`; the coefficient is strictly less than `1/100`.
`threeFifths_twoThirds_scale` proves that `m>=20^15` and `h>=m^(2/3)`
imply `m^(3/5)/h<=1/20`. This is only a geometric threshold.

`anchoredIntegral_lt_onePercent_of_shortInterval` combines these results
with an explicit premise (SI) for every `t in [m^(3/5),m/8]`. It is a
conditional transfer lemma, NOT a proved short-interval arithmetic bound.
It bounds the contribution of widths below H to a longer endpoint
integral; it does not certify endpoints of width below H.

## What is missing from the short-interval arithmetic input

The exact missing dependency is

```text
exists M_PNT, forall natural m>=M_PNT,
  forall real t in [m^(3/5),m/8],
    psi(m+t)-psi(m) <= (201/200)*t.
```

For an *effective* result, M_PNT must be displayed with a verified bound.
The unchanged pinned `MediumPNT` is global. Searches of the pinned
Zeta23 and Mathlib number-theory declarations found no sufficient
short-interval PNT or zero-density input. Subtracting two global `o(m)`
errors does not give `o(t)` at `t=m^(3/5)`. No axiom or dependency upgrade
fills this gap.

[Guth–Maynard, arXiv:2405.20552v2](https://arxiv.org/html/2405.20552v2),
Corollary 1.3, supplies an external all-interval prime-count asymptotic
for `x^(17/30+epsilon)<=y<=x^0.99`. The paper also records Huxley's older
`7/12` exponent, already sufficient for the present `3/5` scale. Its
Corollary 1.4 is an almost-all result and is not the needed substitute.
Section 13.2 works directly with Mangoldt sums and a truncated zero sum,
so it is preferable to importing a pi estimate without accounting for
log weights and proper prime powers. These are external mathematical
inputs, not Lean declarations in this repository. Their hidden error
constants do not provide an explicit M_PNT.

The adaptation still needs uniformity in real base and terminal points.
A closed lower endpoint in a Mangoldt sum only adds a nonnegative term,
so an upper bound transfers to the required open-left interval. The
`x^0.99` upper restriction cannot simply be dropped.

The finite range extension is now proved:
`increment_le_of_block_range` says that if every translated block inside
`[a,a+h]` of length in `[H,2H]` has increment at most `c*t`, then so does
the whole interval, for `h>=H>0`. It takes `k=floor(h/H)` equal pieces and
proves the length and telescoping bounds. The power adaptation is also
proved: `threeFifths_blocks_fit_point99` gives
`2*(a+h)^(3/5)<=a^(99/100)` for `a>=64`, `0<=h<=a/8`.
`increment_le_from_threeFifths_to_point99` then extends a source bound
valid at every real anchor y in `[a,a+h]` and every
`y^(3/5)<=t<=y^(99/100)` to the full range `a^(3/5)<=h<=a/8`.
It uses the original bound directly when h is below `a^0.99`, and
subdivision with `H=(a+h)^(3/5)` otherwise. The number 64 is another
geometric overlap threshold, not an arithmetic one. The source arithmetic
theorem remains absent; no unconditional short-interval theorem is
claimed. Prime existence alone is insufficient, and no RH-conditional
estimate is used.

The smallest useful analytic-number-theory development is the one-sided,
all-real-interval Mangoldt bound on `[x^(3/5),x^0.99]`, with controlled
error in a truncated explicit formula. The pinned global PNT does not
contain the needed local zero-density control. Formalizing an effective
version additionally requires explicit constants and a verified cutoff;
formalizing only an existential literature asymptotic would not complete
the explicit-M target.

## Unconditional uniform range from the pinned global PNT

This branch is kernel checked and has no new arithmetic premise.
First, the finite theorem `anchoredIntegral_le_global_relative` assumes

```text
|psi(y)-y| <= delta*y for all y in [m,m+h], delta>=0,
m>=1, rho>0, rho*m<=h<=m/8.
```

It proves

```text
I_m(m+h) <= delta*(1+6/rho)*C_m(m+h).
```

Both endpoint errors remain: `E_m(m+t)<=delta*(2m+t)`. The existing
accuracy-budget lemma integrates that bound. A proved comparison
`C>=h^2/(3*m*sqrt(m))` and `log(1+h/m)<=h/m` give the displayed constant.
This global-error use is justified only in this fixed-relative regime;
it is not substituted for the sharper anchored short-interval problem.

`eventually_psi_relative_bound` reuses `tendsto_psi_relative_error`, the
already proved adapter from the pinned unconditional `MediumPNT`.
With `delta=eta/(1+6/rho)`, it gives

```text
anchoredIntegral_eventually_le_relative_main:
forall fixed real 0<rho<=1/8 and eta>0,
exists natural M, forall natural m>=M,
forall real h with rho*m<=h<=m/8,
  I_m(m+h) <= eta*C_m(m+h).
```

Uniformity is proved by choosing one global real threshold before h:
every point of every permitted window is beyond that threshold. No
pointwise limits are interchanged. M is non-effective, and rho is fixed.
This does NOT yield the moving relative scale `h=m^(2/3)`.

## Reserve, coverage, and numerical diagnostics

The required reserve comparison is still with
`V(sqrt(m))+D(sqrt(m))*log(x/m)-Adef_m(x)`, not with C.
`integratedMainTerm_fixed_ratio` proves

```text
C_m(m+r*m) = sqrt(m)*(4*(sqrt(1+r)-1)-2*log(1+r)).
```

For fixed r>0 the coefficient is positive by the proved C lower bound.
Thus even a one-percent charge grows as sqrt(m); it is not automatically
small compared with the true reserve.

All numbers in this table are exploratory IEEE-754 diagnostics, not
certified reserve enclosures:

| anchor / terminal x | true I | target T | signed budget | endpoint reserve |
|---|---:|---:|---:|---:|
| 324431 / 339360 | .0121801702813 | .0068134810542 | .0668023110708 | .0546221407896 |
| 8573249 / 8620438 | .0006441390434 | .0004714535427 | .0485337760814 | .0478896370380 |
| 324431 / recovery 361197.6403415228 | .0303121956215 | .0358283604397 | .0661298116476 | .0358176160261 |
| 8573249 / recovery 8906232.48818665 | .0079407872435 | .0216006047422 | .0484393953510 | .0404986081075 |

The recovery coordinates are real squared roots, distinct from the old
next-event labels 361201 and 8906237. The report also retains m=31,
the cutoff-straddling anchor 324432, the unfinished window ending at
19,999,999, zero width, one-integer, and sub-integer tests. At m=31's
recovery the target exceeds the available budget despite being an upper
bound numerically; this illustrates the separate reserve obligation.

`suzuki-sieve-regression.mjs` records I, T, arithmetic-target gap, signed
budget, reserve deficit, and the first failing *tested eligible prefix*.
The grid and the two exact witness endpoints are not an all-prefix cover.
For example, the recovery-window grid first fails at
`330175.78755336296` for anchor 324431; this is a tested-grid observation,
not an isolated earliest real failure. The explicit second witness is
included in the recovery-window test grid for anchor 8573249.
The full-origin validation sieve is separate from the sample-independent
candidate path. Floating-point residuals are regression checks only;
`numerical_enclosure_error` remains null. The separate exact-integer
generator's intervals become proof evidence only after Lean checks the
generated certificate statements.

The established event regression has actual cutoff 9,999,993 and
10,341 periods: 7,872 old-affine passes and 2,469 failures. Neither a
completed-period scan nor the new PNT corollary proves eventual recovery,
coverage of an unfinished excursion, safety at short prefixes, or safe
reanchoring at arbitrary cutoffs. The true tail reserve bound remains open.

## Validation and handoff

Principal audit: `lake env lean AuditSuzukiTwoScale.lean`.
The full pinned `lake build` passes (3950 jobs). All 25 audit entries,
including both strict failures and the unconditional uniform theorem,
report exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`.
These are standard foundational axioms, not new project assumptions.
Cabal build/tests, UI typecheck/build, formal-status/garden/kernel/submission,
the established event regression, event report, surcharge-profile regression,
updated sieve regression, and both generated-data reproducibility checks pass.
The old surcharge test is rerun, not extended. No project-added axioms, sorry/admit,
numerical oracles, unsafe shortcuts, or hidden RH assumptions are used.
Static formal-status entries and exporter JSON remain navigation and
numerical data, not additional proof evidence.

The established handoff is a source commit followed by
`cabal run rh-garden -- ui-export`, validation of all four versioned JSON
files, a separate source-snapshot commit, and push. The exporter intentionally
leaves its build/test fields `not_checked_by_export`; it does not convert
the command results above into a proof oracle. Its ten-million frontier
cutoff is distinct from the rounded-t regression cutoff 9,999,993.

Next independent arithmetic target: prove the all-real-anchor, one-sided
Mangoldt increment bound above (initially on `[x^(3/5),x^0.99]`), tracking
the constants if effectiveness is claimed. The finite transfer is ready;
neither a conditional wrapper nor an increased guessed M supplies that
arithmetic theorem. Its eventual success would still leave the correctly
weighted, signed Suzuki reserve and all-prefix coverage problem.
