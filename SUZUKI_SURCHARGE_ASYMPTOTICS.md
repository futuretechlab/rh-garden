# Suzuki surcharge: finite estimates and uniform profiles

Future Technologies Laboratory LLC — September 2026.

**NO PROOF OF RH IS CLAIMED.** This closes the surcharge-asymptotic branch,
not the correctly weighted Suzuki tail-positivity problem.

## Baseline and scope

Actual starting commit: `b786da02e14c3cf43ba81a80e046dac94ca6829d`.
The checkout matched the report; only the pre-existing `.codex/` directory
was untracked. It was preserved. No dependency pins were changed:

- Lean `v4.33.0-rc2`;
- mathlib `51e6992efd06126df61a496bebf8f49482a4e129`;
- Zeta23 `2bafb8c88f177284a2123b5fefa2ff84e2365eb6`.

The existing exact event-log loss identity, certified obstruction at 31,
initial nonnegativity proof, and positivity through `log(37)` are reused
unchanged. No new finite-prefix claim or larger excursion scan is made.

## Exact finite identities — LeanChecked

Use the existing definitions

```text
gamma(q) = (log(q)-Lambda(q))/sqrt(q) at Mangoldt events, 0 otherwise,
Delta_m(x) = sum_(m<q<=x) gamma(q),
J_m(b) = sum_(m<q<=b²) gamma(q)*log(b²/q).
```

The already checked prime-power identity is
`gamma(p^k)=(k-1)log(p)/sqrt(p^k)` for prime `p` and `k>=1`.
Thus the nonzero support consists exactly of proper prime powers.

For natural `m>=1` and `0<=s<=S`, `primePowerSurcharge_log_ramp` proves

```text
J_m(sqrt(m*exp(s)))
  = sum_(m<q<=m*exp(S)) gamma(q)*max(s-log(q/m),0).
```

`primePowerSurcharge_eq_integral_logDelta` proves

```text
J_m(sqrt(m*exp(s))) = integral_0^s Delta_m(m*exp(r)) dr.
```

These are specializations of `eventErrorCharge_log_ramp` and
`integral_logEventProfile`, which allow arbitrary real event weights.
`intervalIntegrable_logEventProfile` proves integrability using a finite sum
of measurable constant steps. The event condition is `log(q/m)<=r`, so the
event sum uses the right-continuous convention. The anchor is strictly
excluded. An event at the terminal point has zero ramp/charge; its inclusion
in Delta is harmless for integration. No continuity or integrability
hypothesis is supplied by a certificate field.

For arbitrary real `0<y<=z`, `primeReciprocalWindow_eq_abel` proves

```text
sum_(y<p<=z, p prime) log(p)/p
  = theta(z)/z - theta(y)/y + integral_y^z theta(x)/x² dx.
```

It uses the pinned `sum_mul_eq_sub_sub_integral_mul` with the reciprocal
kernel and prime-log coefficients. `intervalIntegrable_theta_div_sq`
proves the required integrability. `primeSquareWindow_eq_reciprocal`
actually reindexes the natural square events through `p |-> p²`, proving
membership and injectivity. `primePowerDelta_eq_square_add_higher` proves
the square/higher-power split, including disjointness via uniqueness of
prime-power representations. No external event sieve is a proof input.

## Higher-power tail — LeanChecked

`SuzukiHigherPowerIndex` is the product of the prime subtype with naturals;
index `(p,n)` represents exponent `n+3`. Define

```text
H3(m) = sum'_(p prime, n>=0, p^(n+3)>m) gamma(p^(n+3)).
```

This is exactly the requested exponent-at-least-three tail. The existing
per-prime geometric estimate bounds its total exponent mass by
`32*log(p)/p^(3/2)`. `summable_higherPowerMass` combines that estimate with
the checked summability over all naturals and the nonnegative product-sum
theorem. `suzukiHigherPowerValue_injective` prevents duplicate counting.

`suzukiHigherPowerTail_nonneg`, `summable_higherPowerTail`, and
`tendsto_suzukiHigherPowerTail` prove nonnegativity, summability of each
cutoff tail, and convergence to zero. The moving cutoff proof uses Tannery's
dominated-convergence theorem: each fixed prime power is eventually below
the anchor, and the summable total mass dominates every cutoff.
`higherPowerWindow_le_tail` reindexes a finite natural-number window and
bounds it by this same tail. No unjustified infinite-sum interchange occurs.

## Primary finite estimates — LeanChecked, conditional arithmetic input

Let `m>=1` be natural, `epsilon>=0`, and `0<=s<=S`. Assume exactly

```text
forall x in [sqrt(m), sqrt(m*exp(S))],
  abs(theta(x)-x) <= epsilon*x.
```

`primeSquare_log_window_error` proves

```text
abs(Delta_square_m(m*exp(s)) - s/2) <= epsilon*(2+s/2).
```

Here `Delta_square` is identified with `suzukiPrimeReciprocalWindow`
by the proved reindexing. The constant `2` retains both endpoint errors;
the anchored `theta(sqrt(m))/sqrt(m)` contribution is not dropped.

`primePowerDelta_log_window_error` proves

```text
abs(Delta_m(m*exp(s)) - s/2)
  <= epsilon*(2+s/2) + H3(m).
```

`primePowerSurcharge_log_window_error` proves

```text
abs(J_m(sqrt(m*exp(s))) - s²/4)
  <= epsilon*(2*s+s²/4) + s*H3(m).
```

The latter integrates the former using the finite log-profile identity and
`integral_surcharge_error_envelope`. There is no second moving-window
partial-summation argument, and no additional analytic premise.
All constants are exact real constants. These are finite estimates, but
neither the input theta bound nor an outward numerical H3 enclosure is
automatically certified by evaluating a floating-point table.

## Unconditional uniform convergence — LeanChecked

The actual pinned PNT declaration is **global `MediumPNT`**, not
`Chebyshev.MediumPNT`. Its statement is

```text
exists c>0, (Chebyshev.psi-id)
  =O[atTop] (fun x => x*exp(-c*(log x)^(1/10))).
```

`SuzukiThetaPNT.lean` divides by `x`, proves the exponential remainder tends
to zero, and combines this with
`Chebyshev.isBigO_psi_sub_theta_sqrt`. The resulting
`tendsto_theta_div_self` is the unconditional theorem `theta(x)/x -> 1`.
`eventually_theta_log_window_bound` then supplies the finite theta hypothesis
simultaneously throughout each window once the lower endpoint is large.
No PNT assumption remains in the public uniform theorems.

For **every** real `S>=0` and `delta>0`:

```text
uniform_primePowerDelta_log_window:
  exists M:Nat, forall m>=M, forall s in [0,S],
    abs(Delta_m(m*exp(s))-s/2) < delta.

uniform_primePowerSurcharge_log_window:
  exists M:Nat, forall m>=M, forall s in [0,S],
    abs(J_m(sqrt(m*exp(s)))-s²/4) < delta.
```

The proofs combine the finite bounds with `H3(m)->0`. The fixed-ratio
corollaries `tendsto_primePowerDelta_fixed_ratio` and
`tendsto_primePowerSurcharge_fixed_ratio` specialize to `s=log(lambda)`:
for every fixed real `lambda>1`, their limits are respectively
`log(lambda)/2` and `log(lambda)^2/4`.

There are **no remaining formal bridges in this branch**. There is **no
effective numerical threshold** extracted from the existential PNT constants.
Uniform *absolute* error does not give relative asymptotics for shrinking
`s_m`. It says nothing about the relative widths of actual excursions.

## Numerical regression — NumericalEvidence only

The existing scan was rerun at actual cutoff **9,999,993**: 10,341 completed
periods, 7,872 old affine passes, 2,469 old failures, 10,341 rounded-sample
passes, 10,147 local-width passes, and 10,340 event-log passes. The sole
event-log failure remains 31; no universal claim beyond that cutoff follows.
The maximum existing surcharge/loss identity residual is `1.524e-9`.

The new `scripts/suzuki-surcharge-profile.mjs` independently enumerates
proper prime powers up to the largest retained real recovery square
**8,906,232.48818665** (536 powers). It checks the fixed-window ramp and
the integral of the step profile at interior samples and event endpoints,
including 32=2^5, terminal events, and prime-power anchors that must be excluded.
The finite table is a test implementation, not a formal arithmetic oracle.

| Start / next event | Actual recovery b² | J | (log(b²/m))²/4 |
|---|---:|---:|---:|
| 31 / 37 | 34.489536036595 | 0.036720505316541 | 0.002844556637159 |
| 324431 / 361201 | 361197.6403415228 | 0.003037998529773 | 0.002881134982094 |
| 8573249 / 8906237 | 8906232.48818665 | 0.000280578301367 | 0.000362988940299 |

The corresponding real roots are `5.872779242964`, `600.997204936531`,
and `2984.331162620303`. The report retains true endpoint loss, integrated
exact-service event-log cost, rounded-sample cost, and conservative linear
cost separately. The direct endpoint loss and accumulated exact-cell cost
differ by their floating-point residual, not by an asserted mathematical gap.
The required terminal-positive/prefix-negative case at 324431 and worst old
affine slack at 8573249 remain unchanged.

Maximum new residuals: ramp `8.882e-16`, step integration `1.777e-15`,
independently enumerated J versus the exported recovery J `4.590e-13`.
All use IEEE-754 arithmetic, **not proved outward rounding**.

```powershell
cabal run rh-garden -- suzuki-event-regression .cabal-work/event-diagnostics.json
node scripts/suzuki-event-report.mjs .cabal-work/event-diagnostics.json
node scripts/suzuki-surcharge-profile.mjs .cabal-work/event-diagnostics.json
```

## Trust, validation, and what remains open

The full pinned Lean build succeeds (3920 jobs). The new audit
`lake env lean AuditSuzukiSurchargeAsymptotics.lean` prints for each of its
20 declarations, including `MediumPNT` and the uniform theorems:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms, not new project assumptions.
There are no added `sorry`, `admit`, axioms, numerical oracles, or unsafe
proof shortcuts. Cabal build/tests, UI typecheck/build, the established
status commands, numerical report checks, and export checks are run for
the handoff. Static `formal-status` names are navigation metadata, never
the source of proof validation.

Nothing here bounds `V(b)` from below, proves eventual recovery, covers true
losses in a never-recovering excursion, or proves universal event-log budget
safety. The old finite prefix and the explicit global tail premise are
unchanged. In particular no `m>=37` universal threshold has been inferred.

The next independent arithmetic input is an **effective, one-sided anchored
Mangoldt increment bound**, at event arguments and throughout a stated
finite-width regime, for

```text
Q_m(h) = psi(m+h)-psi(m)-h,
W_m(h) = sum_(m<n<=m+h) Lambda(n)/sqrt(n)
         - 2*(sqrt(m+h)-sqrt(m)).
```

The precise cancellation-preserving target is to give an explicit bound
`Q_m(h)<=G(m,h)` (all natural `m>=M`, all real `0<=h<=H(m)`, with specified
`M,H,G` independent of unknown interior samples and an integrable upper
envelope `G`). The corresponding written Abel-summation target charges it as

```text
W_m(h) <= G(m,h)/sqrt(m+h)
          + (1/2)*integral_0^h G(m,v)/(m+v)^(3/2) dv.
```

This is an arithmetic increment problem, not the endpoint-positivity
statement in disguise. No successful constants or window regime for this
tail budget have been established here; inventing them would obscure the
remaining problem. Its envelope must be tested with the exact signed
initial state and independently proved reserve, using the existing finite
cell-cost theorem. A cover must also handle cutoffs inside excursions and
finite prefixes of any nonrecovering excursion. A completed-excursion scan
does not discharge those obligations. Further calibration of the artificial
surcharge is not a substitute for this correctly weighted arithmetic work.
