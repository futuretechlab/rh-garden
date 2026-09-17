# Exact Suzuki surcharge audit

Future Technologies Laboratory LLC. Starting checkout:
`74268ea2249cb3f0257c772481e39f458ca5c661` (the actual HEAD, not an archive).
Dependency pins and the pre-existing untracked `.codex/` are unchanged.

**NO PROOF OF RH IS CLAIMED.** Kernel-checked finite theorems, written
asymptotics, conditional tail criteria, and floating-point observations are
different kinds of evidence throughout this report.

## Kernel-checked finite identities

Use the repository normalizations `V(u)=suzukiPsiRoot u`,
`D(u)=suzukiRootSlopeDiscrepancy u`, `S(u)=suzukiRootArchSlope u`,
`B(u)=max(-D(u),0)`, and `a=sqrt(m)`. Sums exclude the anchor and include
the right endpoint. The signed starting value is **exactly** `-D(a)`, not
`B(a)`. No reflected recurrence is used.

`SuzukiPrimePowerSurcharge.lean` defines

```text
gamma(q) = (log(q)-Lambda(q))/sqrt(q) at Mangoldt events, 0 otherwise,
Delta_m(x) = sum_(m<q<=floor(x)) gamma(q),
J_m(b) = sum_(m<q<=floor(b²)) gamma(q)*log(b²/q),
K_log,m(u) = -D(a) + sum_(m<q<=floor(u²)) eventLogWeight(q) - Service(a,u).
```

The principal declarations and their complete mathematical hypotheses are:

| Declaration | Statement |
|---|---|
| `suzukiPrimePowerOvercharge_prime_pow` | For prime `p`, integer `k>=1`, `gamma(p^k)=(k-1)log(p)/sqrt(p^k)`. |
| `suzukiPrimePowerOvercharge_pos_iff` | `gamma(q)>0` iff `q=p^k` for a prime `p` and integer `k>=2`. |
| `eventLogSignedProfile_eq_neg_discrepancy_add_delta` | For integer `m>=1`, `u>=sqrt(m)`, `K_log,m(u)=-D(u)+Delta_m(u²)`. |
| `primePowerCorrectedProfile_eq_neg_discrepancy` | Under the same hypotheses, `K_log,m(u)-Delta_m(u²)=-D(u)`. |
| `integral_weightedEventError` | For `m>=1`, real `b>=a`, any real sequence `eta`, `integral_a^b (2/u) sum_(m<q<=u²) eta(q) du = sum_(m<q<=b²) eta(q)log(b²/q)`. |
| `eventLogWeightedCost_sub_true_bounds` | For `m>=2`, real `b>=a`, `0 <= L_log-L_true <= J_m(b)`. |
| `eventLogWeightedCost_sub_true_eq_surcharge` | Additionally `D(u)<=0` on the **whole closed** interval `[a,b]`: `L_log-L_true=J_m(b)`. |
| `trueWeightedCost_eq_loss_of_negative` | For `m>=2`, `a<=b`, `D<=0` on `[a,b]`, `L_true=V(a)-V(b)`. |
| `eventLogWeightedCost_eq_loss_add_surcharge` | Under those same negative-excursion hypotheses, `L_log=V(a)-V(b)+J_m(b)`. |
| `eventLog_cost_safe_iff_surcharge_le_endpoint` | Under the same hypotheses, `L_log<=V(a)` iff `J_m(b)<=V(b)`. |
| `corrected_cost_safe_iff_endpoint_nonnegative` | Under the same hypotheses, `L_true<=V(a)` iff `0<=V(b)`. |

Here `L_log` and `L_true` are integrals of `(2/u)max(K_log,m(u),0)` and
`(2/u)B(u)`. Recovery at `b` is **not** a premise of these identities; the
negative-interval property suffices. The existing block-local loss theorem
is glued across `SuzukiEventChain` and then extended to an arbitrary real
terminal point by the canonical chain up to `ceil(b²)`.

Finite sums of right-continuous weighted steps are proved interval
integrable. Signed discrepancy integrability follows from its finite
arrival sum and continuous service; positive-part integrability is proved
using absolute values. At `q=b²`, the charge is zero because `log(b²/q)=0`.
The anchor is never charged, including a zero-width interval. These are
theorems, not certificate fields. Between events, all these profiles use
the previously proved exact service decay and actual `2/u` weight.

The existing exact cell formula remains

```text
integral_r^s (2/u) max(K-(S(u)-S(r)),0) du
  = 2(K+S(r))*log(h/r) - A(2log(h)) + A(2log(r)),
```

where the proved unique service cutoff `h` is clipped to `[r,s]`.
Quadratic and `5/3`-service upper costs can exceed this integral; their
extra cost is not part of `J`. Correcting `K_log` by subtracting `Delta`
produces an exact reference, not new information about prime locations.
Its excursion budget is precisely endpoint positivity again.

## Error propagation, without mixing profiles

`weightedCost_perturbation_bound` takes `m>=2`, `b>=a`, `eta0>=0` and
`eta(q)>=0` for every natural `q`. The perturbed signed state is
`-D(u)+eta0+sum_(m<q<=u²)eta(q)`. It proves

```text
0 <= perturbed_cost - true_cost
  <= eta0*log(b²/m) + sum_(m<q<=b²) eta(q)*log(b²/q).
```

`weightedCost_perturbation_eq_of_negative` proves equality when `D<=0`
throughout `[a,b]`; nonnegative errors then keep both profiles active.
Without that sign hypothesis only the inequality is used.

Prime-power substitution uses `eta=gamma, eta0=0`. Starting-state
enclosure error uses `eta0`. Sample rounding is separately propagated
through both sample endpoints and earlier integral cells; the numerical
cost is computed from that *same rounded profile*. The earlier
`transformed_uniform_sample_allowance` gives the conservative uniform
allowance `delta/sqrt(m)` while keeping `R(m)` exact. Service/integration
overcharge is separate again. A reserve lower enclosure `V(a)-nu` loses
`nu` directly from the budget, not from the arrival profile.

## Proved m=31 obstruction and finite prefix

`block_thirtyOne_thirtyTwo` and `block_thirtyTwo_thirtySeven` certify the
actual event blocks. The non-events 33,34,35,36 are proved to have two
distinct prime divisors; no sieve output is trusted. The event at
`32=2^5` has weight `log(2)/sqrt(32)` and excess weight
`4log(2)/sqrt(32)`.

`exists_unique_recovery31` constructs the unique solution of
`S(b)=suzukiMangoldtSlope 32` in the rational interval
`[5871/1000,5875/1000]`. `recovery31_root_bounds` puts it strictly inside
`(sqrt(32),sqrt(37))`, with `floor(b²)=34`.
`recovery31_first_recovery` proves `D(u)<0` for every
`sqrt(31)<=u<b`; `recovery31_negative_excursion` also proves `D(b)=0`.

The inhabited theorem `suzuki_eventLog_obstruction_thirtyOne` proves

```text
1/100 <= V(b) < 35/1000 < 36/1000 < J_31(b),
V(sqrt(31)) < L_log(31,b),
L_true(31,b) < V(sqrt(31)).
```

This concerns the integrated **exact-service** envelope, not failure of a
quadratic relaxation. `recovery31_true_excursion_safe` proves positivity
throughout this interval. It is not a counterexample to Suzuki or RH.

`SuzukiRationalBounds.lean` supplies specialized archimedean value and
slope enclosures. Their proof uses rational logarithm series, harmonic
bounds for Euler's constant, the existing digamma identity, a rational
partial sum and telescoping bound for the quarter-lattice total, and a
geometric exponential tail. `SuzukiSmallArithmetic.lean` checks the
finite log/square-root/Mangoldt data with ordinary proof-producing
arithmetic tactics. No native numerical decision oracle is used.

`small_affine_state_positive` proves, for every integer `5<=n<=36` and
every real `t>=log(2)`,

```text
A(t) - suzukiMangoldtSlope(n)*t + suzukiMangoldtIntercept(n) >= 1/100.
```

Fresh rational samples and the existing unit-curvature supporting
quadratic prove these bounds. The closed-cell identities give
`suzukiPsi_nonnegative_zero_to_log_thirtySeven`: for
`0<=t<=log(37)`, `Psi(t)>=0`. This is an actual finite proof, not an
uninhabited interface or a total-loss budget across recoveries.
The earlier `3,4,5` certificate and already proved
`suzukiInitialNonnegative_proved`, `suzukiPsiArchimedean_ge_exp_sub_one`,
and `suzukiPsi_pos_zero_to_log_three` are reused, not reproved.

## Surcharge asymptotics: written derivation, partial formalization

For each fixed real `lambda>1`, the unconditional mathematical conclusion is

```text
Delta_m(lambda*m) -> (1/2)log(lambda),
J_m(sqrt(lambda*m)) -> (1/4)log(lambda)^2.
```

These two limit statements are **not yet LeanChecked** in this checkout.
Here is the derivation and the exact remaining formal work.

Put `x=sqrt(m)`, `y=c*x`, `c=sqrt(lambda)`. Squares contribute
`sum_(x<p<=y)log(p)/p`. Write `theta(t)=t(1+e(t))` with `e(t)->0`.
Partial summation gives

```text
Delta_square = theta(y)/y - theta(x)/x + integral_x^y theta(t)/t² dt.
```

Its main term is `log(c)`. If `|e(t)|<=epsilon` for `t>=x`, the error is
at most `epsilon*(2+log(c))`, which tends to zero.

The square part of `J` is `2 sum_(x<p<=y)log(p)/p*log(y/p)`, hence

```text
J_square = -2*theta(x)/x*log(c)
  + 2*integral_x^y theta(t)*(1+log(y/t))/t² dt.
```

Its main term is `log(c)^2`. The error is at most
`epsilon*(4log(c)+log(c)^2)`. The open-left, closed-right convention is
preserved by partial summation; a prime exactly at `y` has zero J charge.

For powers of exponent at least three, let `r=p^(-1/2)<=1/sqrt(2)<3/4`.
Their total mass for a fixed prime is

```text
log(p)*sum_(n>=0)(n+2)*r^(n+3)
  = log(p)*r³*(2-r)/(1-r)² <= 32*log(p)/p^(3/2).
```

`higherPower_geometric_mass`, `primePowerOvercharge_eq_geometric`, and
`summable_higher_primePower_overcharge` formalize this exponent sum and
bound. `summable_log_div_threeHalves` proves the dominating natural-number
series summable, using `log(n)<=4*n^(1/4)` and the `5/4` p-series. Thus the
double higher-power series converges. Its mass above `m` tends to zero;
the J factor on `(m,lambda*m]` is between zero and `log(lambda)`, so its
weighted tail also vanishes.

The missing formal bridge is the prime-power reindexing/moving-tail limit
and the two moving-window partial-summation limits from `theta(t)/t->1`.
The pinned `Chebyshev.MediumPNT` in `Zeta23/FromPNTPlus/MediumPNT.lean` supplies an existential
positive constant in a global psi error estimate; Mathlib's
`Chebyshev.psi_sub_theta_le` transfers PNT to theta. These contain no
explicit usable cutoff for this task. No new dependency or RH assumption
has been introduced. This derivation does **not** assert that actual
excursions have fixed relative width or that their budgets fail eventually.
It does show why proper-prime-power overcharge cannot simply be declared
negligible by raising a fixed threshold.

## A concrete unconditional arithmetic attempt

For every integer `1<=m<=q`, set

```text
P(q) = 2log(4)*sqrt(q) + 2log(q) + log(q)^2/2.
```

`mangoldtSlope_le_pinnedPrefix` and `excess_le_pinnedPrefix_anchored`
instantiate the pinned `Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise`:

```text
E_m(sqrt(q)) <= P(q) - T(m) - Service(sqrt(m),sqrt(q)).
```

It uses no intervening exact Chebyshev samples; only the exact anchor
state and explicit constants. `pinnedPrefix_signed_cancellation` proves
that adding `-D(sqrt(m))` leaves exactly `P(q)-S(sqrt(q))`. The scanner
retains the exact state at the anchor, uses this bound at later events,
and integrates exact service decay on every cell. Thus cancellation is
not discarded, but the global-prefix error still dominates the budget.

| Start m | First failing cell | Actual E there | Pinned upper E | Cumulative cost | Reserve | Deficit |
|---|---:|---:|---:|---:|---:|---:|
| 31 | 32 | -0.055641795358 | 19.506098917925 | 1.494500648087 | 0.058720526098 | 1.435780121989 |
| 324431 | 324473 | 0.059934771791 | 548.658830080833 | 0.091310234112 | 0.067287445205 | 0.024022788907 |
| 8573249 | 8573419 | 0.018271096040 | 2424.209810818577 | 0.050331271817 | 0.048549657324 | 0.001781614493 |

These are **numerical** quantitative failures of a proved arithmetic upper
bound's cost budget, with no reserve enclosure error charged. Total costs
are respectively `1.494500648086`, `60.260611269882`, `93.211250193116`.
The inequality itself is valid; its error is of global-prefix size rather
than the small anchored oscillation needed locally. Exact integration does
not repair that loss. The existing all-integer local-width bound was also
retested and remains inadequate for both large regressions.

## Numerical regressions and actual recovery coordinates

All numbers here use `Double`, not certified floating-point arithmetic.
The formal identities, not their residuals, are the source of proof.

| m / next-event label | Actual recovery b² | True loss | Exact-service event-log cost | J | Rounded-sample cost | 5/3 rounded cost |
|---|---:|---:|---:|---:|---:|---:|
| 31 / 37 | 34.489536036595 | 0.028933626483 | 0.065654131799 | 0.036720505317 | 0.028938487783 | 0.032087460527 |
| 324431 / 361201 | 361197.6403415228 | 0.031469829319 | 0.034507827849 | 0.003037998530 | 0.031469922417 | 0.031788344297 |
| 8573249 / 8906237 | 8906232.48818665 | 0.008051052220 | 0.008331630521 | 0.000280578301 | 0.008051058653 | 0.008080368955 |

The real roots are respectively `5.872779242964`, `600.997204936531`,
`2984.331162620303`. Recovery reserves are `0.029786899615`,
`0.035817615788`, `0.040498605158`. `interval_end` is the last integer
`floor(b²)`, not a recovery coordinate; `recovery_before_event` is the
**next** event. Neither is interchangeable with `b²`.

At actual cutoff **9,999,993** (`t_max=16.118095`), the reported baseline
is reproduced: 10,341 completed periods; 7,872 old affine passes and
2,469 failures. Rounded samples pass 10,341, local-width passes 10,147,
event-log passes 10,340. The sole event-log failure is 31. The two large
cases keep their earlier terminal/prefix slack behavior and the worst
old anchored-envelope slack `-6.959435462548` at 8573249.
Maximum surcharge-identity residual is `1.524e-9`.

A full-origin scan at actual cutoff **19,999,999** has 14,451 completed
periods and still only the 31 surcharge failure. No zero reset is used
for a large-range window. The next smallest observed `V(b)-J` is
`0.024715479148` at start 47 (which includes the prime-square event 49).
Maximum identity residual is `2.460e-9`. This is evidence only and does
not prove that `m>=37` suffices.

The exporter records actual event E, arithmetic bounds, outgoing service,
exact/rounded/conservative cell costs, cumulative costs, remaining reserve,
and first failing cells. Endpoint, prime-square, interior-recovery and
signed-surplus regressions are retained. Commands:

```powershell
cabal run rh-garden -- suzuki-event-regression .cabal-work/event-diagnostics.json
node scripts/suzuki-event-report.mjs .cabal-work/event-diagnostics.json
cabal run rh-garden -- suzuki-surcharge-scan 20000000 .cabal-work/surcharge-scan.json
```

## Coverage and the remaining tail

The completed-period scanner omits an unfinished terminal negative
excursion. The larger scan explicitly reports its terminal state; at
event 19,999,981 the discrepancy is `-0.137291192548`, and the unrestricted
optimizer for that frozen state lies beyond the cutoff. That optimizer
is not asserted to be a future actual recovery after further jumps.
The report separately includes the post-arrival arithmetic state and
discrepancy at the integer cutoff: slope `8941.722620060180`, discrepancy
`-0.137025377437`, so the terminal excursion is still unfinished.

The finite prefix uses a cover of closed integer cells and therefore
needs no recovery assumption. `suzukiPrefixThirtySevenPlusTail` plugs it
into the existing exact-prefix-plus-tail interface. Its explicit remaining
premise is `forall t>=log(37), Psi(t)>=0`, including any crossing or
never-recovering excursion. No completed-excursion theorem is substituted
for that premise, and no recovery theorem is claimed here.

For the proposed event-log route at recovery points the arithmetic target
is **exactly `J_m(b)<=V(b)`**, stronger than `V(b)>=0`. Even a proof of that
strengthening for completed periods would still need coverage of all
other points and nonrecovering periods. The prime-power-corrected profile
removes artificial cost but does not supply a tail estimate.

The next precise formal arithmetic theorem justified by this work is:
for every real `lambda>1`, as natural `m->infinity`,
`suzukiPrimePowerSurcharge m (sqrt(lambda*m)) -> (log(lambda))²/4`.
The written proof above identifies its missing PNT/partial-summation
bridge. For *positivity*, genuinely new effective anchored short-interval
control, with enough information to compare true weighted loss against a
proved reserve, is still needed; neither this asymptotic nor the global
prefix bound provides it.

## Trust and validation

The full pinned Lean build succeeds (3908 jobs). The axiom audit command
`lake env lean AuditSuzukiSurcharge.lean` prints, for each of its 25
principal declarations, exactly:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms, not project assumptions. No
`sorry`, `admit`, project axiom, native numerical proof oracle or unsafe
shortcut is added. The initial interval remains proved and is reused.
The submission status remains **NO PROOF OF RH IS CLAIMED.**

`cabal build`, `cabal test`, `npm run typecheck`, `npm run build`, and the
established `formal-status`, `garden`, `kernel`, and `submission` commands
pass. The first Cabal test run caught a stale frontier-text assertion;
the interface description and stronger assertions were updated and the
complete suite passed on rerun. Both numerical scans and the event-report
assertions pass. Existing Lean linter and Haskell partial-function warnings
remain; no new proof assumption is hidden by those warnings.
