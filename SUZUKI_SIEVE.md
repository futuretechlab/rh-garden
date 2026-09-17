# Correctly weighted anchored arithmetic bounds

Copyright (c) 2026 Future Technologies Laboratory LLC.

Starting checkout: `819b940219df3500171f397e57ce384f37695a38`.
The surcharge-asymptotic branch is unchanged. This continuation proves an
effective arithmetic bound, instantiates it, and measures its substantial
deficit against Suzuki reserves. **NO PROOF OF RH IS CLAIMED.**

## Kernel-checked arbitrary-interval identities

Write `V(u)=suzukiPsiRoot(u)`, `D(u)=suzukiRootSlopeDiscrepancy(u)` and
`E_m(y)=psi(y)-psi(m)-(y-m)`. The new definitions use

```text
I_m(x) = integral_m^x E_m(y) (1 + log(x/y)/2)/(y sqrt(y)) dy,
C_m(x) = 4(sqrt(x)-sqrt(m)) - 2 sqrt(m) log(x/m),
Adef_m(x) = integral_m^x ArchDefect(sqrt(m),sqrt(y))/y dy.
```

`integratedKernel_eq_rpow` identifies `y sqrt(y)` with `y^(3/2)` for
`y>0`. In `SuzukiAnchoredIntegral.lean`:

- `anchoredIntegral_eq_logArrival_sub_main`, for natural `m>=1`, real
  `x>=m`, proves
  `I_m(x)=sum_(m<q<=x) Lambda(q)/sqrt(q)*log(x/q)-C_m(x)`.
- `suzukiPsiRoot_eq_signed_anchoredIntegral`, for `m>=2`, `x>=m`, proves
  `V(sqrt(x))=V(sqrt(m))+D(sqrt(m))*log(x/m)-Adef_m(x)-I_m(x)`.
- `integratedArchDefect_eq` proves
  `Adef=C-A(log x)+A(log m)+S(sqrt(m))*log(x/m)`.
- `anchoredIntegral_le_accuracy_budget`, for `m>=1`, `x>=m`, `eta,beta>=0`
  and `E_m(y)<=eta*(y-m)+beta` for every real `y in [m,x]`, proves
  `I_m(x)<=eta*C_m(x)+beta/sqrt(m)*log(x/m)`.
- `anchoredError_prime_predecessor`, for every prime `p`, proves
  `E_(p-1)(p)=log(p)-1`.

The real-endpoint Abel theorem is the pinned
`sum_mul_eq_sub_sub_integral_mul`, applied to
`f(y)=log(x/y)/sqrt(y)`, with derivative
`-(1+log(x/y)/2)/(y sqrt(y))`. Continuity of the kernel and interval
integrability of the monotone step function are proved, not hypotheses.
Archimedean integration reuses the exact service-defect theorem and chain
rule. The anchor is excluded; a terminal event has logarithmic weight zero.
All events, including prime powers, remain right-continuous.

There is **no** negative-excursion, eventual-recovery, event-anchor, or
nonnegative-discrepancy hypothesis. In particular, the exact signed initial
`D` is not replaced by a reflected backlog. No all-prefix positivity follows
just from evaluating the identity at one endpoint.

The calibration preserves `R(y)-R(m)`, not `|R(y)|+|R(m)|`.
`integratedMainTerm_nonneg` is checked. For interpretation, elementary
differentiation gives the small-width scale
`C_m(m+h) ~ h^2/(2*m^(3/2))` for fixed `m` and `h/m -> 0`; this scale
observation is not registered as a new Lean asymptotic theorem.
The prime predecessor theorem rules out a uniformly small pure-slope error
at all anchors and all unit prefixes.

## The effective arithmetic theorem and its inputs

`SuzukiFiniteSieve.lean` defines, for a finite divisor support `Dset` and
rational coefficients `a`,

```text
nu(n) = (sum_(d in Dset, d|n) a(d))^2.
```

Assume every support element lies in `[1,z]`, `1 in Dset`, `a(1)=1`,
and `z<=m`. (Thus the user's regime `1<=z<m` is included.) Lean proves
`nu>=0`, `nu(p)=1` for primes `p>z`, and for arbitrary nonnegative finite
weights

```text
sum_(m<p<=N, p prime) w(p) <= sum_(m<n<=N) w(n)*nu(n).
```

`weighted_sieve_eq_quadratic` proves the exact expansion

```text
sum_n w(n)*nu(n)
  = sum_(d,e in Dset) a(d)*a(e)*sum_(n, lcm(d,e)|n) w(n).
```

`unit_sieve_eq_count_quadratic` gives the exact natural counting entries
`N/lcm(d,e)-m/lcm(d,e)` with integer division, assuming `m<=N`.
`count_multiples_real_Ioc` identifies the real-endpoint counts as
`floor(x/L)-m/L`. Negative coefficient products are retained: upward
rounding every matrix entry is not a valid evaluation method.

The proper-power majorant is `suzukiAllBasePowerBound m N w`:

```text
sum_(2<=k<=Nat.log 2 N) sum_(2<=a<=N, m<a^k<=N) log(a)*w(a^k).
```

This exact integer exponent cutoff is sufficient because `2^k<=a^k<=N`.
It is the integer implementation of the usual logarithmic cutoff. All
integer bases are allowed. Composite bases and multiple representations
can overcount; they cannot omit a prime-power term. The proof uses prime
power factorization to establish domination, not a supplied future event
table. `weightedMangoldt_le_prime_add_allBasePowers` and
`weightedMangoldt_le_sieve_add_allBasePowers` prove this inclusion with
the correct `log(p)` weight, not `log(p^k)`.

Finally `anchoredIntegral_le_sieve`, for `m>=1`, `x>=m` and the divisor
hypotheses above, proves the requested bound:

```text
I_m(x) <= sum_(m<n<=floor(x))
           log(n)/sqrt(n)*log(x/n)*nu(n) + PP_m(x) - C_m(x).
```

This is an arithmetic theorem with actual proof terms, not a certificate
field assuming its conclusion. The only arithmetic inputs are the anchor,
endpoint, finite rational coefficients, and exact integer divisibility.
Translation dependence through residues is intentional; sample independence
does not mean translation independence.

## Proved concrete improvements

The explicit rational specialization is `Dset={1,2}`, `a_1=1,a_2=-1`.
Lean proves that its sieve weight is the odd-integer indicator. In particular,

```text
anchoredIntegral_ten_fifteen_le_sieve:
I_10(15) <= SieveUpper({1,2},a,10,15),

sieveIntegralUpper_ten_fifteen_eq:
SieveUpper = log(11)/sqrt(11)*log(15/11)
           + log(13)/sqrt(13)*log(15/13) - C_10(15).
```

`allBasePowerBound_ten_fifteen` proves that the all-base proper-power
contribution is zero. No assertion that 11 or 13 is prime is needed for
this upper bound. `sieve_ten_fifteen_strictly_improves_baseline` proves strict
improvement over the baseline `sum_(10<n<=15) log(n)/sqrt(n)*log(15/n)-C`.
These are instantiated finite bounds, not uninhabited structures.

A second universal specialization pays `log 2` at even integers and `log n`
at odd integers. `vonMangoldt_le_parity` proves it at every integer, including
powers of two. `anchoredIntegral_le_parity` integrates it, and
`parityIntegralUpper_lt_baseline` proves strict improvement whenever an
even integer `q>2` occurs strictly before `x` in the interval. It remains
valid on arbitrarily short prefixes; there is no artificial pure-slope
assumption. Neither specialization asserts a universally adequate reserve.

## Independent numerical screen

Run:

```text
cabal run rh-garden -- suzuki-event-regression .cabal-work/event-diagnostics.json
node scripts/suzuki-event-report.mjs .cabal-work/event-diagnostics.json
node scripts/suzuki-sieve-regression.mjs .cabal-work/event-diagnostics.json .cabal-work/sieve-diagnostics.json
```

`suzuki-sieve-candidate.mjs` accepts no prime, event, psi, theta, or reserve
samples. Its predetermined rule is
`z=max(1,min(600,m-1,floor(sqrt(floor(x)-m))))`; support is the squarefree
integers at most `z`. Weighted residue sums form the matrix. Cholesky
suggests coefficients, rounded to integers over `10^6`; those rational
proposals are exported for reproducibility. The validity theorem does not
depend on trusting the optimizer, and **no optimizer-minimum claim is made**.

The candidate computes the full integer-divisor expression, including the
all-base proper-power overcount. It has no fitted density error or burst
allowance: those are encoded explicitly in its finite residue expression.
For unit and shorter prefixes the level may be 1, so its estimate can be
particularly crude. Direct weighted optimization improves the count-based
screen slightly, but does not remove its persistent prime-part overcharge.

Future samples are built only in `suzuki-sieve-regression.mjs`, from the
origin, for validation. The actual validation cutoff is **19,999,999**
(needed for the unfinished terminal regression), not a new enlarged
completed-excursion scan. Measured recoveries are test endpoints only, not
universal interval caps or inputs to a parameter fit. All decimals below
are **NumericalEvidence**, not proved outward enclosures.

| m | actual real x at recovery | true I | sieve upper | signed reserve budget | deficit |
|---:|---:|---:|---:|---:|---:|
| 31 | 34.489536036595 | -0.023066239 | 0.058351335 | 0.006720661 | 0.051630675 |
| 324431 | 361197.640341523 | 0.030312196 | 3.136082786 | 0.066129812 | 3.069952974 |
| 8573249 | 8906232.48818665 | 0.007940787 | 2.305584593 | 0.048439395 | 2.257145198 |

The old next-event labels are respectively 37, 361201 and 8906237, not
the real recoveries. At 31 the proper-power event 32 is retained. Its
previously proved event-log obstruction and true safety are unchanged.

The large cases decompose as follows:

| contribution | 324431 | 8573249 |
|---|---:|---:|
| starting V | 0.067287445343 | 0.048549660205 |
| signed D log(x/m) | -0.001157633695 | -0.000110264854 |
| integrated archimedean defect | 8.80631e-17 | 3.26872e-21 |
| C | 3.341642919375 | 2.139235458087 |
| actual prime weighted sum | 3.368982247189 | 2.146895667029 |
| sieve prime weighted sum | 6.457682581684 | 4.441869733236 |
| prime-part overcharge | 3.088700334496 | 2.294974066207 |
| actual proper-power part | 0.002972867808 | 0.000280578301 |
| all-base proper-power part | 0.020043123471 | 0.002950318333 |
| proper-power overcharge | 0.017070255663 | 0.002669740032 |

Granting the **actual** proper-power contribution only as a favorable
validation comparison gives `3.119012530117` and `2.302914853450`, reproducing
the user's preliminary screen. Levels are 191 and 577, with 117 and 352
divisors. Count-optimized coefficients give `3.136338791071` and
`2.305638240736`. Replacing prime logarithms by `log x` in that count-first
comparison gives `3.172488719559` and `2.312688840738`. The all-integer
baselines are `39.182687015353` and `32.039010002799`; parity reduces these
to `19.078049318104` and `15.691237847030`. This is a genuine improvement
but nowhere near reserve compatibility.

The first failures on the **predetermined test grid**, not claimed first
failures over all real prefixes, are `329026.830042690` and
`8625277.670029163`. The corresponding bound/budget pairs are
`0.072933164/0.067135760` and `0.072936491/0.048532152`.
At 31 the first grid failure is `33.399056025159`.

Other required regimes:

| interval | true I | sieve upper | budget | endpoint result |
|---|---:|---:|---:|---|
| 324432 to 361197.640341523, cutoff inside excursion | 0.030500666 | 3.136271257 | 0.066318282 | fails |
| 19999981 to 19999999, still negative D at cutoff | -1.81122e-9 | 8.00831e-9 | 0.041983029 | passes numerically |
| 30 to 31, terminal prime | -0.002960639 | -0.002960639 | 0.055759887 | passes numerically |
| 31 to 32, terminal proper power | -0.002821005 | -0.002821005 | 0.043243580 | passes numerically |
| 31 to 32.25, after jump | -0.003425578 | 0.001342239 | 0.039449892 | passes numerically |
| 10 to 15, signed surplus at anchor | 0.047603849 | 0.047603849 | 0.079686716 | passes numerically |
| 31 to 31 | 0 | 0 | 0.058720526 | passes numerically |
| 37 to 37.5 | -0.000549216 | -0.000549216 | 0.042122775 | passes numerically |

For `10 -> 15`, the variable-level rule nevertheless fails a tested prefix
at 13.125, when its level is only 1. Endpoint success is therefore explicitly
not promoted to interval success. The fixed `{1,2}` formal specialization
and the variable-level numerical rule are identified separately.
At the 31 recovery, parity gives `0.005504657833 < 0.006720660781`, whereas
at 10 to 15 parity gives `0.105034638464 > 0.079686715541`.
Both pass the remaining short-prefix endpoint tests, but both fail the
large and cutoff-straddling budgets. No positive initial surplus is discarded:
the 10 anchor has `D=+0.102232783831`. At 19,999,999 the terminal discrepancy
is still `-0.137025377942`; eventual recovery is not presumed.

The report records every contribution, coefficient proposal, first grid
failure, and residual. Independent cellwise quadrature checks the anchored
integral identity; direct evaluation of the explicit formula checks the
signed reserve identity. Matrix/direct-sum residuals are under `1e-8`.
`numerical_enclosure_error` is deliberately `null`: there is no proved
rounding bound, no outward rounding, and no certified numerical reserve
comparison here. The large deficits are exploratory failures of these
particular estimates, not a theorem excluding all divisor sieves.

## Validation and remaining arithmetic work

The full pinned Lean build succeeds (3923 jobs). The 19-declaration
`AuditSuzukiArithmeticSieve.lean` audit is the authoritative axiom check;
its actual output for every declaration is
`depends on axioms: [propext, Classical.choice, Quot.sound]`.
These are standard foundational axioms, not project assumptions.
The source adds no axioms, `sorry`, `admit`, or unsafe proof shortcuts.
Cabal build/tests, UI typecheck/build, formal-status/garden/kernel/submission,
the numerical regressions and the versioned export checks accompany the
handoff. Static theorem-name metadata is navigation, not proof checking.

The established event scan reproduces cutoff 9,999,993, 10,341 periods,
7,872 old-affine successes and 2,469 failures. The 324431 regression retains
positive terminal slack and negative prefix slack; 8573249 retains the
worst reported old anchored-envelope failure. Existing finite positivity
through `log 37`, initial positivity, and the certified m=31 obstruction
are reused without extending or reproving them.

The new finite analytic/arithmetic bridge is complete. The missing result
is **quality**, not another certificate interface. The sieve prime bounds
are roughly twice the true prime sum. Proper-power sharpening alone would
leave almost the entire observed deficit. An improvement must be justified
by arithmetic information or a better majorant, not by fitting future samples.

One independently formulated next target is to obtain an **explicit M**
and prove, for all natural `m>=M` and all real
`m^(2/3)<=h<=m/8`, with `x=m+h`,

```text
I_m(x) <= C_m(x)/100 + log(x)/sqrt(m)*log(x/m).
```

This is a proposed arithmetic research target, **not a proved bound or an
assertion that such an explicit M has been found**. It uses only `m,h`,
not V, D or local samples. Its illustrative charges in the two large
windows would be `0.035828360440` and `0.021600604742`, below their measured
budgets. A pointwise route would require a one-percent density allowance
plus a logarithmic burst allowance; the direct integrated target need not
assume that pointwise bound. The latter cannot simply be extrapolated to
all microscopic intervals. The present weighted sieve does not prove
either version. No explicit short-interval PNT constants have been imported
from a citation or inferred from the non-effective pinned PNT.

Even this proposed regime would need separate short-prefix bounds and
independently proved starting reserves. Uniform coverage must include
cutoffs inside excursions and every finite prefix of an excursion which
never recovers. The arbitrary-finite-interval identity removes a recovery
assumption from the formula, not these arithmetic coverage obligations.
No universal threshold at 37 or universal tail positivity is asserted.
