# Optimal use of cumulative moment information

Future Technologies Laboratory LLC, September 2026.

Starting checkout: `dc95eb6146899a0dc91a2f561774f58c6bc6d737`.
The live checkout matched the report; only the pre-existing untracked `.codex/`
was present. Dependency pins and the completed recovery-floor modules are unchanged.

**NO PROOF OF RH IS CLAIMED.**

## Scope and information boundary

This branch optimizes two precisely specified relaxations, not the Mangoldt
sequence itself. It supplies improved unconditional finite lower bounds, not
a uniform lower floor, a smaller zero-free strip, or a new positivity criterion.

The P-only candidate uses exactly `(q,s)` and the proved cumulative cap P.
The parity candidate additionally uses the already-proved pointwise parity cap.
Here `s=S_q` is an intentionally retained scalar terminal state. Neither
candidate reads intermediate prime, Mangoldt, or Chebyshev samples. Numerical
recovery coordinates enter only the separate validation of the dual margin.

The finite-instance proof reuses the previously certified prefix state at 31;
that explicit finite information is not a hidden input to the universal
candidate. No new prime table or larger arithmetic scan was added.

## Audited inputs

The actual definitions remain

```
S_q = sum_{1<=n<=q} Lambda(n)/sqrt(n),
T_q = sum_{1<=n<=q} Lambda(n)*log(n)/sqrt(n),
A_star(s) = sup_{t>=log 2} [s*t-A(t)].
```

`Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise` has hypothesis **real x>=1**
and bounds the sum over `0<n<=floor(x)`. The existing adapter
`mangoldtSlope_le_pinnedPrefix` has hypothesis **natural q>=1** and proves

```
S_q <= P(q),
P(x)=2 log(4)*sqrt(x)+2 log(x)+(log(x))^2/2.
```

The new `pinnedPrefix_mono` proves monotonicity on natural indices >=1.
The parity bound reuses `vonMangoldt_le_parity` from `SuzukiFiniteSieve.lean`:
even n have weight at most log(2); odd n at most log(n). This includes the
correct weights at all prime powers and needs no local primality classification.

No existing finite layer-sum optimizer was found. The new finite Abel identity
uses the existing interval-sum recurrence and telescoping APIs, not a new
measure-theoretic partial-summation development.

The existing active-block adapter and curvature bound are reused, not altered.
Every actual recovery lies strictly inside its active complete block and has
reserve `T_q-A_star(S_q)`. The sharper state-local curvature estimate still
retains the actual left reserve and signed discrepancy. Its sharpness is not
available from `(q,s,P,parity)` alone.

## Exact finite identities and P-only optimality

`RHGarden.CumulativeMoment.mass a n` sums indices 2,...,n; `moment a q`
sums `a_n log(n)` on 2,...,q. Values outside the finite index set are irrelevant.
Put `s=mass a q` and `ell_n=log((n+1)/n)>0`.

For q>=2, `moment_eq_layer` proves, without any sign assumption,

```
T_q = s log(2) + sum_{2<=n<q} (s-S_n)*ell_n.
```

For arbitrary U, `moment_sub_lower` proves the exact identity

```
L_U(s;q) = s log(2) + sum_{2<=n<q} max(s-U_n,0)*ell_n,
T_q-L_U(s;q) = sum_{2<=n<q} (min(s,U_n)-S_n)*ell_n.
```

`lower_le_moment` assumes `a_n>=0` on 2,...,q and `S_n<=U_n` for 2<=n<q.
These assumptions make every displayed gap summand nonnegative. There is no
continuous input obligation or unspecified integrability premise.

`prefix_cap_attainment` assumes q>=2, s>=0, U nonnegative and nondecreasing
on natural indices >=2, and `s<=U_q`. Define C_0=C_1=0 and
`C_n=min(s,U_n)` for n>=2. Its increments are nonnegative, meet every prefix
cap, have total s at q, and attain **exactly** `L_U(s;q)`.
`capped_increments_supported` proves those increments vanish outside 2,...,q.

Together the lower-bound and attainment theorems establish the minimum over
arbitrary nonnegative real finite weight vectors with these prefix caps and
total s. This is NOT an optimum over primes, prime powers, Euler products,
active-block data, or all arithmetic information. The attaining artificial
weights need satisfy none of those additional constraints.

### Actual arithmetic instances

`mangoldtIntercept_eq_layer`, `mangoldtIntercept_sub_cumulativeLower`, and
`cumulativeMomentLower_le_intercept` instantiate the identities and inequality
with `a_n=Lambda(n)/sqrt(n)` and `U_n=P(n)`, with actual proof terms.
`pinned_moment_relaxation_attained` instantiates the relaxation optimum at S_q.
`globalDualMargin_ge_cumulative` subtracts the SAME exact A_star(S_q).
It is a lower bound for the unrestricted margin for every q>=2; the existing
active-block theorem is still required to identify that margin with a recovery.

The finite improvement proof establishes

```
q>=31 -> log(2)*S_q + 4/5 <= L_P(S_q;q) <= T_q.
```

It uses the existing proof `S_31>=8936967/1000000`, monotonicity of S,
`P(2)<=6`, and `log(3/2)>=2/5`, retaining just the n=2 layer term.
The declarations include `cumulativeMoment_thirtyOne_improves`,
`cumulativeMoment_thirtyTwo_improves`, and
`cumulativeMoment_thirtyOne_proved_bound`. The q=32 instance includes the
proper-prime-power state of the retained m=31 excursion. No floating-point
value in the numerical table is a premise of these proofs.

## One additional constraint: parity

For c_n>=0 and nonnegative nondecreasing U, define

```
C_0=C_1=0,
C_n=min(s,U_n,C_(n-1)+c_n), n>=2.
```

`greedy_nonneg`, `greedy_mono`, `greedy_le_total`, `greedy_le_cap`, and
`greedy_increment_le` prove feasibility. `mass_le_greedy` proves domination
of EVERY feasible prefix, using its prefix caps, pointwise caps, and total
mass allowance. This domination direction does not require U monotone.

If any nonnegative feasible sequence has total s, `greedy_terminal_eq` proves
`C_q=s`. `greedy_attainment` then proves the increments attain the minimum
logarithmic moment, and `greedy_increments_supported` supplies finite support.
The hypotheses for attainment include monotonicity and nonnegativity of U
and nonnegativity of c; these are discharged for the actual arithmetic caps.

`greedy_layer_le_moment` and `lower_le_greedy_layer` prove

```
L_P(S_q;q) <= L_(P,parity)(S_q;q) <= T_q.
```

The exact extra information is exposed by `greedy_layer_sub_lower`:

```
L_(U,c)(s;q)-L_U(s;q)
 = sum_{2<=n<q} [min(s,U_n)-C_n]*ell_n.
```

`parityCumulativeMomentLower_le_intercept`,
`parity_moment_relaxation_attained`, and
`globalDualMargin_ge_parityCumulative` instantiate all arithmetic premises.
This optimum is still ONLY for real weights with the two specified caps.

## Numerical adequacy: common dual, separate error accounting

`suzuki-moment-candidate.mjs` accepts only q and s; its cumulative and parity
caps are fixed symbolic rules. `suzuki-moment-regression.mjs` reads actual
states exported by the existing sieve validation path. It does no prime scan.
All rows below use the same approximate dual `s*t-A(t)` at the retained
recovery coordinate t. Changing from F to the baseline column includes a
sharper archimedean calculation; only baseline-to-P is pure moment improvement.

| Excursion start | Active q | Actual margin | log(2)S-A_star | P-only margin | P+parity margin | Older F |
|---|---:|---:|---:|---:|---:|---:|
| 31 | 32 | 0.029786900 | -15.517174746 | -13.674166865 | -1.915109179 | -84.341262584 |
| 324431 | 361183 | 0.035817616 | -12150.554173087 | -1248.783276795 | -1195.517495228 | -21465.560249895 |
| 8573249 | 8906197 | 0.040498608 | -79443.173948952 | -4768.251209367 | -4714.983971659 | -129100.116157159 |

The recovery squares remain 34.489536036595, 361197.6403415228, and
8906232.48818665; next-event labels are not substituted for them.
Parity gains over P are about 11.759057686, 53.265781566, and 53.267237708.
The remaining deficits against actual reserves are about 1.944896079,
1195.553312844, and 4715.024470267. None of these bounds pays the reserve.

**Enclosure error: not certified (`null`).** Computation uses IEEE-754 and
compensated sums, not outward interval arithmetic. The terminal discrepancy
residuals are about 5.51e-14, 5.00e-12, and 1.77e-10. Agreement of the greedy
increment moment with its layer formula is a numerical regression, not a
proof or an error enclosure. The approximate dual is not an exact optimizer
witness. The Lean finite identities and symbolic instance are the proof results.

The existing short-prefix, m=31, large-excursion, strict one-percent failure,
and unfinished-terminal cases are retained. In particular 19999981->19999999
still has negative terminal discrepancy and no computed recovery endpoint.

## Asymptotic audit — WRITTEN DERIVATION, not LeanChecked

No new Big-O or Tendsto theorem for these optima is claimed. The finite
identities, arithmetic inequalities, attainment and finite-prefix comparison
are formalized. The following asymptotic analysis is ordinary mathematics.

Write kappa=2 log(4). Extend P to real y>=2 and let Y solve P(Y)=s for large s.
P is strictly increasing and unbounded, so this solution is unique. Since
`P(y)=kappa*sqrt(y)+O(log(y)^2)`,

```
sqrt(Y)=s/kappa+O(log(s)^2),
log(Y)=2 log(s/kappa)+O(log(s)^2/s).
```

The continuous layer integral is

```
s log(2)+integral_2^Y (s-P(y))/y dy
 = s log(Y) - [2 kappa sqrt(y)+(log y)^2+(log y)^3/6]_2^Y
 = 2s log(s/kappa)-2s+O(log(s)^3).
```

The integer-grid error is nonnegative and bounded independently of s and q.
On each [n,n+1], the positive-part map is 1-Lipschitz and P is increasing,
so the difference between the grid and integral terms is at most

```
(P(n+1)-P(n))*log(1+1/n).
```

These terms are O(n^(-3/2)+(log n)/n^2), a summable majorant. If P(q)>=s,
the positive part vanishes beyond q, so this comparison is uniform over all
such q, not a pointwise limit silently interchanged with q.

The existing quarter-series formula and first-derivative formula give
`A(t)=4 exp(t/2)+c*t+O(1)` and `A'(t)=2 exp(t/2)+c+O(exp(-t/2))`.
For the actual half-line optimizer at large s this yields
`t_s=2 log(s/2)+O(1/s)` and

```
A_star(s)=2s log(s/2)-2s+O(log s).
```

Consequently the P-only lower margin has the written asymptotic

```
[L_P(s;q)-A_star(s)]/s -> -2 log(log 4) = approximately -0.653268519957,
```

uniformly over q with P(q)>=s. This is an unbounded negative lower-bound
function, not a negative upper bound on actual recovery reserves.

### Fixed exact initial prefix

`lower_sub_lower_fixed_prefix` is a finite, kernel-checked comparison:
if W=U on N,...,q-1, q>=N>=2, and s dominates both caps on 2,...,N-1, then

```
L_W(s;q)-L_U(s;q) = sum_{2<=n<N} (U_n-W_n)*log((n+1)/n).
```

In particular, fixing a genuinely finite initial arithmetic prefix and using
P afterward contributes a constant once s exceeds those finitely many caps.
It cannot change the written linear asymptotic deficit. This is not a proposal
to increase the exact prefix indefinitely.

### Why parity does not change the leading deficit (written)

Let G be the uncapped greedy sequence `G_n=min(P(n),G_(n-1)+c_n)`.
For nonnegative c, the capped sequence satisfies `C_n=min(s,G_n)`, by induction.
For all sufficiently large odd n,

```
c_n=log(n)/sqrt(n) >= P(n)-P(n-2).
```

There is some odd index at which G reaches P. Indeed, if no sufficiently large
odd index reached P, no preceding even index could reach P either (the displayed
inequality would force the following odd index to do so). With neither cap
active, G would eventually equal a constant plus the sum of c_n, which grows
as sqrt(n)*log(n), contradicting G_n<=P(n)=O(sqrt(n)).
After its first sufficiently large odd contact, every subsequent odd index
has G_n=P(n). At an intervening even index,

```
0 <= P(n)-G_n <= P(n)-P(n-1)=O(n^(-1/2)+(log n)/n).
```

Therefore `sum_{n>=2} (P(n)-G_n)*log(1+1/n)` is finite. The 1-Lipschitz property
of min(s,.) bounds the parity improvement by this s-independent constant.
For feasible q, C_q=s, so no omitted terminal tail invalidates this comparison.
Thus parity has the SAME written normalized limit and an unbounded negative
deficit. This conclusion is about these two relaxations only, not all sieves
or all uses of parity/arithmetic structure.

The synthetic scalar-state checks use no primes. At s=100,300,1000,3000,10000,
the parity gains are approximately 53.23085,53.25885,53.26539,53.26689,53.26737.
These are evidence consistent with the written bounded-improvement argument,
not a certified limiting constant.

### Exact missing formal bridges

The Big-O inversion of P, the uniform sum/integral remainder bound, the
archimedean-dual Big-O adapter, and summability of the uncapped parity-greedy
deficit are not formalized here. In particular there is no Lean theorem
claiming the normalized limit or a uniform numerical threshold. The completed
finite theorems do not depend on any of these written statements.

## Next actual arithmetic information

The P-only relaxation fills mass too early; the parity constraint corrects
only a bounded initial/alternating defect in that filling. A useful next
candidate must constrain mass placement on the growing scale n comparable to
s^2, not merely amend a fixed prefix. One precise independent arithmetic
input to investigate is a lower bound on the weighted tail

```
sum_{n<k<=q} Lambda(k)/sqrt(k)
```

uniformly for a specified macroscopic range of n/q, with explicit constants
and a stated threshold. A concrete next proposition to test is an explicit Q
such that, for every integer q>=Q and integer q/4<=n<=q/2, the displayed tail
is at least `(199/100)*(sqrt(q)-sqrt(n))`. This is a proposed arithmetic theorem,
not a result of this branch; its reserve adequacy is not asserted. Subtraction
from the retained terminal s then yields
an upper cap on S_n that preserves correlation with s. Its integrated gain
over the current cap must be measured with the exact layer weights; the
written leading deficit to overcome is `2 log(log 4)*s`, before lower-order
errors and the actual reserve can be addressed. No such new tail estimate is
assumed or wrapped in a new certificate here. A non-explicit global PNT
statement or a fixed 201/200 increment estimate is not an explicit uniform
recovery floor.

## Validation and handoff

The finite modules are `SuzukiCumulativeMoment.lean`, `SuzukiGreedyMoment.lean`,
and `SuzukiMomentBounds.lean`. Validation completed before the source commit:

- Full `lake build`: successful, 3,959 jobs.
- `lake env lean AuditSuzukiMomentBounds.lean`: all 34 audited declarations
  report exactly `[propext, Classical.choice, Quot.sound]`. The audit includes
  the new finite results and retained log(37), m=31, and strict one-percent
  failure certificates. No project-added axioms, `sorry`, `admit`, numerical
  oracles, `native_decide`, or unsafe proof shortcuts were introduced.
- `cabal build`, `cabal test`, `npm run typecheck`, `npm run build`: passed.
- `formal-status`, `garden`, `kernel`, `submission`: passed as tooling;
  submission remains negative. These metadata commands do not check proofs.
- `suzuki-event-regression` and `suzuki-event-report.mjs`: passed at the
  unchanged actual cutoff 9,999,993; 10,341 periods, 7,872 old affine passes,
  2,469 failures, maximum cost/surcharge residual 1.524e-9.
- `suzuki-surcharge-profile.mjs`: unchanged identity regressions passed;
  maximum ramp and integral residuals 8.882e-16 and 1.777e-15. These are
  floating-point consistency checks, not proof evidence.
- `suzuki-sieve-regression.mjs`: passed at the unchanged cutoff 19,999,999.
  Its sole data extension exports the already-computed terminal S and T.
- Both `suzuki-one-percent-witness.mjs ... --check` runs reproduced the
  existing generated files (1,186 and 2,986 rows), without modification.
- `suzuki-recovery-floor-regression.mjs` and the new
  `suzuki-moment-regression.mjs`: passed, including zero-mass, one-atom,
  infeasible-parity-total, same-dual, greedy-identity, and unfinished-tail
  checks. No new prime scan was introduced.
- `git diff --check`: passed. Pins, completed recovery-floor source, and
  `.codex/` are untouched.

The normal handoff is a source commit, then `cabal run rh-garden -- ui-export`,
validation of all four versioned JSON files and the UI, then a separate
snapshot commit. Exporter trust fields remain `not_checked_by_export` and do
not certify Lean builds or axiom audits.

**NO PROOF OF RH IS CLAIMED.**
