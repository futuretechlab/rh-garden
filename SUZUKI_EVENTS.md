# Finite Suzuki event certificates

Future Technologies Laboratory LLC. Research continuation, 2026-09-16.

NO PROOF OF RH IS CLAIMED.

## Authoritative baseline and trust categories

The starting checkout was `4d19a0d645f35e91b4899aab88c847e815786248`, not
the reported `7c23cea49f2106ec260d74bac8cfb3aaabe48735`. Its preceding commits
had already supplied exact cell costs and a block-chain verifier, and had
closed the initial interval. No dependency was changed: Lean is
`v4.33.0-rc2`, mathlib is `51e6992efd06126df61a496bebf8f49482a4e129`, and
Zeta23 is `2bafb8c88f177284a2123b5fefa2ff84e2365eb6`.

The additions distinguish:

1. Unconditional structural theorems: complete finite partitions, signed
   dynamics, analytic gluing, finite sample integration, and event-log bounds.
2. An inhabited concrete Lean certificate: events `3,4,5`, including the
   prime-square arrival, proving nonnegativity on `[sqrt 3,sqrt 5]`.
3. Conditional criteria: finite event/reserve/cost bounds imply interval
   nonnegativity; the existing tail field is still an explicit hypothesis.
4. Numerical evidence: all Haskell `Double` values, root bisections and JSON.
   Neither upward decimal rounding of an approximate sample nor a small
   integration residual is a proved outward bound.
5. The missing universal arithmetic theorem: no all-height family of adequate
   event bounds and reserve comparisons is proved.

## Signed dynamics and finite analytic obligations

Use `A(t)=suzukiPsiArchimedean(t)`, `S(u)=suzukiRootArchSlope(u)`,
`D(u)=suzukiRootSlopeDiscrepancy(u)`, `B(u)=max(-D(u),0)`,
`Service(r,u)=S(u)-S(r)`, `a=sqrt(m)`, `z0=-D(a)`, and
`E_m(u)=Arrival((m,floor(u^2)])-Service(a,u)`.

The previously checked identity is `z0+E_m(u)=-D(u)` for `m>=1,u>=a`.
It never replaces the signed `z0` by `B(a)`. The previous
`rootSlopeBacklog_eq_chebyshevProfile` does require `D(a)<=0`; the previous
busy-period loss equality requires a negative excursion. The new all-prefix
inequality below requires neither sign hypothesis.

`SuzukiEventPartition.lean` adds `SuzukiEventChain m n`, including an empty
chain and arbitrary integer endpoints. Its cells are strictly ordered and
prove that every interior integer has zero von Mangoldt value.
`SuzukiEventChain.exists_canonical` says, for every `m<=n`, a chain exists
whose finite point set is exactly `suzukiMangoldtEventPartition m n`:
the two endpoints and all nonzero-von-Mangoldt integers between them.
`event_mem` proves completeness for every prime power, independently of the
exploratory sieve. A non-event terminal has zero arrival, explicitly checked
by `signedRootState_nonEvent_terminal` and the concrete terminal `6` test.

For each cell `[sqrt(q),sqrt(r))`, arrivals are constant and

```text
E_m(u) = E_m(sqrt(q)) - Service(sqrt(q),u),
z_m(sqrt(r)) = z_m(sqrt(q)) - Service(sqrt(q),sqrt(r)) + Lambda(r)/sqrt(r).
```

The left state already includes its arrival; the anchor is excluded from
the arrival sum. The right endpoint's arrival is charged in the next cell.
Values at the right endpoints do not affect interval integrals.

`integral_weighted_backlog_eventFree_eq_cost`, for `q>=2` and an event-free
cell `q<r`, states exactly

```text
integral_[sqrt(q),sqrt(r)] (2/u)*B(u) du
  = ExactCost(sqrt(q),sqrt(r),-D(sqrt(q))).
```

The continuous service envelope is interval integrable; finite gluing proves
`SuzukiEventChain.backlog_integrable` and `backlog_aestronglyMeasurable`
(with the closed-interval restricted Lebesgue measure). For any such chain,
`m>=2` and `sqrt(m)<=u<=sqrt(n)`, `loss_le_backlog_integral` gives

```text
PsiRoot(sqrt(m))-PsiRoot(u) <= integral_[sqrt(m),u] (2/v)*B(v) dv.
```

This is net loss bounded by cumulative downward variation, not an equality.
The density is nonnegative, so its full-interval integral bounds every
prefix integral, even when recovery occurs inside a cell.

`SuzukiFinitePartitionCertificate.nonnegative` takes only a finite complete
chain, left-event bounds `E_m(sqrt(q_i))<=e_i`, cell-cost bounds
`ExactCost(r_i,r_(i+1),z0+e_i)<=c_i`, a reserve bound
`reserve<=PsiRoot(a)`, and `sum c_i<=reserve`. It proves
`0<=PsiRoot(u)` for **every** `u` in the closed root interval.
There is no continuous error-envelope field, integrability field,
negative-excursion field, or continuum of prefix-loss fields.
`toBusyPeriodCertificate` fills the established interface without changing
its meaning. Domain bounds `m>=2` and completeness are still necessary for
the proved service estimates and the absence of unaccounted arrivals.

## Exact weighted cost and conservative alternatives

For `sqrt(2)<=r<=s`, `C(u)=max(K-Service(r,u),0)`, and the unique active
endpoint `h` in `[r,s]`, the reused kernel-checked formula is

```text
integral_[r,s] (2/u)*C(u) du
  = 2*(K+S(r))*log(h/r) - A(2*log(h)) + A(2*log(r)).
```

`h=r` if `K<=0`; `h=s` if `K>=Service(r,s)`; otherwise strict increase
of `S` and the intermediate value theorem give the unique solution
`Service(r,h)=K`. The expression is zero at `h=r`. The proof uses the chain
rule `d/du A(2 log u)=(2/u)S(u)` and positive-part case splitting.
These results already existed in the actual baseline and are reused.

The `5/3` service lower bound gives a conservative linear envelope with
`hL=r` for `K<=0`, otherwise `min(s,r+3K/5)`, and cost

```text
2*(K+5*r/3)*log(hL/r) - (10/3)*(hL-r).
```

New `exactServiceCellCost_le_quadratic` proves the convenient upper bound
`ExactCost(r,s,K)<=K^2/(c*r)` if `K>=0,c>0` and
`Service(r,u)>=c*(u-r)` throughout the cell. This last inequality is an
upper estimate, not the exact weighted integral. The concrete proof uses
the newly proved `c=19/10` bound on `u>=sqrt(3)`.

## Finite arithmetic inputs and cancellation

`SuzukiEventArithmetic.lean` proves the exact event-free error kernel and its
integrability. Writing `R(x)=psi(x)-x`, an event-free cell satisfies

```text
R(x) = q+R(q)-x       (q<=x<r),
integral_[sqrt(q),sqrt(r)] R(u^2)/u^2 du
  = (q+R(q))*(1/sqrt(q)-1/sqrt(r)) - (sqrt(r)-sqrt(q)).
```

For a complete Mangoldt block chain, let `J(rho)` be the finite sum of these
elementary pieces with `R(q)` replaced by `rho(q)`. The theorem
`SuzukiMangoldtBlockChain.arrivalServiceExcess_le_jumpSamples` needs just the
finite left-sample bounds and the terminal sample bound. It concludes

```text
E_m(sqrt(n)) <= rho(n)/sqrt(n) - R(m)/sqrt(m)
                 + J(rho) + ArchDefect(sqrt(m),sqrt(n)).
```

The lower anchor term remains exact. `transformed_uniform_sample_allowance`
proves that using `rho(q)=R(q)+delta` changes the entire transformed
expression by exactly `delta/sqrt(m)`. Nonuniform allowances between zero
and `delta` are bounded by the same amount using monotonicity. The Explorer
keeps the anchor sample exact and propagates every other allowance through
both the endpoint and integral terms, then through the cell costs.

A separate unconditional arithmetic coarsening is
`SuzukiEventChain.excess_le_logArrival_sub_service`:

```text
E_m(sqrt(n)) <= sum_[m<q<=n, Lambda(q)!=0] log(q)/sqrt(q)
                - Service(sqrt(m),sqrt(n)).
```

It follows from the pinned `vonMangoldt_le_log`, charges only actual events,
and excludes the anchor. It is exact at primes but conservatively overcharges
prime powers. No asymptotic PNT constant or RH-strength assumption enters.
The previously pinned coarse local-width bound is also tested, not retuned.

## Concrete proof terms

`psiRoot_sqrt_three_reserve` proves `43/1000<=PsiRoot(sqrt(3))`, from a
20-term nonnegative archimedean series truncation and rational analytic
bounds. It does not assume positivity of the target interval.
`neg_discrepancy_sqrt_three_le` proves `-D(sqrt(3))<=1/3`;
`neg_discrepancy_sqrt_four_le` proves `-D(2)<=9/50`, with
`Lambda(4)=log(2)` in the signed recurrence.

`suzukiFinitePartitionCertificate_three_five` is an actual inhabited value:

| Cell | Finite event bound | Cell-cost upper bound |
| --- | --- | --- |
| `[sqrt(3),2]` | `e_3=0` (exact anchored excess) | `34/1000` |
| `[2,sqrt(5)]` | `e_4=D(sqrt(3))+9/50` | `9/1000` |

The second signed-state envelope is genuinely conservative; the two costs
sum to the proved `43/1000` reserve. Prime events `3,5` and the prime-square
event `4` are present. `suzukiPsiRoot_nonnegative_three_five` applies the
finite verifier; `suzukiPsi_nonnegative_zero_to_log_five` joins the previously
proved initial interval. `suzukiPrefixFivePlusTail` fills the prefix of the
existing exact-prefix-plus-tail certificate and still requires explicitly
`forall t>=log(5), 0<=suzukiPsi(t)`. No global certificate is constructed.

The proposed initial proof was already present at the starting commit:
`suzukiPsiArchimedean_ge_exp_sub_one` proves
`A(t)>=(151/20000)*(exp(t/2)-1)` for `t>=0`,
`suzukiInitialNonnegative_proved` inhabits `SuzukiInitialNonnegative`, and
`suzukiPsi_pos_zero_to_log_three` proves strict positivity on `(0,log(3)]`.
These were audited, not duplicated or promoted as new work.

## Numerical regression and reproducibility

Run from the repository root:

```text
cabal run rh-garden -- suzuki-event-regression .cabal-work/event-diagnostics.json
node scripts/suzuki-event-report.mjs .cabal-work/event-diagnostics.json
```

The exact configured `t_max=16.118095` gives actual integer cutoff
**9,999,993**, not 10,000,000. It reproduces 10,341 completed periods and
the old affine count 7,872 passing / 2,469 failing. The corrected rounded
sample envelope passes numerically on all 10,341; the unconditional
event-log coarsening passes 10,340; the local-width bound passes 10,147.
Maximum exact-cost/net-loss residual is `1.524e-9`; maximum rounded-envelope
cost excess over exact-state cost is `4.8613e-6`.

The separate `ui-export` scan uses `t_max=log(10000000)` and reports its
actual cutoff **10,000,000** explicitly in the JSON. It also contains 10,341
completed periods. The refreshed four-file snapshot was JSON-validated and
the production UI rebuilt successfully; it identifies source commit
`b681424e0f3e033ccf8a25859551a8f134ad9d14`. The exporter deliberately does
not infer formal-build or test success from a static metadata label.

Important correction to the earlier report: its displayed rounded samples
were not propagated into its cost calculation. Those earlier costs were
**exact-state** costs. The new exporter separates those from the genuinely
conservative transformed-sample envelope costs below.

| Diagnostic | `324431 -> 361201` | `8573249 -> 8906237` |
| --- | ---: | ---: |
| Event count / full exported rows | 2888 / 2889 | 20836 / 20837 |
| Old terminal slack | 0.610118882679 | 1.262018614446 |
| Old constant-prefix slack | -0.075697414664 | 0.763124429424 |
| Old affine slack | -2.152672822854 | -6.959435462548 |
| Starting reserve | 0.067287445205 | 0.048549657324 |
| Exact-state weighted cost | 0.031469829319 | 0.008051052220 |
| Rounded-sample envelope cost | 0.031469922417 | 0.008051058653 |
| Envelope cost gap | 9.3099e-8 | 6.433e-9 |
| Maximum transformed-excess gap | 1.751880e-6 | 3.410910e-7 |
| Linear-envelope cost | 0.031788344297 | 0.008080368955 |
| Rounded-envelope reserve remaining | 0.035817522787 | 0.040498598671 |
| Event-log cost | 0.034507827849 | 0.008331630521 |
| Event-log reserve remaining | 0.032779617356 | 0.040218026802 |
| Local-width cost | 40.059791098690 | 32.282518019581 |
| First local-width failing cell | 325891 | 8586031 |

Neither required case has a rounded-sample or event-log failure. At the
first local-width failing cells, actual excess / arithmetic upper bound are
`0.288651505135 / 29.978337911510` and
`0.083809909222 / 65.332966297554`. Cumulative costs exceed the respective
reserves by `0.000030442357` and `0.000314337108`. The failure is the
arithmetic envelope's total-cost budget, not integration approximation or
a substituted reserve lower estimate. No claim about actual negativity
follows. Full rows record outgoing service, weighted costs, actual excess,
each upper bound, cumulative rounded cost, reserve, and the first failure.

Tests cover zero-width cells, nonpositive signed states, right-endpoint
cutoffs, an interior recovery, a prime-square arrival, and actual event
states whose service surplus would be destroyed by a reflected recurrence.

The sole event-log failure is `31 -> recovery before 37`, at cell `32`.
Here `Lambda(32)=log(2)`, but the coarsening pays `log(32)=5*log(2)`.
The true event excess is `-0.055641795358`, the bound is `0.434487276376`;
total envelope cost `0.065654131799` exceeds reserve `0.058720526098` by
`0.006933605701`. Exact-state cost is only `0.028933626483`. This is a
specific prime-power arithmetic overcharge, not a failure of the dynamics
or a counterexample to positivity. It is retained in the full regression
export, rather than dropped from the pass count.

## Next explicit universal arithmetic target (open)

**Subsequent audit:** [SUZUKI_SURCHARGE.md](SUZUKI_SURCHARGE.md) proves that
this target is exactly `J_m(b) <= V(b)` on a negative excursion. The `m=31`
failure is now a kernel-checked counterexample to the unrestricted target,
while true positivity is proved through `log 37`. The proposed threshold
`37` below is not established by this audit or by the extended scan.

For a complete negative excursion starting just after an event `m`, let
`a=sqrt(m)` and `b` be its first recovery root. Set

```text
L_m(q) = sum_[m<k<=q, Lambda(k)!=0] log(k)/sqrt(k),
K_m(q) = -D(a) + L_m(q) - Service(a,sqrt(q)),
V_m = A(log(m)) - sum_[k<=m] (Lambda(k)/sqrt(k))*log(m/k).
```

The sharply specified sufficient target is, for all such excursions with
`m>=37`,

```text
sum_[cells q_i before b]
  ExactCost(sqrt(q_i), min(sqrt(q_(i+1)),b), K_m(q_i)) <= V_m.
```

The constants and profile here are fixed, not an existential unspecified
continuous upper bound: `V_m` is the exact prime-side starting reserve and
`L_m` is an independently proved conservative event-local arrival sum.
The cutoff `37` isolates the observed `31` obstruction, not a proved
threshold for the infinite statement. This is an **unproved research
target**; the finite scan does not imply it, and later failures are possible.
It is stronger than the required positivity bound, because it charges
prime-power overestimates and cumulative downward variation. An explicit
weighted short-interval prime-power estimate controlling these finite costs
is still missing from the pinned ingredients. Finite prefix proofs and
adequate reserve propagation would also have to accompany a universal route.

## Validation and proof trust

The full pinned `lake build` succeeded (3892 jobs). `cabal build`,
`cabal test`, `npm run typecheck`, `npm run build`, and the established
`formal-status`, `garden`, `kernel`, and `submission` commands succeeded.
`formal-status` is metadata, not a replacement for kernel checking.
The submission command still reports `Kernel proof term absent` and
`NO PROOF OF RH IS CLAIMED.` Existing deprecation/linter warnings remain.

`lake env lean AuditSuzukiEvents.lean` audits 17 principal declarations,
including the canonical partition, signed terminal, loss inequality,
measurability, finite verifier, both exact cost formulas, sample transform,
event-log bound, actual reserve and certificate, extended prefix, and
previous initial theorem. Every declaration reports exactly

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms, not new project assumptions. No
`sorry`, `admit`, project-added axiom, numerical oracle, or unsafe proof
shortcut was introduced. Dependency pins and the pre-existing untracked
`.codex/` directory are preserved.
