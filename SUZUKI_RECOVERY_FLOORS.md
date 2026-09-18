# Recovery floors and one-sided spectral growth

Future Technologies Laboratory LLC, September 2026.

Starting checkout: `0cae503b25e1f0ae5e22f53fd0fa710e185902f9`.
The live checkout matched the report; only the pre-existing untracked
`.codex/` was present. Dependency pins are unchanged.

**NO PROOF OF RH IS CLAIMED.**

## Result and information boundary

The new branch proves structural implications and equivalences for the
actual Suzuki function. It does not supply the uniform arithmetic floor
appearing in those equivalences. Qualitative recovery, the completed
surcharge branch, the two-scale transfer, and the countermodel are reused,
not re-proved or expanded.

The three source modules are:

- `SuzukiOneSidedGrowth.lean`: one-sided growth, poles, and zero-free strips.
- `SuzukiRecoveryFloor.lean`: actual minimum coverage and active-block adapters.
- `SuzukiRecoveryMarginBounds.lean`: an unconditional, explicit but inadequate
  arithmetic lower bound, with its scale deficit proved.

## One-sided growth of the ORIGINAL function

For `sigma >= 0`, `xiZeroFreeRightOf_of_suzukiPsi_exp_lower` proves

```
(exists C>=0, exists T>=0, forall t>=T,
  -C*exp(sigma*t) <= Psi(t))
  -> forall rho, xi(rho)=0 -> Re(rho)<=1/2+sigma.
```

Reflection gives `abs(Re(rho)-1/2)<=sigma`, through
`xi_strip_of_suzukiPsi_exp_lower`. At sigma zero,
`riemannHypothesis_iff_suzukiPsi_eventually_bounded_below` proves

```
RH <-> exists C>=0, exists T>=0, forall t>=T, -C<=Psi(t).
```

`riemannHypothesis_of_suzukiPsi_polynomial_lower` also proves RH from any
eventual lower bound `-C*(1+t)^N`, with `C>=0` and natural `N`. The elementary
exponential-series estimate used here has an explicit domination constant:

```
(1+t)^N <= (N! / sigma^N * exp(sigma))*exp(sigma*t),
sigma>0, t>=0.
```

These are implications from lower-bound PREMISES. Neither a bounded nor a
polynomial lower floor for the actual function is asserted.

### Transform and surviving pole

The function used in Landau is ordinary multiplication and addition:

```
f(t)=exp(-sigma*t)*Psi(t)+C,
G(z)=L(z+sigma)+C/z,
L(w)=logDeriv xi(1/2+w)/w^2.
```

It is not the special Volterra-transformed `suzukiPsiShifted sigma` family.
Only the already-proved **zero-parameter** identification is used to reuse
the original Laplace transform. The denominator is `(z+sigma)^2`, not `z^2`.

The initial transform and absolute convergence are proved for
`Re z>0` and `Re z+sigma>1/2`. `G` is meromorphic and analytic at every
positive real point when `sigma>=0`. Zero is a boundary point; no incorrect
removable value is assigned there.

At `z0=rho-1/2-sigma`, assuming `z0!=0` and `rho-1/2!=0`,
`suzukiDampedLaplaceContinuation_residue` proves the punctured limit

```
(z-z0)*G(z) -> xiMultiplicity(rho)/(rho-1/2)^2.
```

For a zero strictly to the right of `1/2+sigma`, the real part of `z0` is
positive, both denominators are nonzero, and the actual multiplicity is
positive. The analytic term `C/z` cannot cancel the pole. The reused
`meromorphicOrderAt_nonneg_of_eventual_nonneg` applies the generic eventual-
sign Landau principle, holomorphy of the absolutely convergent Laplace
integral, and meromorphic uniqueness. Its nonnegative-order conclusion
contradicts the nonzero residue. No RH or short-interval PNT is used.

## Actual finite-minimum coverage

Write `V(u)=Psi(2 log u)` and `D(u)=suzukiRootSlopeDiscrepancy u`.
`SuzukiFirstRecovery(a,b)` means

```
a<b, D(b)=0, forall v in [a,b), D(v)<0.
```

`SuzukiRecoveryEndpoint(U,b)` additionally supplies a negative anchor
`a>=U`. For `U>=sqrt(2)` and `u>=U`,
`suzukiPsiRoot_minimum_covered_by_recovery` proves

```
exists c, (c=U or SuzukiRecoveryEndpoint(U,c)) and V(c)<=V(u).
```

The proof chooses an actual positive-discrepancy `R>u` and minimizes the
continuous Psi on the logarithmic image of `[U,R]`. A left-sided minimum
has nonpositive post-jump discrepancy, excluding the terminal `R`. At an
interior minimum, the right derivative is nonnegative, so `D=0`.

At a nonzero Mangoldt event, the left derivative exceeds the right one by
`Lambda(q)/sqrt(q)>0`; the two minimum conditions are incompatible. Thus
the minimum is strictly inside a COMPLETE Mangoldt block. Strictly
increasing smooth slope supplies a negative anchor immediately to its left
and a first recovery at the minimum. Zero-arrival integer boundaries stay
inside that same block. No global continuity of D, no pre-jump zero, and no
termwise differentiation of the xi series is used.

The witness `c` can exceed `u`. This is essential, not a coverage gap.

## Constant floors, equivalence, and dichotomy

`suzukiPsiRoot_ge_min_of_recovery_floor` proves

```
(forall b, RecoveryEndpoint(U,b) -> -B<=V(b))
  -> forall u>=U, min(V(U),-B)<=V(u),  U>=sqrt(2).
```

This transfer itself does not even need `B>=0`. The existence criterion
uses nonnegative B:

```
RH <-> exists U>=sqrt(2), exists B>=0,
  forall b, RecoveryEndpoint(U,b) -> -B<=V(b).
```

The theorem is `riemannHypothesis_iff_bounded_recovery_floor`.
`arbitrarily_deep_recoveries_of_not_RH` gives the precise contrapositive:
if RH is false, then after every `U>=sqrt(2)`, for every `B>=0`, there are
`a>=U` and `b>a` with a negative starting state, actual first recovery at b,
and `V(b)<-B`. It asserts no time bound, density, or growth rate.

**Scale warning:** a bound `V(b)>=-C*b^p`, or one polynomial in `log b`,
cannot be transferred backward to u by substituting u for b. No such
substitution appears in the proofs. Only the constant floor transfers
without a recovery-time relation.

## Existing dual margin and the cutoff adapter

`recoveryEndpoint_active_block` proves that EVERY actual recovery in the
stated domain lies strictly inside an active complete block `(q,r)`, with

```
log q < t=2 log b < log r,
t = suzukiArchDualOptimizer(S_q),
A'(t)=S_q,
V(b)=T_q-A_star(S_q)=suzukiGlobalDualMargin(q).
```

It reuses both existing active-block margin/optimizer identities. It does
not extrapolate the unrestricted optimizer into an inactive cell.

The corrected arithmetic target remains

```
exists B>=0, exists N,
forall q r, q>=N -> IsActiveMangoldtBlock(q,r) ->
  T_q-A_star(S_q)>=-B.
```

`recovery_floor_of_active_block_tail` handles the cutoff explicitly:
choose a proved prime event `p>=max(N,2)` and use `U=sqrt(p)`. A recovery
after U cannot lie in a block with `q<p<r`, because event-completeness would
force `Lambda(p)=0`. Therefore its active block has `q>=p>=N`.
This is an existential event-cutoff adapter; it does not assume that an
arbitrary integer N is an event or that its straddling block is already
covered. No finite-prefix positivity extension is needed for an eventual
boundedness criterion. Existing positivity through log(37) is unchanged.

`riemannHypothesis_iff_active_block_tail_floor` proves the target is
RH-equivalent. The reverse direction uses the event-cutoff adapter and
minimum coverage. The forward direction uses the already-proved RH-to-Psi
nonnegativity implication, with B=0. The target itself is NOT supplied.

## A proved arithmetic attempt and its quantitative deficit

The first estimate keeps mass and logarithmic moment correlated:

```
T_q-log(2)*S_q
  = sum_{1<=n<=q} Lambda(n)/sqrt(n) * (log(n)-log(2)) >= 0.
```

The n=1 term vanishes; all other terms are nonnegative. At an actual active
optimizer, substitute `S_q=A'(t)` only inside its valid block. This gives
the unconditional smooth bound

```
T_q-A_star(S_q) >= A(t)-(t-log(2))*A'(t).
```

Next use the proved archimedean bound with `kappa=151/20000` and the pinned
global Chebyshev estimate

```
A(t)>=kappa*(exp(t/2)-1),
S_q<=2 log(4)*sqrt(q)+2 log(q)+(log(q))^2/2.
```

Since `log q<t`, the fully explicit bound is

```
F(t)=kappa*(exp(t/2)-1)
  -(t-log(2))*(2 log(4)*exp(t/2)+2t+t^2/2),
V(b)>=F(2 log b).
```

`active_margin_ge_correlated_support`, `active_margin_ge_explicit_floor`,
and `recovery_reserve_ge_explicit_floor` establish these inequalities with
actual proof terms. Their inputs are nonnegative actual Mangoldt weights,
the active-state equation, and proved global bounds; they do not read any
unknown local prime table, fit an error to samples, or impose a measured
recovery length.

This attempt is quantitatively inadequate. `recoveryExplicitFloor_le_neg_exp`
proves `F(t)<=-exp(t/2)` for `t>=2`.
`explicit_floor_unbounded_on_actual_recoveries` proves that for every B and
cutoff there is an ACTUAL recovery b with `F(2 log b)<-B`. This statement is
about the ESTIMATE, not the actual reserve, which is bounded BELOW by F.
The expression's leading magnitude is `2 log(4)*t*exp(t/2)`; in root
coordinates it is of order `b log b`, not a constant floor. The leading-
term description is ordinary written asymptotic analysis; the displayed
inequalities and unboundedness witnesses are the kernel-checked statements.

The sharper already-proved state-local curvature estimate is also reused:

```
T_q-A_star(S_q) >= V(sqrt(q))
  -(max(-D(sqrt(q)),0))^2 / ((5/3)*sqrt(q)).
```

`active_margin_ge_existing_curvature_energy` applies it only to active
blocks. This retains the signed left state and actual left reserve; no
uniform lower bound for those quantities is inferred. It is much sharper
on retained finite examples, but obtaining all its sharpness from measured
states is finite verification, not an independent tail estimate.

### Other proved candidates audited, not upgraded

The pinned `MediumPNT` actually supplies an existential `c>0` and Big-O
error `x*exp(-c*(log x)^(1/10))`, NOT the stronger square-root logarithmic
exponent. It gives no displayed numerical threshold or Big-O constant.
The existing finite global-error transfer, for `rho*m<=h<=m/8`, gives

```
I_m(m+h) <= delta*(1+6/rho)*C_m(m+h),
V(sqrt(m+h)) >= V(sqrt(m))+D(sqrt(m))*log(1+h/m)
  -Adef_m(m+h)-delta*(1+6/rho)*C_m(m+h).
```

The global error hypothesis and signed reserve are not discarded. This
does not bound that reserve uniformly and only gives the already-proved
fixed-relative-width regime. Even a suitable reserve-error transfer of
size `exp(t/2-c*sqrt(t))` would remain larger than every polynomial in t;
the pinned exponent 1/10 has the same obstruction. Such a reserve-error
transfer is not silently claimed as a new Lean theorem here.

The separate all-interval `201/200` increment theorem still has no proof
or explicit prime threshold in this checkout. Neither its fixed density
coefficient nor qualitative recovery supplies a constant recovery floor.
These failures of available estimates are not an impossibility theorem
for all correlated-moment estimates.

## Numerical regression, not a proof

The new script reads the retained event and sieve diagnostics and performs
NO new prime scan. It checks the bounds only as IEEE-754 regressions; the
Lean proofs are authoritative. Measured endpoints are validation inputs,
not presumed universal interval limits.

| Excursion start | Actual recovery square | Reserve | Smooth support floor | Explicit F | State-local curvature floor |
|---|---:|---:|---:|---:|---:|
| 31 | 34.489536036595 | 0.029786900 | -15.5172 | -84.3413 | 0.026284946 |
| 324431 | 361197.640341523 | 0.035817616 | -12150.5542 | -21465.5602 | 0.035817517 |
| 8573249 | 8906232.48818665 | 0.040498608 | -79443.1739 | -129100.1162 | 0.040498600 |

Their final active blocks are respectively `(32,37)`, `(361183,361201)`,
and `(8906197,8906237)`. Next-event labels are not recovery coordinates.
Approximate curvature gaps are 0.00350195, 9.89e-8, and 7.74e-9; the last
two are sensitive to the retained floating-point evaluation error.

The two one-percent failures are retained. The interval
`19999981 -> 19999999` remains explicitly unfinished, with negative terminal
discrepancy approximately -0.13702537794. No recovery endpoint has been
computed for it by this branch.

## Validation and next independent input

Validation completed before the source commit:

- Full `lake build`: successful, 3,956 jobs.
- `lake env lean AuditSuzukiRecoveryFloor.lean`: all 34 audited declarations
  report exactly `[propext, Classical.choice, Quot.sound]`. This includes
  the principal new results and the retained initial-interval, m=31,
  log(37), and two strict one-percent failure certificates. No project-added
  axiom, `sorry`, `admit`, numerical oracle, or unsafe proof shortcut was added.
- `cabal build`, `cabal test`, `npm run typecheck`, and `npm run build`: passed.
- `formal-status`, `garden`, `kernel`, and `submission`: passed as tooling;
  the submission status remains negative. The metadata commands themselves
  do not check Lean proofs.
- `suzuki-event-regression` and `suzuki-event-report.mjs`: passed at the
  unchanged actual cutoff 9,999,993, with 10,341 periods, 7,872 old anchored
  passes and 2,469 old failures. The exact-cost/surcharge residual is below
  1.53e-9; this floating-point residual is not proof evidence.
- `suzuki-surcharge-profile.mjs`: retained identity regressions passed
  (ramp residual below 8.89e-16; integral residual below 1.78e-15). This is
  validation of the unchanged branch, not a new surcharge result.
- `suzuki-sieve-regression.mjs`: passed at its unchanged cutoff 19,999,999,
  preserving short-prefix, cutoff-straddling, strict-failure, and unfinished
  terminal checks. Both `suzuki-one-percent-witness.mjs ... --check` runs
  reproduced the existing generated proof data without changes.
- `suzuki-recovery-floor-regression.mjs`: passed against regenerated baseline
  diagnostics, with no new prime scan. Its outputs remain NumericalEvidence.
- `git diff --check`: passed; dependency pins and `.codex/` are untouched.

The normal handoff is a source commit, then `cabal run rh-garden -- ui-export`,
validation of all four versioned JSON files and the UI, then a separate
snapshot commit. Export status fields remain `not_checked_by_export`; an
export is not a Lean build or an axiom audit.

The next genuinely independent arithmetic input is a uniform bound on the
correlated moment deficit `A_star(S_q)-T_q`, restricted to active complete
blocks beyond a justified cutoff. The theorem above now precisely identifies
its RH strength. Neither an uninhabited premise nor the failure of our coarse
explicit F supplies that input. A smaller useful step is an effective
correlated-moment remainder in a specified active-block regime that improves
the exponentially growing lower-floor error without replaying exact unknown
future samples. Its quantifiers, constants, and remaining reserve terms must
be stated before it can be used as a tail bound.

**NO PROOF OF RH IS CLAIMED.**
