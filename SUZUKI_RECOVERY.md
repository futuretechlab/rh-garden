# Qualitative Suzuki discrepancy oscillation and recovery

Future Technologies Laboratory LLC, September 2026.

Starting checkout: `276597637639d5a14cba329685f3324f6505464f`.
The live checkout matched the report. Only the pre-existing `.codex/` was
untracked. Lean, mathlib, and Zeta23 pins are unchanged.

**NO PROOF OF RH IS CLAIMED.**

Continuation: [recovery floors and one-sided spectral growth](SUZUKI_RECOVERY_FLOORS.md)
classifies the uniform reserve floor that would suffice. Its proved equivalence
does not supply that arithmetic floor or change this qualitative theorem.

## Mathematical result and its scope

Write `Psi(t) = suzukiPsi t` and
`D(u) = suzukiRootSlopeDiscrepancy u`, with the existing right-continuous
signed Mangoldt state. The new theorems concern these actual functions,
not a model or an assumed arithmetic envelope.

`suzukiRootSlopeDiscrepancy_cofinal_pos` and
`suzukiRootSlopeDiscrepancy_cofinal_neg` say, respectively:

```
U >= sqrt(2) -> exists u > U, D(u) > 0;
U >= sqrt(2) -> exists u > U, D(u) < 0.
```

`suzukiRootSlopeDiscrepancy_first_recovery` says:

```
a >= sqrt(2), D(a) < 0 ->
exists b > a, D(b) = 0 and forall u in [a,b), D(u) < 0.
```

The corresponding uniqueness theorem compares any two such first zeros.
There is no effective bound for `b`, the depth of the excursion, its
weighted loss, or the reserve at recovery. Neither this result nor a
completed finite excursion scan proves Suzuki positivity.

## Forward difference and the real-axis extension

`SuzukiForwardDifference.lean` defines
`f_ell(t) = Psi(t+ell)-Psi(t)`. It is continuous. For `ell >= 0` and
`Re z > 1/2`, absolute convergence and the existing translated-tail split
give

```
L(z) = logDeriv xi(1/2+z)/z^2,
H_ell(z) = (exp(ell*z)-1)*L(z)
           - exp(ell*z)*integral[0,ell] Psi(v)*exp(-z*v) dv.
```

The formal transform theorem is
`complexLaplaceIntegral_suzukiForwardDifference`. No termwise
differentiation of the zero series is performed. Its convergence proof
reuses the already-proved exponential majorant through the initial
Laplace-convergence theorem.

The definition `suzukiForwardLaplaceContinuation` uses the product of
two **divided differences** (`dslope`): one for `exp(ell*z)` and one for
`logDeriv xi(1/2+z)`. The functional equation gives `xi'(1/2)=0`;
the already-proved `xi(1/2) != 0` makes the centered logarithmic
derivative analytic there. Thus the assigned value really is

```
H_ell(0) = ell*xi''(1/2)/xi(1/2) - integral[0,ell] Psi(v) dv.
```

The integral is written as the equivalent complex-valued compact initial
transform in Lean. Away from zero the definition equals the displayed
quotient. `analyticAt_suzukiForwardLaplaceContinuation_real` proves
analyticity at **every** real argument, not merely positive arguments.
The compact correction is entire. This avoids the incorrect zero value
of a totalized quotient.

## Zero existence, multiplicity, and the shifted Landau argument

`xiZeroOccurrence_nonempty` uses the existing occurrence-indexed Suzuki
series. An empty occurrence type would give `Psi(log 2)=0`, contradicting
`suzukiPsi_pos_zero_to_log_three`. It uses neither RH nor an imported
numerical zero.

For an occurrence `rho`, no-real-zeros gives `Im rho != 0`. Set
`z0=rho-1/2` and `ell=pi/abs(Im rho)`. The exponential `exp(ell*z0)`
has zero imaginary part and negative real part, so it is not one.
The critical strip, not the critical line, places `Re(z0+1)>0`.

The existing analytic-order proof in `XiNevanlinna.lean` is refactored
to expose its multiplicity calculation as
`tendsto_mul_logDeriv_riemannXi`:

```
(s-rho)*logDeriv xi(s) -> xiMultiplicity(rho), as s -> rho, s != rho.
```

The original no-finite-limit theorem is recovered from that calculation;
its statement is unchanged. The forward continuation has residue

```
xiMultiplicity(rho) * (exp(ell*z0)-1) / z0^2,
```

proved by `suzukiForwardLaplaceContinuation_residue`, with nonvanishing
in `suzukiForward_residue_ne_zero`. No simplicity of the zero is assumed.

If `c*f_ell` is eventually nonnegative for nonzero real `c`, apply Landau
to `g(t)=c*exp(t)*f_ell(t)`. Its continuation is `c*H_ell(z-1)`.
It is analytic at every positive real argument and initially converges
for `Re z > 2`. The existing eventual-sign Landau principle supplies
absolute convergence for every positive real parameter. The Laplace
integral is consequently holomorphic on `Re z > 0`. Meromorphic
uniqueness propagates the transform identity there, contradicting the
surviving pole at `z0+1`.

Both `c=1` and `c=-1` are used. The positive exponential shift is essential:
a pole on the imaginary axis would not contradict holomorphy only in the
unshifted open right half-plane.

`suzukiForwardDifference_cofinal_signs` gives a single `ell>0` for which
both signs occur after every real `T`. In particular, `Psi` is neither
eventually nondecreasing nor eventually nonincreasing.

## Finite calculus and first recovery across jumps

`SuzukiRootRecovery.lean` proves, for `log 2 <= a <= b`,

```
Psi(b)-Psi(a) = integral[a,b] D(exp(t/2)) dt.
```

This is `suzukiPsi_sub_eq_integral_rootDiscrepancy`. Integrability is
proved, not assumed: the smooth archimedean derivative is continuous on
the compact interval and the accumulated Mangoldt slope is monotone.
The right derivative of `Psi` includes the arrival at an event. The
right-derivative form of the fundamental theorem glues the finite cells.
Positive/negative forward integrals then give actual positive/negative
discrepancy witnesses at arbitrarily large roots.

The recovery proof takes the infimum of the nonnegative states after
the anchor, bounded above by a cofinal positive witness. It proves
right continuity from local constancy of `floor(u^2)` on the right and
uses

```
D(v)-D(u) <= S(v)-S(u),  0 <= u <= v.
```

This is a no-upward-jump inequality, not a global continuity assertion.
Right continuity forces the infimum's state to be nonnegative; the
inequality and continuity of `S` force it to be nonpositive. An event
whose **left limit** is zero but whose actual post-jump value is negative
cannot be selected. `first_recovery_has_finite_event_cover` supplies a
canonical event-complete cover from `floor(a^2)` through `floor(b^2)+1`.
The established completeness theorem accounts for every prime power.

`exists_completed_suzukiRootNegativeExcursion` supplies the existing
`IsSuzukiRootNegativeExcursion` interface with an actual endpoint.
`no_neverRecovering_suzukiRoot_excursion` rules out even eventual
nonpositive discrepancy. Existing busy-period and exact-prefix-plus-tail
certificate meanings are unchanged; no tail-safety field is erased.

## Remaining arithmetic and coverage requirements

Qualitative never-recovery is now discharged for the actual discrepancy.
The following are **not** discharged:

- Proved loss/depth bounds relative to the signed starting reserve.
- Nonnegativity of the recovery reserve, or universal Suzuki positivity.
- A numerically located recovery for the unfinished terminal scan period.
- Certified short prefixes and safe reanchoring at arbitrary cutoffs.
- An explicit threshold for the actual-prime `201/200` increment estimate.

The smallest useful independent arithmetic target remains a bound for
the correctly weighted anchored integral `I_m(x)`, uniform over every
real prefix in a stated regime, compatible with

```
V(sqrt(m)) + D(sqrt(m))*log(x/m) - Adef_m(x).
```

One sufficient next theorem is an independently proved all-real-anchor
increment bound `psi(m+t)-psi(m) <= (201/200)*t` for
`m^(3/5) <= t <= m/8` beyond a justified threshold. The completed
two-scale transfer is available. Even that theorem alone would not
compare its integral charge with the signed reserve or cover shorter
endpoints. No threshold has been guessed or raised in this sprint.

## Separate smooth countermodel

`SmoothCountermodel` is conspicuously separate from actual primes. Set

```
b(x)=1-1/(x*(x^2-1)), q(x)=b(x)+(1/4)*x^(-1/4),
Q(x)=integral[2,x] q(y) dy,
d(x)=d0+m^(1/4)-x^(1/4),
W(x)=R0+(d0+m^(1/4))*log(x/m)-4*(x^(1/4)-m^(1/4)).
```

The finite formal results check nonnegative arrivals for `x>=2`, the
all-length increment bound for `a>=50^4`, the matching smooth discrepancy
and reserve derivatives, and the rational negative reserve witness.
The model's `50^4` is **not** a threshold for primes.

At `m=100^4`, `x=101^4`, `R0=1/100`, `d0=0`, the formula reduces to
`1/100+400*log(101/100)-4 <= -37/3750 < 0`.
The cubic logarithm bound is proved by differentiation; all four stated
integer width conditions are checked with exact proof terms.

The additional model asymptotic `Q(x)/x -> 1` is a **written derivation**,
not yet a Lean declaration in this module: `q(x)->1`, and for each
epsilon split the integral at a point after which `abs(q-1)<=epsilon`.
The compact initial integral divided by x tends to zero; the remaining
average error is at most epsilon. Equivalently, the correction from
`1/[x(x^2-1)]` has bounded integral and the added power integrates to
`(x^(3/4)-2^(3/4))/3=o(x)`.

Thus the full PNT-behaviour countermodel argument includes that explicitly
identified written bridge. It refutes no statement about actual primes.
Its negative real growing mode is excluded for the actual function by
the spectral/Landau argument, not by the fixed increment bound alone.

## Validation and handoff

The numerical regressions are unchanged. The event run uses actual cutoff
9,999,993 and finds 10,341 periods: 7,872 old-affine passes, 2,469 failures,
10,341 jump-sample passes, and 10,340 event-log passes. The retained actual
recovery squares are approximately 34.489536036595, 361197.6403415228, and
8906232.48818665 for anchors 31, 324431, and 8573249; the next-event labels
37, 361201, and 8906237 are not substituted for these coordinates.
The one-percent finite-failure regression gaps remain approximately
0.00536668922707 and 0.000172685500648. At the separate sieve-validation
cutoff 19,999,999, the window starting at 19,999,981 still has negative
terminal discrepancy (approximately -0.13702538) and is explicitly
unfinished. Qualitative existence has not located its recovery.
All of these floating-point values remain NumericalEvidence.

The full `lake build` passed (3,953 jobs), including the retained 4,172
certified prime rows. `lake env lean AuditSuzukiRecovery.lean` passed:
all 34 audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`. This includes both cofinal-sign
theorems, first recovery and uniqueness, the removable value and residue,
the countermodel's finite results, and the retained initial, `m=31`,
`log 37`, and two one-percent failure certificates. These are standard
foundational axioms, not new arithmetic or RH assumptions.

`cabal build`, `cabal test`, UI `npm run typecheck` and `npm run build`,
and the established `formal-status`, `garden`, `kernel`, and `submission`
commands passed. The event regression, event report, surcharge-profile
identity regression, sieve regression, and both one-percent witness
generator `--check` runs passed. The latter reproduce the committed
finite data; the Lean proofs, not the generators, establish their truth.
`git diff --check` passed and all dependency-pin files are unchanged.

The post-source-commit handoff regenerates the four versioned JSON inputs
with `cabal run rh-garden -- ui-export`, checks their provenance and
regression content, and records them in a separate snapshot commit before
pushing. The exporter itself deliberately says `not_checked_by_export`:
it does not infer proof validation from theorem-name metadata. No
submission-readiness field is promoted by these recovery results.

The completed surcharge and two-scale results, prefix through `log 37`,
the `m=31` obstruction, both large arithmetic failures, and the unfinished
terminal regression are retained. Numerical data are not promoted to
proofs, and the submission status stays **NO PROOF OF RH IS CLAIMED.**
