# Suzuki positivity Explorer

The Suzuki Explorer searches the two-parameter configuration space
`(omega,t)` for useful positivity patterns. It is a discovery tool, not a
proof checker. Every result it emits has trust class `NumericalEvidence`.

> Numerical positivity over any finite range is not evidence sufficient for
> the Riemann hypothesis.

## Certified normalization

The numerical code is anchored to these LeanChecked statements in
`RHGarden.SuzukiExplorer`:

```text
XiZeroFreeRightOf omega
  <-> forall t, 0 <= suzukiPsiShifted omega t

RiemannHypothesis
  <-> forall t, 0 <= suzukiPsiShifted 0 t

suzukiPsiShifted omega t
  = SuzukiShift omega suzukiPsiPrimeSide t.
```

The last equality combines the certified triangular-test explicit formula
with Suzuki's certified Volterra shift. The arithmetic support is fixed on
the half-open prime cell `[log n, log (n+1))`; Lean checks the corresponding
floor identity and fixed finite Mangoldt sum for the base contribution.

## Running scans and branch searches

For example:

```text
cabal run rh-garden -- explore-suzuki \
  --omega 0.5 --omega 0.25 --omega 0.125 --omega 0.0625 --omega 0 \
  --t-min 0.05 --t-max 8 --samples 1601 --prime-cells \
  --output suzuki-scan.json --format json \
  --certificate-output suzuki-candidates.json
```

Alternatively use `--omega-min`, `--omega-max`, and `--omega-count` for a
uniform parameter grid. Output may be ASCII, CSV, or JSON. The arithmetic
cutoff is deliberately capped at two million cells.

The first positional argument selects a focused search mode:

```text
cabal run rh-garden -- explore-suzuki branches \
  --omega-min 0 --omega-max 0.05 --omega-count 11 \
  --t-max 6 --samples 6001

cabal run rh-garden -- explore-suzuki crossings \
  --omega-min 0 --omega-max 0.05 --omega-count 11 \
  --t-max 6 --samples 6001

cabal run rh-garden -- explore-suzuki cluster \
  --omega 0 --cell-min 180 --cell-max 240 \
  --t-max 5.5 --samples 30001

cabal run rh-garden -- explore-suzuki certificate-status

cabal run rh-garden -- explore-suzuki blocks \
  --t-max 5.71 --samples 3001
```

Other modes are `scan`, `cell`, and `margins`. The cell bounds restrict the reported
critical points and cluster ranking. Every mode supports CSV/JSON output.

The evaluator uses `Double` for discovery. It computes the base
archimedean term by integrating the checked prime-free derivative formula,
subtracts the finite von Mangoldt ramps, and applies the Volterra shift by a
nonuniform trapezoidal rule. An independent path shifts the archimedean part
and subtracts the closed shifted prime ramps

```text
Lambda(n) / sqrt(n) * exp(-omega*log n) * (t-log n).
```

The maximum difference between these paths is reported as the cross-check
error. Agreement catches sign and normalization mistakes, but remains only
floating-point evidence.

## Analytic derivative evaluator

The Explorer evaluates closed first and second derivatives of the exact
shifted arithmetic expression, independently of the value evaluator. If
`f=Psi`, `g=T_omega f`, and

```text
J0(t) = integral_0^t exp(-omega*u) f(u) du,
J1(t) = integral_0^t (t-u) exp(-omega*u) f(u) du,
```

then direct differentiation gives

```text
g'(t)  = exp(-omega*t) (f'(t)+omega*f(t)) + omega^2 J0(t),
g''(t) = exp(-omega*t) f''(t).
```

The cancellation in the second identity is exact and is now independently
LeanChecked in `RHGarden.SuzukiConvexity`. A mixed derivative gives
the implicit-branch predictor `dt/domega=-Psi_{t omega}/Psi_{tt}` whenever
the curvature is nonzero. Regression tests compare `g'` with centered finite
differences of the independent adaptive-Simpson value evaluator and compare
`g''` with finite differences of `g'`; discrepancies are reported.

## Critical points and branches

Lean proves substantially more geometry than the original root scanner used.
On every prime cell `n >= 2`, the Mangoldt contribution is affine and

```text
Psi''(t) = y + 1/y - y^3/(y^4-1) >= 1,  y=exp(t/2).
```

Together with `(T_omega Psi)''=exp(-omega*t) Psi''`, this makes every shifted
cell strictly convex for every real `omega`. The Explorer therefore checks
only the derivative signs at the two interior ends: if they bracket zero it
refines the unique critical point, otherwise the minimum is at an endpoint.
Cell 1 retains the generic scanner. Multiple detected interior roots in a
cell `n >= 2` are now a regression failure. An interior fold is formally
impossible; branches can instead meet prime boundaries or cease to win the
global lower envelope.

For simultaneous minimum branches A and B, the crossings mode brackets sign
changes of `m_A(omega)-m_B(omega)` and recomputes both cell minima while
bisecting in omega. These are candidate crossings, not exact equations.
Alongside every cell minimum the Explorer records

- `Psi_omega(t)/t` and `Psi_omega(t)/t^2`;
- `exp(-t/2) Psi_omega(t)` and `exp(-omega*t) Psi_omega(t)`;
- `omega*t`;
- neighboring prime gaps;
- Chebyshev `theta(n)`, `psi(n)`, and `psi(n)-n`;
- prime-power events at cell boundaries.

The refined scan on `0 <= omega <= 0.05` resolves the earlier apparent jump
from cell 14 to the 207 region. In increasing omega order, its numerical
lower envelope is

```text
cell 208 --0.01474830--> cell 34
         --0.02270270--> cell 14
         --0.02706459--> cell 5.
```

The candidate common minima at these crossings are respectively about
`0.033040519`, `0.034777470`, and `0.035483865`. Thus the old coarse scan
missed cell 34, and the initial `1,2,5,14,...` Catalan coincidence does not
continue.

At `omega=0`, a 30,001-node scan of cells 180--240 finds cell 208 best at
`t=5.33809175`, `Psi=0.0280226237`, with cell 207 only `2.21e-6` higher.
Cells 209, 206, and 213 follow. The detailed root classification shows two
interior basins (cells 208 and 213); most other close competitors are
prime-threshold endpoints. This is not one smooth critical branch crossing
all cells 207--216.

The report also fits only low-complexity diagnostics (`log(cell)` against
`1/omega` and `log(1/omega)`, and `t*` against `log(cell)`). These short scans
do not yet support a stable scaling law.

Nor is the cascade explained by a prime event at the winning cell itself.
Cells 14, 34, and 208 have no prime-power event at either boundary in this
scan; their surrounding prime gaps are 4, 6, and 12, while the recorded
Chebyshev `psi(n)-n` values are approximately `-1.205`, `-1.396`, and
`-1.854`. This tentatively points toward accumulated Mangoldt slope between
events rather than a single boundary impulse, but the sample is far too
small for a statistical conclusion.

## Candidate lower bounds

For every sampled cell the Explorer searches affine bounds `a+b*t`, using a
finite slope grid. Coefficients are rounded downward to rational numbers with
denominator one million and serialized as, for example:

```json
{
  "trust": "NumericalEvidence",
  "status": "numerically_passed",
  "omega": 0.25,
  "t_interval": [0.693147180560, 1.098612288668],
  "prime_cell": 2,
  "basis": ["1", "t"],
  "coefficients": [
    {"numerator": 48222, "denominator": 1000000},
    {"numerator": 0, "denominator": 1000000}
  ],
  "discovery_precision": 0.00496875
}
```

The allowed statuses are `candidate`, `numerically_passed`, and
`numerically_failed`. None means proved.

## Lean certificate boundary

`SuzukiCellLowerBoundCertificate` accepts rational parameters but also
requires Lean proofs that its interval lies in the declared prime cell, that
the proposed lower bound is nonnegative, and that it lies below
`suzukiPsiShifted` throughout the interval. The generic theorem
`SuzukiCellLowerBoundCertificate.shiftedPsi_nonnegative` then certifies the
cell.

As an end-to-end smoke test, Lean uses the existing symbolic local-positivity
theorem to extract a positive rational `q < log 2`, constructs the zero
affine certificate on `[0,q]`, and proves
`exists_suzukiPsi_nonnegative_on_firstCertifiedInterval`. No floating-point
output is imported into this proof.

`SuzukiCellConvexCertificate` is the stronger branch-aware verifier. It
contains a rational critical bracket, proof that the bracket lies inside its
prime cell, derivative signs on the two flanks, a lower bound on the bracket,
and nonnegativity of that bound. The generic checked theorem
`lowerBound_on_Icc_of_deriv_signs` propagates the bracket bound to the whole
cell, and `SuzukiCellConvexCertificate.shiftedPsi_nonnegative_on_cell`
specializes it to shifted Psi. The formal development also proves
`differentiableOn_suzukiPsiShifted_primeCellInterior`.

`SuzukiStrongConvexCellCertificate` is simpler and no longer needs a
critical bracket. A rational sample point supplies a checked value lower
bound and derivative absolute upper bound, while a positive curvature lower
bound supplies

```text
Psi_omega(t) >= Psi_omega(x)
  - |Psi_omega'(x)|^2/(2*m).
```

The generic theorem `lower_bound_of_secondDeriv_ge` and the certificate's
`positive_on_cell` verifier are LeanChecked. Numerical values still provide
no proof fields.

Candidate JSON now also emits rationalized `strong_convex_sample`,
`strong_convex_value_lower`, `strong_convex_deriv_abs_upper`, and
`strong_convex_curvature_lower` fields together with their numerical
candidate margin.  These are proof-search hints only: rounding does not
establish any of the corresponding inequalities, so Lean must verify every
field independently.

The first nontrivial instance of this pipeline is now LeanChecked for the
actual unshifted function.  On cell 2, `[log 2, log 3]`, Lean evaluates the
finite Mangoldt term to the single ramp at 2 and uses the rational sample
`x=9/10`.  Exact Taylor/series bounds prove

```text
Psi(9/10) > 1/100,
|Psi'(9/10)| <= 13/100,
Psi'' >= 1 throughout the cell.
```

Thus the verified strong-convexity margin is
`1/100-(13/100)^2/2=31/20000>0`, and
`suzukiPsi_pos_cell_two` proves strict positivity on the complete closed
cell.  This certificate imports no Explorer floating-point value.

The numerical candidates currently found for the requested certification
tests are:

```text
omega=1/10, cell 2: t*=0.89237347, Psi=0.04090532, curvature=1.310889
omega=1/20, cell 5: t*=1.7799955,  Psi=0.03788844, curvature=2.2167661
```

Neither of these *shifted* candidate cells is Lean-certified yet. Universal
curvature is no longer the obstruction. The successful unshifted cell-2
proof demonstrates the exact sample-bound pipeline; extending it to shifted
values still requires rigorous pointwise bounds for `Psi_omega(x)` and
`|Psi_omega'(x)|`. No decimal approximation is admitted as a certificate.

The full workflow is:

```text
formal representation map
  -> floating-point search
  -> candidate rational coefficients
  -> independent analytic inequalities in Lean
  -> kernel-checked certificate.
```

Finite cell certificates cannot prove a statement on an infinite tail.
`SuzukiPsiTailCertificate` names that separate open requirement; the
Explorer's normalized envelopes are intended to help discover its eventual
shape.

## Mangoldt-state margin mode

The exact formal cell identity is now

```text
S_n = sum_{k<=n} Lambda(k)/sqrt(k),
C_n = sum_{k<=n} Lambda(k) log(k)/sqrt(k),
Psi(t) = A(t) - S_n t + C_n
        for log n <= t <= log(n+1).
```

The compact restricted dual

```text
D_n(s) = max_{log n <= t <= log(n+1)} (s t - A(t))
```

is attained at a unique point for every `n>=2`. Lean proves that the entire
cell is nonnegative exactly when the scalar margin
`C_n-D_n(S_n)` is nonnegative. It also proves that a Mangoldt update is
non-destructive before accounting for movement to the next cell; if there is
no update, all margin change comes from that interval motion.

Run the arithmetic-state view with, for example:

```text
cabal run rh-garden -- explore-suzuki margins \
  --t-max 5.71 --samples 30001 --cell-min 2 --cell-max 300
```

Rows include `S_n`, `C_n`, the candidate restricted dual and margin, the
candidate maximizer type, Mangoldt masses at both boundaries, and distances
to neighboring Mangoldt events. These values are `NumericalEvidence`; only
the defining identities and equivalences are LeanChecked.

A scan through cell 300 again places cell 208 first, at candidate margin
`0.0280226237`, followed extremely closely by cell 207. The state is constant
from the event at 199 through cell 210; cell 208 is nine integers after that
event and three before the next one at 211. The next nearby basin, cell 213,
uses the state updated at 211. This is consistent with interval motion being
responsible for deterioration between sparse events, but it is not a proved
tail law or a causal statistical conclusion.

## Mangoldt event-block mode

The preferred discrete configuration is now a whole interval between
consecutive prime-power events, not an individual integer cell. The `blocks`
mode reports the event endpoints, gap, constant `(S_q,C_q)` state, slope
deficits at both ends, unique candidate optimizer, `exp(t*)`, block margin,
and the integer cell containing the optimizer. All values remain
`NumericalEvidence`; the corresponding state constancy, convexity, and
block-margin equivalences are LeanChecked separately.

The old winner labels translate exactly as follows:

```text
cell 5   : event block 5 -> 7
cell 14  : event block 13 -> 16
cell 34  : event block 32 -> 37
cell 208 : event block 199 -> 211.
```

The endpoints 16 and 32 are powers of two, hence genuine Mangoldt events.
At omega zero, the `199 -> 211` block has an interior candidate optimizer
near `exp(t*)=208.115`, candidate margin `0.02802262`, and the deficit
`S_q-A'(t)` changes from approximately `+0.639` to `-0.199`. This sign
change is the structural invariant locating the dangerous point; the label
208 merely identifies which integer subcell contains it.

## Archimedean dual dynamics mode

The `dual` command follows the event state against the unrestricted
half-line Legendre dual:

```text
cabal run rh-garden -- explore-suzuki dual --t-min 1.5 --t-max 5.71
```

For each event `q` and next event `r` it reports `lambda_q`, `(S_q,C_q)`,
the unique optimizer `tStar(S_q)`, `AStar(S_q)`, the global dual margin,
the post-event deficit `A'(log q)-S_q`, smooth drift to `r`, the next
Mangoldt impulse, and the exact recurrence's predicted next deficit.  It
also distinguishes active blocks, where `log q<tStar<log r` and the global
dual margin equals the block margin, from endpoint-minimized blocks.

The corresponding facts are LeanChecked in `SuzukiDualDynamics.lean`:
quadratic coercivity and dual attainment, uniqueness and one-Lipschitzness
of `tStar`, `AStar'=tStar`, the signed-area event update, the deficit
recurrence, and active-block exactness. The displayed values are still
`NumericalEvidence`.

The first scan shows that the unrestricted global margin is positive over
the displayed range but is not identical to an inactive block margin. The
dangerous active blocks `5->7`, `13->16`, `32->37`, and `199->211` share a
simple pattern: a negative post-event deficit crosses zero under smooth
archimedean drift before the next impulse. No monotonic normalized deficit
or always-positive event increment appears in this range; both signs occur.
This rules out those naive invariants but does not address the infinite tail.

A regression scan through event integers below 5000 produced 710 complete
event blocks. The smallest candidate global margin was about `0.02752057`
at `3089->3109`; none was negative. There were 251 active blocks, while the
event-area increment was negative 357 times and positive 353 times. Thus
positivity of this finite sample is not explained by monotone event gains.
The robust low-complexity invariant is instead the active-block sign
crossing: the post-event deficit is negative and becomes positive under
archimedean drift before the next impulse. This condition is exact in Lean,
but it does not itself lower-bound the margin or certify a tail.

## Kicked convex-flow boundary state

`RHGarden.SuzukiKickedFlow` reduces each complete event block `q -> r` to
the two boundary coordinates

```text
B_q = Psi(log q)
d_q = A'(log q) - S_q.
```

Writing `h=log r-log q`, `G=A'(log r)-A'(log q)`,
`R=A(log r)-A(log q)-A'(log q)h`, and
`lambda_r=Lambda(r)/sqrt(r)`, Lean checks the exact state transition

```text
EVENT q:        (B_q, d_q)
                   |
                   | smooth convex flow over h
                   v
                (B_q + d_q*h + R, d_q + G)
                   |
                   | Mangoldt kick lambda_r
                   v
EVENT r:        (B_r, d_r = d_q + G - lambda_r).
```

Unit archimedean curvature gives the certified coarse bounds
`G >= h` and `R >= h^2/2`. The optimizer displacement
`x_q=log q-tStar(S_q)` has the even simpler checked sawtooth recurrence

```text
x_q -> x_q+h -> x_r=x_q+h-DeltaT_r,
0 <= DeltaT_r <= lambda_r.
```

The associated kick area lies between zero and `lambda_r^2/2`, giving
exact two-sided bounds for each global-dual-margin update.

The deliberately conservative safety quantity

```text
E_q = B_q - max(-d_q,0)^2/2
```

is a LeanChecked lower bound for `Psi` throughout the following block.
Thus `E_q >= 0` certifies that block, and initial positivity together with
nonnegative safety energy at every complete block is a sufficient (not
proved) criterion for RH. It is not an invariant numerically: in the scan
of 78,733 complete blocks with event integers below one million, it is
already negative on `5 -> 7`, and its smallest sampled value is about
`-0.21434087` on `59797 -> 59809`, while that block's candidate exact margin
is about `0.04362295`.

The same scan tested the low-complexity potentials
`M+c*x^2`, `M+c*max(-x,0)^2`, and `M+c*d^2` for
`c in {1/4,1/2,1}`. Every candidate decreases at tens of thousands of
events. `M+(1/2)x^2` had the least-negative worst single update among the
tested displacement potentials, but still decreased 42,031 times; it is
therefore a failed ansatz, not a candidate invariant.

For the four previously dangerous blocks, the safety data are:

```text
block       B_q          d_q          E_q          exact margin   slack
5 -> 7      0.06716321  -0.39738606  -0.01179463   0.03261803     0.04441266
13 -> 16    0.05813822  -0.44621494  -0.04141566   0.03106868     0.07248434
32 -> 37    0.04606458  -0.43183818  -0.04717752   0.02978690     0.07696442
199 -> 211  0.04238375  -0.63892444  -0.16172846   0.02802262     0.18975109
```

The impulse-to-drift ratios `lambda_r/G` for these blocks are approximately
`0.90`, `0.22`, `0.70`, and `0.44`; no common near-critical ratio emerges.
The heuristic comparison of Mangoldt impulses with prime-power gaps remains
only a guide for choosing arithmetic statistics. All displayed scans are
`NumericalEvidence`, never a finite-range or tail certificate.

## True-curvature safety and optimizer queues

`RHGarden.SuzukiTrueCurvature` retains the exact curvature instead of
discarding it to the unit lower bound. Lean checks

```text
A''(t) = exp(t/2) * (1 - 1/(exp(t/2)^2*(exp(t/2)^4-1)))
A''(t) >= (5/6)*exp(t/2),                 t >= log 2.
```

Thus a block beginning at `q` has certified curvature
`m_q=(5/6)*sqrt(q)`, and

```text
E_q^curv = B_q - max(-d_q,0)^2/(2*m_q)
```

is a LeanChecked lower bound for the entire following complete block.
Universal nonnegativity of these energies, together with the still-open
initial interval, would suffice for RH; that premise is not asserted.

The scan of all 78,733 complete blocks with event integers below one million
found no negative `E_q^curv`. Its smallest candidate value was
`0.024789985513` on `5 -> 7`. This finite result is strictly
`NumericalEvidence`, not evidence adequate for RH and not a tail
certificate. Representative rows are:

```text
block        m_q          old E_q       E_q^curv      exact margin   slack
5 -> 7       1.86338998   -0.01179463    0.02478999    0.03261803     0.00782804
13 -> 16     3.00462606   -0.04141566    0.02500469    0.03106868     0.00606399
32 -> 37     4.71404521   -0.04717752    0.02628495    0.02978690     0.00350195
199 -> 211  11.75561332   -0.16172846    0.02502080    0.02802262     0.00300183
59797 -> 59809
             203.77854265 -0.21434087    0.04249561    0.04362295     0.00112734
```

The optimizer kick area now has the sharp checked bounds

```text
DeltaT^2/2 <= kickArea <= lambda*DeltaT - DeltaT^2/2.
```

Consequently a negative global-margin update requires negative post-event
optimizer displacement. The backlog `max(-x_q,0)` obeys a checked
Lindley-style upper recurrence, while true curvature improves the kick
response to `DeltaT <= 6*lambda/(5*exp(tStar/2))`.

Numerically, `DeltaT<h` held for 29,865 of the 78,733 scanned transitions,
so eventwise queue clearing is not a viable universal invariant. The largest
post-event backlog in this range was about `0.18165663`, at `q=2`. These
queue statistics remain discovery data only.

## Square-root optimizer coordinates

The `roots` mode uses the natural coordinate
`uStar(S)=exp(tStar(S)/2)`, with normalized state
`rho_q=uStar(S_q)/sqrt(q)` and displacement
`x_q=sqrt(q)-uStar(S_q)`. Run it with, for example:

```text
cabal run rh-garden -- explore-suzuki roots --t-min 0.69314718056 --t-max 14.503644
```

`RHGarden.SuzukiRootDynamics` proves that every actual Mangoldt event state
is in the interior optimizer regime and checks

```text
duStar/dS = 1/(2*F(uStar)),       5/6 <= F(uStar) < 1,
lambda/2 <= DeltaU <= 3*lambda/5,
x_r = x_q + sqrt(r)-sqrt(q)-DeltaU,
rho_r = sqrt(q/r)*rho_q + DeltaU/sqrt(r).
```

It also proves the exact root-area formula

```text
DeltaM = 4 * integral_{uBefore}^{uAfter}
  F(u) * log(sqrt(r)/u) du.
```

Thus only optimizer overshoot beyond `sqrt(r)` can contribute negative area.
This localizes margin loss but does not prove that accumulated margins stay
positive.

The scan of 148,520 complete blocks below approximately 1.99 million found:

```text
maximum rho                    1.1062927046 at q=2
maximum rho for q >= 1,000     1.0074140035 at q=1129
maximum rho for q >= 100,000   1.0007777556 at q=102679
maximum rho for q >= 1,000,000 1.0002801714 at q=1195247
largest absolute overshoot     0.3609905053 at q=24137
largest DeltaU/sqrt-gap       11.0903278418 at q=65536
blocks with rho>1              75,925 / 148,520
blocks with DeltaU>sqrt-gap    93,422 / 148,520
crude gap-condition failures  103,049 / 148,520
```

The high kick/gap ratio at `65536=2^16` comes from a tiny square-root gap
followed by a nonzero prime-power impulse. The crude condition
`r-q >= (6/5)*Lambda(r)` therefore fails too often to be a plausible eventual
reduction in its present form.

The root-area bound suggests overshoot reserves. The candidates
`M+(5/3)overshoot^2/sqrt(q)` and `M+2 overshoot^2/sqrt(q)` stayed positive in
this scan, but decreased at 73,603 and 73,417 events, with worst changes about
`-0.01666` and `-0.02055`. They are not Lyapunov invariants. The useful result
is the exact coordinate and signed-area localization, not a scanned invariant.

## Root discrepancy and multi-event busy periods

The next exact coordinate is the root-slope discrepancy

```text
P(u) = A'(2 log u)
Sroot(u) = sum_{n <= u^2} Lambda(n)/sqrt(n)
D(u) = P(u) - Sroot(u).
```

`RHGarden.SuzukiRootDiscrepancy` kernel-checks the hybrid laws. Inside a
complete Mangoldt block,

```text
D'(u) = 2 F(u),                  5/3 <= D'(u) < 2,
```

and at the next event `r` the right-continuous discrepancy jumps downward by
`Lambda(r)/sqrt(r)`. With `H(u)=Psi(2 log u)`, Lean also checks

```text
H'(u) = 2 D(u)/u
H(b)-H(a) = integral_a^b 2 D(u)/u du
```

on every complete block. Consequently a negative-discrepancy excursion
consumes exactly the weighted backlog area `integral 2*max(-D,0)/u`. The RH
prefix-area statement recorded in Lean is an equivalence with the existing
initial-interval and block-margin formulation; its open positivity premise is
not asserted.

The command

```text
cabal run rh-garden -- explore-suzuki busy --t-max 14.5 --samples 801
```

groups consecutive negative-discrepancy blocks into numerical busy periods.
The scan through events below about `1.98e6` found 5,137 completed periods,
including 1,530 spanning more than one event. The longest contained 4,663 event
states (`1477501` to recovery before `1543811`); the widest root interval ran
from `324431` to recovery before `361201` and contained 2,888 event states.
The largest reserve fraction consumed was the early one-event excursion
`5 -> 7`, about `0.51435`. The previously dangerous `199 -> 211` block belongs
to a three-state excursion starting at `193`, consuming about `0.02129` from a
starting reserve of `0.04931`.

These figures are `NumericalEvidence`. They show that the natural unit is a
multi-event busy period, not an isolated prime cell. Event counts and root
widths can grow while the logarithmic width stays small; in the largest scans
the arrival/service ratio can be very close to one. The next certificate
problem is therefore to bound cumulative weighted backlog loss using finite
arrival mass and smooth service, rather than require every event to clear its
own deficit.
