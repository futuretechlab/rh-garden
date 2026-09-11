# RH Garden research status

**This project does not prove the Riemann Hypothesis.** It now certifies a
large representation loop for Riemann xi and the Li test family, but the
universal positivity proposition remains open.

## LeanChecked representation loop

The first analytic loop is closed in Lean:

```text
Xi
  -> Taylor and generating representations
  -> classical Li coefficients
  -> signed Lagarias height-star zero sums
  -> occurrence-indexed genus-one canonical product
  -> exact xi logarithmic derivative
  -> Xi.
```

The checked ingredients include the multiplicity-aware xi divisor, genuine
height cutoffs, exact conjugation and Weil-reflection symmetries, the pinned
Zeta23 local zero-count estimate, reciprocal-square and reciprocal-three-halves
summability, canonical-product local uniform convergence, the zero-free
quotient growth theorem, normalized affine factorization, and passage of
finite Li jets through locally uniform logarithmic-derivative limits.

In the project's zero-based convention,
`classicalLiRealCoefficient k` is the conventional coefficient
`lambda_(k+1)`. Lean proves that the complex coefficient is real and that both
signed star limits have this value:

```text
LiStarConvergesTo ( k+1) (classicalLiCoefficient k)
LiStarConvergesTo (-(k+1)) (classicalLiCoefficient k).
```

Individual Li zero sums retain Lagarias's conditional height-star convention;
they are not silently represented by an unordered `tsum`.

## Infinite Weil-Li representation

For the integer-indexed Li tests

```text
G_n(s) = 1 - (1 - 1/s)^n,
```

`RHGarden.LiWeilInfinite` defines the occurrence-indexed Weil summand and the
ordinary infinite scalar

```text
weilLiScalar n m =
  sum_rho G_n(rho) * conjugate(G_m(1-conjugate(rho))).
```

This sum is absolutely convergent. Lean proves each test is
`O(1/|rho|)` on xi zeros, bounds a paired summand by a constant times
`1/|rho|^2`, applies occurrence-indexed reciprocal-square summability, and
shows the genuine height cutoffs exhaust the resulting `tsum`.

Passing the finite identity through this ordinary limit on the left and three
star limits on the right proves Lagarias equation (3.3) for Riemann xi:

```text
weilLiScalar n m
  = classicalLiSigned n
  + classicalLiSigned (-m)
  - classicalLiSigned (n-m).
```

Hermitian symmetry is also LeanChecked. On the diagonal, equation (3.4)
becomes

```text
weilLiScalar n n = 2 * classicalLiSigned n
weilLiQuadraticValue k = 2 * classicalLiRealCoefficient k.
```

The second formula is the certified bridge

```text
ClassicalLiRealSequence <-> WeilLiQuadraticValues.
```

The representation name deliberately says `WeilLi`: only Lagarias's Li test
family has been formalized at the infinite level.

## Distinct positivity propositions

The garden keeps three claims separate:

```text
LiPositive       := every classical Li coefficient is nonnegative
WeilLiPositive   := every diagonal Weil value on G_n is nonnegative
WeilFormPSD      := the full Weil form is positive semidefinite on its test space
```

Lean proves

```text
LiPositive <-> WeilLiPositive
```

coefficientwise from `weilLiQuadraticValue k = 2*lambda_(k+1)`. This is an
equivalence of two open propositions and proves neither endpoint. The full
`WeilFormPSD` statement is stronger and remains a separate future
formalization; it must not be inferred from the Li-test diagonal identity.

Li's `LiPositive <-> RiemannHypothesis` criterion remains registered as
literature-certified rather than kernel-checked. Thus neither Li positivity,
Weil-Li positivity, full Weil positivity, nor RH has been discharged.

## Suzuki zero-side screw kernel

`RHGarden.SuzukiScrew` starts the Suzuki district from the xi divisor. For an
analytic-multiplicity occurrence `a`, Lean defines

```text
gamma_a = i * (rho_a - 1/2)
```

and checks the inverse coordinate, the real and imaginary coordinates, and
the equivalence between real spectral parameters and `XiTZerosReal`. A
cofinite comparison with occurrence reciprocal-square summability proves
summability of `1/|gamma_a|^2`; it does not repeat zero counting.

The zero-side series, real screw function, and kernel are

```text
Psi(t) = sum_a (1-exp(i*gamma_a*t))/gamma_a^2
g(t) = -Psi(t)
GKernel(t,u) = g(t-u)-g(t)-g(-u)+g(0).
```

Lean proves unconditional conjugation and evenness of `Psi`, absolute
summability at fixed real arguments, and the exact `tsum` algebra

```text
Kernel(t,u) = sum_a
  (exp(i*gamma_a*t)-1)*(exp(-i*gamma_a*u)-1)/gamma_a^2.
```

`RHGarden.XiMidpoint` uses Zeta23's pinned `N=1` Euler--Maclaurin formula to
write `zeta(1/2) = -3/2 + J/2`, with `|J| <= 2`. Consequently
`Re zeta(1/2) < 0`, so zeta and xi are nonzero at the midpoint. Lean then
proves `xiSpectralParameter a != 0` for every occurrence. Thus every division
above is now literally by a nonzero spectral parameter; no RH input is used.

Assuming the existing open proposition `XiTZerosReal`, Lean rewrites every
kernel term as

```text
suzukiFeature a t * conjugate (suzukiFeature a u)
```

and proves both finite-height Gram positivity and positive semidefiniteness of
the limiting kernel. This implication proves neither RH nor the converse
Suzuki criterion.

`RHGarden.XiNevanlinna` now defines
`Q_xi(z)=i*logDeriv xi(1/2-i*z)` and proves the centered, absolutely convergent
spectral partial fraction. It LeanChecks

```text
XiTZerosReal <-> XiNevanlinna
```

without assuming simple zeros: the reverse direction uses analytic order to
show that a logarithmic derivative cannot be analytic at any xi zero. Compact
local normal convergence proves screw continuity, and the remaining screw
axiom is exactly `KernelPSD riemannScrewKernel`.

For `Im z>1/2`, Lean also proves absolute integrability and the convention-
correct Fourier--Laplace identity

```text
integral_0^infinity g(t)e^(izt) dt = (i/z^2) Q_xi(-z).
```

`RHGarden.SuzukiPointwise` now proves that `Q_xi` is odd and normalizes this
to Suzuki's form

```text
integral g(t)e^(izt) dt = -(i/z^2) Q_xi(z),
integral Psi(t)e^(izt) dt = (i/z^2) Q_xi(z).
```

It defines `SuzukiPsiNonnegative` and LeanChecks

```text
KernelPSD riemannScrewKernel -> SuzukiPsiNonnegative
```

from the exact diagonal `K(t,t)=2*Psi(t)`. The one-sided Laplace transform
and explicit xi continuation are checked on `Re w>1/2`; the continuation is
meromorphic and regular at every positive real parameter. A uniform pinned
Euler--Maclaurin argument proves `Re zeta(s)<0` for real `1/2<s<1`, supplying
the only previously missing positive-real-axis xi nonvanishing input.

`RHGarden.KernelIntegral` now proves the missing finite-to-continuous
positivity passage. For every jointly continuous complex kernel, finite
sampled `KernelPSD` implies nonnegativity of its compact-interval double
integral against continuous tests. The proof uses finite-range approximants,
their fiber measures as positive weights, and dominated convergence. Its
Riemann-screw specialization, the bounded-support whole-line Hermitian form,
the zero-mean convolution simplification, and compact truncated-exponential
test positivity are all LeanChecked.

The Suzuki 2023, Theorem 1.7 route is now LeanChecked. The generic
`NonnegativeLaplaceBoundaryPrinciple` is proved by all-order moment
integrability, differentiated Laplace integrals, Taylor expansion, and a
Tonelli passage through the nonnegative exponential series. For nonnegative
`Psi`, this extends the Laplace transform analytically across the full right
half-plane. Meromorphic uniqueness with the explicit xi continuation and the
logarithmic-derivative pole theorem then force every spectral parameter to be
real. Thus Lean checks

```text
SuzukiPsiNonnegative -> XiTZerosReal
ScrewKernelPSD <-> XiTZerosReal
RiemannHypothesis <-> ScrewKernelPSD.
```

These are conditional implications and equivalences of open propositions;
they do not prove any positivity assertion or RH. The historical general
Krein--Langer correspondence remains literature context rather than a
formalized theorem.

## Garden trust state

The following representation edges are LeanChecked:

```text
XiHeightZeroCutoff -> LiStarPartialSums
XiHeightZeroCutoff -> FiniteWeilCutoffValues
LiStarConvergence -> WeilLiQuadraticValues
FiniteWeilCutoffValues -> WeilLiQuadraticValues
ClassicalLiRealSequence <-> WeilLiQuadraticValues.
XiDivisor -> XiSpectralParameters
XiSpectralParameters -> SuzukiPsiZeroSide
SuzukiPsiZeroSide -> RiemannScrew
RiemannScrew -> RiemannScrewKernel
RiemannScrewKernel -> IntegralScrewQuadraticForm
RiemannScrew -> XiNevanlinnaTransformHighStrip
SuzukiGramKernel -> RiemannScrewKernel
```

The criterion reductions

```text
LiPositive <-> WeilLiPositive
ScrewKernelPSD -> SuzukiPsiNonnegative
SuzukiPsiNonnegative -> XiTZerosReal
ScrewKernelPSD <-> XiTZerosReal
```

are also LeanChecked. No edge promotes either proposition to a proof, and no
edge connects the unformalized full `WeilFormPSD` criterion to RH.

## Exact next frontier

The representation and converse are complete; the next mathematical frontier
is the open positivity itself. One must prove `SuzukiPsiNonnegative` (equivalently
the Riemann screw kernel is PSD, hence RH), or attack an equivalent Li/Weil
positivity statement. Full Weil-form PSD and general Krein--Langer theory
remain distinct from the specialized theorem proved here. No positivity
theorem for the Li sequence, screw kernel, or full Weil form is claimed.

## Prime-side and shifted Suzuki frontier

The zero-side positivity frontier now has two additional formalized
coordinates. `RHGarden.SuzukiShifted` defines every term of Suzuki's
prime-side equation (1.1), proves the finite Mangoldt contribution vanishes
on `0 <= t < log 2`, and defines the continuous real-even shifted Volterra
family of equation (11.1). It also defines global/eventual positivity sets and
the monotone zero-free-half-plane family, proving the unconditional safe
zero-free parameter `omega=1/2` and

```text
RiemannHypothesis <-> 0 in SuzukiShiftedPositivitySet.
```

This equivalence does not assert membership. The zero-side/prime-side bridge
is now LeanChecked: `RHGarden.SuzukiTriangle` extends Zeta23's compactly
supported `C^2` explicit formula to Suzuki's piecewise-linear triangular test
by normalized smooth convolution. The zero sum, finite prime sum, pole terms,
and Gamma bracket are all passed through the limit, and the Gamma bracket is
evaluated exactly. Consequently `suzukiPsi_eq_primeSide` and the prime-free
archimedean formula on `0 <= t < log 2` are unconditional.
`RHGarden.SuzukiLocalPositive` differentiates that formula exactly and proves
that `artanh(exp(-t/2))` tends to positive infinity while the remaining
derivative terms stay bounded near zero. Hence the unconditional theorem
`exists_suzukiPsi_pos_near_zero` supplies some `delta>0` with
`Psi(t)>0` on `0<t<delta`; evenness gives local symmetric nonnegativity, and
`G_g(t,t)=2 Psi(t)` gives local diagonal screw-kernel nonnegativity. This is
strictly weaker than global `SuzukiPsiNonnegative` and much weaker than
`KernelPSD`; neither open proposition is discharged. Positivity all the way
to `log 2` and the first-prime interval remain open.

`RHGarden.SuzukiShiftTransform` now proves the generic first and second
Volterra Fourier--Laplace transforms, the multiplier

```text
F_+(T_omega f)(z)
  = ((z+i omega)^2/z^2) F_+(f)(z+i omega),
```

Suzuki equation (11.2) on the upper-half-plane convergence strip, and the
semigroup identity `T_eta T_omega = T_(omega+eta)`. The function-level proof
uses the FTC resolvent factorization `(I+omega J)^2 M_omega`, since the pinned
library has no applicable one-sided transform uniqueness theorem. Global
shifted positivity is consequently upward closed.

`RHGarden.SuzukiShiftedLandau` now supplies the compact-tail version of the
Landau argument. It LeanChecks that the compact initial transform is entire,
that translation identifies the remaining tail transform up to its exact
exponential factor, and that eventual nonnegativity forces convergence and
analyticity throughout `Re w>0`. Meromorphic uniqueness and the checked
logarithmic-derivative pole obstruction prove

```text
SuzukiPsiShiftedEventuallyNonnegative omega
  -> XiZeroFreeRightOf omega.
```

The converse is factored through `RHGarden.SuzukiShiftedNevanlinna`.
Reflection-pairing in the
exact shifted spectral partial fraction cancels the genus-one correction and
LeanChecks

```text
XiZeroFreeRightOf omega <-> XiShiftedNevanlinna omega.
```

`RHGarden.SuzukiShiftedHerglotz` closes the remaining forward subedge without
assuming the general Krein--Langer correspondence. Each shifted pole in the
closed lower half-plane is represented by its positive Cauchy probability
measure (a Dirac mass on the boundary and a Cauchy density below it). Their
countable sum satisfies the Herglotz integrability condition by the existing
reciprocal-square theorem. The resulting rank-one integral kernel is PSD and
is the translation-difference kernel of an explicit continuous screw
function. Its one-sided transform is `-(i/z^2) Q_omega(z)`. A new specialized
Fourier uniqueness theorem, reduced to Mathlib's characteristic-function
uniqueness for finite positive measures, identifies this screw with
`-Psi_omega`. Hence Lean now checks

```text
XiZeroFreeRightOf omega
  <-> XiShiftedNevanlinna omega
  -> forall t, 0 <= Psi_omega(t),

XiZeroFreeRightOf omega
  <-> SuzukiPsiShiftedEventuallyNonnegative omega.
```

In particular `Psi_omega` is globally nonnegative for every
`omega >= 1/2`.

The shifted representation district is therefore complete. The actual
mathematical frontier is to move the certified safe parameter region left
from `omega=1/2` toward `omega=0`; membership at zero is equivalent to RH.
Full Weil-form PSD and the general Krein--Langer theorem remain separate.

## Numerical discovery and exact certificates

`RHGarden.SuzukiExplorer` LeanChecks the global shifted criterion directly:

```text
XiZeroFreeRightOf omega
  <-> forall t, 0 <= suzukiPsiShifted omega t,

RiemannHypothesis
  <-> forall t, 0 <= suzukiPsiShifted 0 t.
```

It also proves that shifting the certified prime-side expression gives the
exact shifted function and that each cell `[log n,log(n+1))` has a fixed
finite Mangoldt support. `SuzukiCellLowerBoundCertificate` is an exact
rational-data interface: its proof fields, not its data, establish a cell
lower bound. The first smoke-test theorem extracts an existential rational
subinterval of the already checked local-positive neighborhood and certifies
nonnegativity there.

The companion `explore-suzuki` executable performs floating-point scans,
candidate minimization, prime-statistic collection, and affine lower-bound
fitting. Its graph edges have trust `NumericalEvidence`, which is rejected by
both Kernel and Literature modes. Candidate data can only become checked by
an independent Lean proof. A modest scan suggests changes in the dangerous
minimizing cell as `omega` decreases, but this is neither a global bound nor
evidence sufficient for RH. The certificate schema, numerical cross-check,
and current patterns are documented in `EXPLORER.md`.

The Explorer evaluates closed first/second/mixed derivatives, continues local
minimum branches in `omega`, and detects prime-boundary collisions and
adaptively refines crossings of the numerical lower envelope. The fine
`0 <= omega <= 0.05` scan resolves the coarse cell-14-to-207 jump into the
candidate cascade `208 -> 34 -> 14 -> 5` as omega increases. At omega zero,
cell 208 narrowly beats cell 207 and a separate interior basin occurs in cell
213; most of the surrounding 207--216 cluster consists of cell-boundary
values. All of these facts remain `NumericalEvidence`.

On the checked side, `RHGarden.SuzukiConvexity` proves the exact cancellation
`(T_omega Psi)''=exp(-omega*t) Psi''`, zero second derivative of the fixed
Mangoldt cell sum, and the closed lower bound `Psi''>=1` on every cell
`n>=2`. Hence every shifted cell is strictly convex for every real omega,
has at most one interior critical point, and admits no interior fold.
`SuzukiStrongConvexCellCertificate` verifies a whole-cell lower bound from a
single exact sample value/derivative bound and a curvature bound. The first
complete unshifted instance is now checked: on `[log 2,log 3]`, Lean evaluates
the Mangoldt sum to its one ramp and proves at `x=9/10` that
`Psi(x)>1/100` and `|Psi'(x)|<=13/100`. Together with `Psi''>=1`, the exact
margin `31/20000` yields `suzukiPsi_pos_cell_two` on the entire closed cell.
The shifted candidate cells 2 at omega `1/10` and 5 at omega `1/20` remain
numerically positive but uncertified. The infinite tail remains wholly open.

`RHGarden.SuzukiMangoldtState` now compresses every unshifted prime cell to
two cumulative arithmetic numbers:

```text
X_n=(S_n,C_n),
X_(n+1)-X_n = Lambda(n+1)/sqrt(n+1) * (1,log(n+1)).
```

On the complete closed cell `[log n,log(n+1)]`, Lean checks the exact formula
`Psi(t)=A(t)-S_n*t+C_n`; the entering ramp cancels at the right endpoint.
The restricted dual `D_n(s)=max(s*t-A(t))` is compactly attained and has a
unique maximizer. Consequently cell safety is the single scalar inequality
`C_n>=D_n(S_n)`, and `suzukiCellMargin n := C_n-D_n(S_n)` satisfies a checked
cell-positivity equivalence. The existing cell-two certificate now implies
`suzukiCellMargin_two_pos` without repeating its analytic bounds.

The global checked representation is

```text
RH <-> SuzukiInitialNonnegative
       and forall n>=2, 0 <= suzukiCellMargin n.
```

This is only an equivalent open formulation. A proved dual perturbation
bound shows that the sparse Mangoldt jump itself cannot decrease the
same-cell margin. If `Lambda(n+1)=0`, the state is unchanged and the complete
margin change is replacement of `D_n` by `D_(n+1)`. The moving-cell dual is
therefore the exact next research frontier; no monotonicity across adjacent
cells has been claimed.

The next finite-cell experiment is to reuse the exact point-evaluation bound
library on unshifted cell 3 (or cell 5 if its arithmetic expression proves
simpler), then test shifted cell 2 at omega `1/10`. In parallel, the branch
cascade suggests studying why its winning cells are attached to particular
Mangoldt boundary events. A genuine infinite-tail certificate remains a
separate RH-sized requirement; a finite numerical scan cannot supply it.

The integer-cell indexing has now been collapsed further in
`RHGarden.SuzukiMangoldtBlocks`. A Mangoldt event is exactly a prime power,
and consecutive events `q<r` delimit a single constant state throughout
`[log q,log r]`. Lean checks the endpoint-inclusive formula
`Psi(t)=A(t)-S_q*t+C_q`, strict convexity, and a unique attained minimum on
the whole block. Its margin is both the minimum value of `Psi` on the block
and the finite minimum of the constituent integer-cell margins. Consequently
the sparse checked representation is `RH <-> SuzukiInitialNonnegative and
every consecutive Mangoldt-block margin is nonnegative`. This remains an
equivalent open formulation.

The half-line dual `AStar` and global state margin are now defined, and their
exact finite-difference update at each event is checked. Finiteness and
attainment of that unrestricted dual are the next analytic step; no
signed-area formula has been claimed.

`RHGarden.SuzukiDualDynamics` closes that analytic step without special-
function asymptotics. The unit curvature bound gives a quadratic lower bound
for `A`, hence boundedness and coercivity of `S*t-A(t)`. The unrestricted
dual is attained at a unique optimizer `tStar(S)`; `tStar` is monotone and
1-Lipschitz, and the elementary envelope inequalities prove
`AStar'(S)=tStar(S)`. Consequently every arithmetic update has the exact
signed-area form

```text
M_(n+1)-M_n = integral_{S_n}^{S_n+lambda}
  (log(n+1)-tStar(s)) ds.
```

At consecutive Mangoldt events the checked slope-surplus recurrence is
`delta_r=delta_q+(A'(log r)-A'(log q))-lambda_r`. Active blocks are exactly
those containing `tStar(S_q)` in their interior; on them the restricted
block margin equals the global dual margin. Inactive blocks attain their
minimum at the appropriate endpoint. These are structural equivalences and
updates only; no claim that all margins are nonnegative is made.

`RHGarden.SuzukiKickedFlow` now gives the exact event-boundary state
`(B_q,d_q)`, where `B_q=Psi(log q)` and `d_q=A'(log q)-S_q`. Across a
complete block `q->r`, Lean checks

```text
B_r = B_q + d_q*h + R
d_r = d_q + G - lambda_r,
```

with `h=log(r/q)`, archimedean slope recovery `G>=h`, convex remainder
`R>=h^2/2`, and `lambda_r=Lambda(r)/sqrt(r)`. It also checks the optimizer
sawtooth `x_r=x_q+h-DeltaT_r`, `0<=DeltaT_r<=lambda_r`, the kick-area bound
`0<=area<=lambda_r^2/2`, and the resulting two-sided event-margin bounds.

The boundary safety energy `E_q=B_q-max(-d_q,0)^2/2` is a certified lower
bound for the entire next block, so its universal nonnegativity plus the
initial interval would suffice for RH. A 78,733-block numerical scan below
one million events refutes this as a plausible invariant: `E_q` first turns
negative on `5->7` and reaches about `-0.21434087` on `59797->59809`, whose
candidate exact margin remains about `0.04362295`. Simple quadratic
potentials in the dual margin with displacement or slope coordinates also
decrease at tens of thousands of events. These failures are useful
`NumericalEvidence`: the next invariant must retain more of the exact convex
response than the unit-curvature quadratic envelope, and no tail positivity
claim follows.

`RHGarden.SuzukiTrueCurvature` strengthens this state machine using the exact
closed curvature. It proves `A''(t)>=(5/6)exp(t/2)` above `log 2`, hence the
uniform block bound `(5/6)sqrt(q)`, a curvature-weighted safety energy that
certifies the following complete block, and the corresponding sufficient RH
criterion (whose universal premise remains open). It also proves sharp
endpoint-dependent kick-area bounds, localizes every possible negative
global-margin update to negative post-event optimizer displacement, gives a
Lindley-style backlog recurrence, and bounds optimizer response by
`6*lambda/(5*exp(tStar/2))`.

The million-range Explorer scan covered 78,733 complete blocks. Unlike the
unit-curvature energy, the curvature-weighted energy had no numerical
failure; its smallest sampled value was about `0.02478999` on `5->7`.
This is only `NumericalEvidence`. The next research frontier is an exact
event-update law or arithmetic lower bound for this sharper energy, not an
extrapolation of the finite scan. Eventwise backlog clearing also fails as a
simple universal picture: only 29,865 of 78,733 scanned transitions had
`DeltaT<h`.

The numerical `explore-suzuki dual` regression through event integers below
5000 contains 710 complete blocks. Its candidate global dual margins stayed
positive, with the smallest about `0.02752057` on `3089->3109`, but event
updates split almost evenly in sign (357 negative, 353 positive). This is
`NumericalEvidence`, not a tail certificate. It shows that eventwise margin
monotonicity is not the right invariant. The exact active-block criterion—a
negative post-event slope surplus followed by a positive pre-impulse surplus
at the next event—is the clearest structural state variable exposed so far.

`RHGarden.SuzukiRootDynamics` moves the attained optimizer to
`uStar(S)=exp(tStar(S)/2)`. The curvature factor
`F(u)=1-1/(u^2*(u^4-1))` lies in `[5/6,1)` on the arithmetic range, and Lean
checks `uStar'(S)=1/(2F(uStar(S)))`. An exact cell-two bound proves the
interior regime at `q=2`; monotonicity of the cumulative Mangoldt slope then
extends it to every actual Mangoldt event. Consequently every complete block
has checked root-kick bounds `lambda/2 <= DeltaU <= 3lambda/5`, the exact
recurrence `x_r=x_q+sqrt(r)-sqrt(q)-DeltaU`, and the normalized recurrence
`rho_r=sqrt(q/r)rho_q+DeltaU/sqrt(r)`.

The dual-margin update has also been changed exactly from slope to root:

```text
DeltaM = 4 * integral F(u) log(sqrt(r)/u) du.
```

A 148,520-block numerical scan below about 1.99 million finds `rho` narrowing
toward one, with maximum `rho=1.00028018` after one million, but raw root
kicks exceed square-root gaps in 93,422 blocks. The crude gap condition fails
103,049 times. Natural quadratic overshoot potentials stay positive over the
scan but decrease at roughly half the events, so none is a Lyapunov invariant.
These are `NumericalEvidence` only. The exact next frontier is to exploit the
signed root-area over multiple events or find arithmetic control on cumulative
normalized overshoot; no RH positivity premise has been proved.

The root-discrepancy milestone makes that multi-event frontier exact. Define
`D(u)=A'(2 log u)-S_floor(u^2)`, where the step term is the cumulative weighted
Mangoldt slope. Lean checks that `D'=2F` between events, with derivative in
`[5/3,2)`, and that an event subtracts exactly `Lambda(q)/sqrt(q)`. It also
checks `(Psi(2 log u))'=2D(u)/u`, the complete-block weighted-area identity,
and the exact weighted-backlog loss on any negative excursion. An RH
prefix-area equivalence has been added as a representation only; it does not
establish its positivity side.

The Explorer now groups consecutive negative blocks into busy periods. Below
about 1.98 million it found 5,137 completed periods, 1,530 of them multi-event;
the longest contained 4,663 event states. The old `199 -> 211` danger belongs
to a three-state excursion starting at `193`, rather than an isolated cell.
This is numerical discovery, not proof evidence. The exact Abel identity
`sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi` connects arrival mass to a
finite Chebyshev-psi sum without assuming PNT or an RH-strength error bound.
The next mathematical frontier is a certified cumulative-arrival/service
bound strong enough to dominate an entire busy-period loss.

`RHGarden.SuzukiBusyPeriods` now LeanChecks the cumulative layer: exact
weighted-Mangoldt interval additivity and Abel subtraction, root-service
integrals and bounds, arrival/service excess telescoping, busy-period mass
balance, and a generic weighted-loss estimate. A proof-carrying
`SuzukiBusyPeriodCertificate` turns exact reserve/loss bounds into interval
positivity; `SuzukiExactPrefixPlusTailCertificate` records how a finite exact
prefix could be joined to a genuine tail theorem. Neither certificate has an
unconditional global inhabitant.

The pinned-library audit is quantitatively clarifying. Mathlib contains
global Chebyshev-psi bounds; Zeta23 contains an explicit global prefix bound
for `sum Lambda(n)/sqrt(n)` and kernel-checked PNT asymptotics. No usable
short-interval weighted-Mangoldt theorem was found. Applying a prefix bound at
the busy-period endpoint discards the large known starting prefix, so it is
structurally too coarse even before constants are optimized. The first exact
arithmetic improvement needed is a local bound on
`sum_{a^2<n<=b^2} Lambda(n)/sqrt(n)` that controls the induced weighted
backlog loss by the reserve `PsiRoot(a)`.

The two-million-range comparison makes the scale concrete. The tightest
comparable global-prefix/actual-local-arrival ratio was about `28.2423`, on
the `324431 -> 361201` excursion (actual arrival `62.8067`, service `62.8175`,
prefix expression `1773.8042`). Thus the checked global estimate is already
more than an order of magnitude too coarse in its best observed case; the
missing ingredient is interval sensitivity, not a small numerical sharpening.

The RH Garden Navigator under `ui/` consumes exported registry, frontier,
status, and bounded Explorer JSON. It is an `ExactExecutable` research tool;
its numerical plots remain `NumericalEvidence`, and Proof Mode makes that
boundary visible rather than changing any theorem status.

The pinned prime-bound audit found Mathlib's explicit Chebyshev bounds
`Chebyshev.psi_le`, `psi_le_const_mul_self`, and `psi_ge`; Zeta23 also proves
explicit `sum Lambda(n)/sqrt(n)` upper bounds (including its precise
partial-summation estimate), while `Zeta23.FromPNTPlus.MediumPNT` contains a
kernel-checked PNT asymptotic. These are unconditional, but their present
global error scales do not by themselves control each short multi-event busy
period. No zero-free or RH-strength estimate was imported into the new queue
representation.

## Short-interval arithmetic frontier

The local arithmetic input is now a named Lean interface rather than the
phrase "better prime bounds." `SuzukiWeightedShortIntervalProfileBound` asks,
for every root prefix `u` of an excursion beginning at `sqrt m`, for

```text
sum_{m < n <= floor(u^2)} Lambda(n)/sqrt(n)
  <= Service(sqrt m,u) + E(u).
```

`busyPeriod_safe_of_weightedMangoldt_profile` proves the excursion safe when
`E` is nonnegative and

```text
integral 2/u * (backlog(sqrt m) + E(u)) du
  <= PsiRoot(sqrt m).
```

The constant-profile specialization remains checked, but the ten-million
Explorer scan shows why it is not the final interface. On the numerical
`324431 -> 361201` excursion, the constant-excess budget is `0.5993354` while
the observed maximum prefix arrival/service excess is `0.6750328`; the scalar
rectangle is short by `0.0756974` even before replacing exact arrivals by a
theorem. The profile theorem charges error at its actual `2/u` weight and is
therefore the exact current target.

The same module now proves the interval-sensitive elementary bound

```text
Arrival(m,n) <= (n-m) * log(n) / sqrt(m+1).
```

It improves dramatically on throwing away the lower prefix, but is still
about `13.0255` times the terminal proxy on `324431 -> 361201` and reaches
about `16.7814` on the worst terminal comparison in the twenty-million scan. The pinned
global-prefix expression is `1773.8042` versus exact local arrival `62.8067`
on the former period, a factor `28.2423`.

The extended scan through twenty million found 14,451 completed numerical busy
periods. Of the 13,436 with a finite positive-width exponent, 219 have
`thetaEff = log(h)/log(x)` above `17/30`, while 13,063 are at or below `1/2`.
The short periods are numerous but generally have enormous reserve slack;
the hard large excursions instead had `thetaEff` around `0.77--0.84`. For
example, `324431 -> 361201` has `thetaEff=0.828406` and
`h/x^(17/30)=27.6998`; the widest scanned hard excursion beginning at
`6932909` has `thetaEff=0.837892` and ratio `71.6849`. No further substantive
constant-envelope failure appeared; the smallest positive relative slack in
the larger scan is about `0.0006811` at `12284411 -> 13067531`.

The export keeps two precision diagnostics distinct. `epsilonRequired` is
the requested terminal arrival headroom divided by exact arrival;
`prefixEpsilonRequired` is the stronger sampled prefix-envelope slack on the
same scale. The latter is what exposes the failure of a constant rectangle
and drives the profile-valued formal target.

The `17/30` line is external context from Guth--Maynard,
arXiv:2405.20552. It is `LiteratureCertified` metadata only: no effective
constants, weighted translation, or Lean formalization are claimed, and an
almost-all interval result would not suffice for every busy period.

A single numerical family `E = C h/(sqrt(x) log(x)^A)` does not fit all
scanned periods under the constant rectangle. Already for `A=0` the narrow
periods demand `C` about `0.790`, while the widest hard period allows at most
about `0.003997`. The next plausible architecture is consequently two-regime
and profile-valued: a local discrete bound for narrow intervals plus an
all-interval PNT-quality profile for long intervals. This is an exploratory
design constraint, not a theorem or evidence for RH.
