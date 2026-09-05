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
shifted positivity is consequently upward closed. The exact next formal
frontier is Suzuki Theorem 11.1: eventual, rather than global, nonnegativity
requires a compact-tail version of the Landau argument, and the reverse
zero-free-to-eventual-positive direction still needs its shifted asymptotic
argument.

On the shifted side the first exact obstruction remains a two-variable Fubini calculation for
nested Volterra integrals, needed for both the semigroup law and equation
(11.2); the shifted Landau/eventual-positivity theorem comes after it. Full
Weil-form PSD and general Krein--Langer remain separate.
