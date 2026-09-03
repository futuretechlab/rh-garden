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

Only `ScrewToNevanlinnaBridge` remains literature-certified. The pinned
library contains no Krein--Langer or equivalent positive-kernel theorem from
which that implication can be instantiated.

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
RiemannScrew -> XiNevanlinnaTransformHighStrip
SuzukiGramKernel -> RiemannScrewKernel
```

The criterion reductions

```text
LiPositive <-> WeilLiPositive
```

are also LeanChecked. No edge promotes either proposition to a proof, and no
edge connects the unformalized full `WeilFormPSD` criterion to RH.

## Exact next frontier

The next Suzuki frontier is the single isolated proposition
`ScrewToNevanlinnaBridge`, from kernel PSD to `XiNevanlinna`. The downstream
implication `XiNevanlinna -> XiTZerosReal` is now LeanChecked, as are midpoint
nonvanishing, literal denominators, continuity, and the high-strip transform.

No positivity theorem for the Li sequence or full Weil form is claimed.
