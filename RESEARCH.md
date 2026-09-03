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

## Garden trust state

The following representation edges are LeanChecked:

```text
XiHeightZeroCutoff -> LiStarPartialSums
XiHeightZeroCutoff -> FiniteWeilCutoffValues
LiStarConvergence -> WeilLiQuadraticValues
FiniteWeilCutoffValues -> WeilLiQuadraticValues
ClassicalLiRealSequence <-> WeilLiQuadraticValues.
```

The criterion reductions

```text
LiPositive <-> WeilLiPositive
```

are also LeanChecked. No edge promotes either proposition to a proof, and no
edge connects the unformalized full `WeilFormPSD` criterion to RH.

## Exact next frontier

The representation and convergence questions for the Li test family are now
closed. The next mathematical frontier is a certified, non-circular proof of
nonnegativity of the equivalent sequences—either `LiPositive` or
`WeilLiPositive`—or a genuinely stronger construction proving the full Weil
form positive semidefinite. A positive Gram/norm-square factorization, a full
Weil test-space development, or an independently certified operator-theoretic
argument would be new mathematics; none is claimed here.

The later Suzuki screw-function and Hilbert--Polya operator programs remain
research directions only. They must not be registered as proofs without a
finite, auditable kernel term and all required analytic identifications.
