# Research corridor: xi to the Li sequence

**Status: this project does not currently prove the Riemann Hypothesis.** The
implemented corridor organizes known identities and exposes missing proof
obligations. The local route from the normalized xi generating germ to the
independently defined standard classical Li coefficients is now kernel checked;
the positivity and RH-criterion bridges remain literature metadata.

## Common source and target

The source is Riemann's completed function

```text
xi(s) = 1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s).
```

The zero/Hadamard route and the Mobius/logarithmic-derivative route both reach
Li coefficients with index convention `n >= 1`. Taking a zero multiset is
information loss: reconstruction requires normalization, growth, exponential
factors, and analytic hypotheses that are not silently assumed. The registered
zero formula

```text
lambda_n = sum_rho [1 - (1 - 1/rho)^n]
```

retains its standard limiting interpretation and remains
`LiteratureCertified`.

The formal analytic route now continues through fully checked local steps:

```text
XiFunction
  -> XiTaylorAtOne
  -> XiAfterFormalMobius
  -> LiGeneratingLog
  -> LiGeneratingSequence
  -> NormalizedClassicalLiSequence
  -> ClassicalLiSequence
```

The last edge is branch-conscious. Lean compares logarithmic derivatives near
`s = 1`, proves the two logarithms differ locally by a constant, and observes
that the `(n+1)`-st derivative of `C*s^n` vanishes. It does not assume a global
complex-log addition law.

## Distinct sequence and proposition layers

The research map keeps these notions distinct:

```text
ClassicalLiSequence
ClassicalLiRealSequence
LiPositive
WeilLiTestFunctions
WeilQuadraticValues
WeilPositive
RiemannHypothesis
```

`ClassicalLiSequence` and `ClassicalLiRealSequence` are separate representation
nodes joined by a `LeanChecked` coefficientwise real-embedding theorem. `LiPositive` and
`RiemannHypothesis` are criterion propositions. `WeilPositive` is a separate
property of `WeilQuadraticValues`. Sequence identification, real-valuedness,
positivity, and RH equivalence therefore cannot be conflated by route search.

Li's `LiPositive <-> RiemannHypothesis` criterion remains literature-certified.
Finite positivity computations cannot satisfy its universal quantifier. The
representation graph records both directions of the literature relationship
between the standard classical Li sequence and the specified Weil
quadratic-functional values. It does **not** assume Weil positivity.

## Status ledger

Implemented and kernel checked:

- the xi/nontrivial-zeta-zero correspondence and RH/xi critical-line
  reformulations (equivalences of open propositions, not proofs of them);
- analytic xi Taylor and local logarithm germs;
- the finite FMS/PowerSeries Mobius coefficient adapter;
- generating coefficients equal normalized classical Li coefficients;
- the standard local xi logarithm at `s = 1`;
- local equality of normalized and standard logarithmic derivatives;
- local constancy of their difference and annihilation of `C*s^n`;
- generating coefficients equal independently defined standard classical Li
  coefficients.

Literature-certified only:

- the zero-sum formula and its analytic summation convention;
- Li positivity equivalent to RH;
- the real classical Li sequence mapped to Lagarias's registered test functions
  and Weil functional values (see `LAGARIAS_WEIL.md`);
- Nyman-Beurling and Lagarias criteria;
- hypotheses needed for global zero products and reconstruction.

Conjectural or unconstructed:

- a positive Gram or norm-square factorization for all Li coefficients;
- a self-adjoint Hilbert-Polya operator with exactly the required spectrum;
- a bridge unifying Li/Weil positivity with Nyman-Beurling geometry.

## Prospective Li-Weil-spectral corridor

The next research corridor is deliberately staged:

```text
ClassicalLiRealSequence
  -> LiZeroSumSequence
  -> FiniteWeilCutoffValues
  -> WeilQuadraticValues
  -> WeilPositive
  -> RiemannHypothesis

WeilLiTestFunctions
  -> FiniteWeilCutoffValues
```

The later spectral research corridor is:

```text
Weil quadratic functional
  -> positive-semidefinite representation?
  -> screw function
  -> finite-interval self-adjoint operators
  -> conjectural limiting operator
```

Lagarias defines `G_n(s)=1-(1-1/s)^n` and proves
`||G_n||_W^2=2 Re(lambda_n)` in equations (3.2)--(3.4); exact hypotheses and
conventions are recorded in `LAGARIAS_WEIL.md`. He obtains an RH criterion through positivity of their real parts
([arXiv:math/0404394](https://arxiv.org/abs/math/0404394)). This is published
provenance for the Li/Weil correspondence, not a LeanChecked edge.

The finite algebraic core is now Lean checked in `RHGarden.WeilFinite`: (3.5),
(3.6), finite (3.3), its diagonal form, and the `2*Re` form for explicitly
reflection-stable `Multiset` cutoffs. This upgrades only
`WeilLiTestFunctions -> FiniteWeilCutoffValues`. Derivative Li to the
conditionally star-convergent zero sum, selection of cofinal zero cutoffs, and
the absolutely convergent finite-to-infinite Weil limit remain literature-only
analytic boundaries. In particular, the norm-square notation does not prove
the Weil form positive semidefinite.

The next representation layer is also Lean checked, without convergence:

```text
XiFunction -> XiDivisor -> XiRadialZeroCutoff
XiDivisor -> XiHeightZeroCutoff
XiHeightZeroCutoff -> LiStarPartialSums
XiHeightZeroCutoff -> FiniteWeilCutoffValues
```

`xiZeroHeightCutoff T` is the divisor support in `|Im rho|<=T`, repeated by
analytic multiplicity, matching Lagarias equation (6.106). Weil reflection
preserves height and analytic multiplicity exactly, so this cutoff is
reflection-stable. `xiZeroRadialCutoff` remains a separate auxiliary object for
the radial cuts used in Lagarias's interpolation section. `LiStarConvergesTo`
is only a `Tendsto` proposition. The edges
from partial sums to convergence, from derivative Li to the negative-index star
limit, and from convergent finite identities to the infinite Weil functional
remain literature-only. Radial cutoffs are not claimed reflection-stable: only
their unconditional norm displacement bound by one is checked.

Suzuki's screw-function program supplies a continuous-function framework for
studying Weil's distributional quadratic form. Earlier work develops RH
equivalences and unconditional partial results through the zeta screw function
([arXiv:2206.03682](https://arxiv.org/abs/2206.03682)). The 2026 work organizes
Weil's quadratic form through that framework and studies finite-interval
self-adjoint operators without assuming RH
([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)). Its limiting
self-adjoint realization with spectrum equal to the zero ordinates is explicitly
a conjecture. The project must not register that limit as proved or use it to
upgrade Weil positivity, Li positivity, or RH.

## Next mathematical bottleneck

Real-valuedness of every `classicalLiCoefficient` is now Lean checked from xi
conjugation symmetry and local principal-log symmetry at `s=1`. `LiPositive`
is defined on the real sequence but remains unproved. The zeta/xi multiplicity
seam and the exact half-open height-window count representation are now also
Lean checked in `RHGarden.ZetaMultiplicity`. The proposition
`XiLocalZeroCountBound` is deliberately unproved; the equivalent zeta theorem
is externally formalized by Anthropic's Apache-2.0 `zeta-23-lean` artifact at
the revision recorded in `ZETA23_COMPATIBILITY.md`.

The next formal boundary is integrating or selectively adapting that local
height-count theorem. Reconnaissance found that upstream's local
logarithmic-derivative partial fraction has a slightly smaller raw dependency
closure but supplies only a finite disk-local approximation, not the paired
height limit needed for `Σ 1/ρ`; it is therefore not presently a cheaper
star-convergence route. Once the local count is available, the generic
reciprocal-square summability argument is small enough to adapt independently.
The remaining special step is the `n=1` paired cancellation argument. Separately, the
infinite Weil form needs absolute-convergence control. The broader bottleneck remains a certified, non-circular
universal positivity theorem; this sprint claims none.
