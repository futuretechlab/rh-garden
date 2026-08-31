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
WeilQuadraticValues
WeilPositive
RiemannHypothesis
```

`ClassicalLiSequence` and `ClassicalLiRealSequence` are separate representation
nodes, with no certified edge between them yet. `LiPositive` and
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
- classical Li coefficients related to the registered Weil functional values;
- Nyman-Beurling and Lagarias criteria;
- hypotheses needed for global zero products and reconstruction.

Conjectural or unconstructed:

- real-valuedness inside this Lean development (although classical theory
  supplies the expected symmetry);
- a positive Gram or norm-square factorization for all Li coefficients;
- a self-adjoint Hilbert-Polya operator with exactly the required spectrum;
- a bridge unifying Li/Weil positivity with Nyman-Beurling geometry.

## Prospective Li-Weil-spectral corridor

The next research corridor is deliberately staged:

```text
Classical Li coefficients
  -> Weil quadratic functional
  -> positive-semidefinite representation?
  -> screw function
  -> finite-interval self-adjoint operators
  -> conjectural limiting operator
```

Lagarias relates generalized Li coefficients to values of Weil's quadratic
functional and obtains an RH criterion through positivity of their real parts
([arXiv:math/0404394](https://arxiv.org/abs/math/0404394)). This is published
provenance for the Li/Weil correspondence, not a LeanChecked edge.

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

The next small formal bridge is real-valuedness of every
`classicalLiCoefficient`, most plausibly from conjugation symmetry of xi or real
Taylor coefficients at `s = 1`. Only after that bridge should the project define
Lean positivity on the resulting real sequence. The broader bottleneck remains
a certified, non-circular universal positivity theorem for the full sequence or
its corresponding Weil test-function family.
