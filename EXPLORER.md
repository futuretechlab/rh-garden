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

## Running a scan

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

## Candidate minima and metadata

Each cell search uses endpoints, dense samples, and linearly interpolated
derivative sign changes. It reports a candidate minimum, not a rigorous
minimum. Alongside it the Explorer records

- `Psi_omega(t)/t` and `Psi_omega(t)/t^2`;
- `exp(-t/2) Psi_omega(t)` and `exp(-omega*t) Psi_omega(t)`;
- `omega*t`;
- neighboring prime gaps;
- Chebyshev `theta(n)`, `psi(n)`, and `psi(n)-n`;
- prime-power events at cell boundaries.

A modest scan over `0.05 <= t <= 8` found candidate minimizing branches at
the lower endpoint for `omega=0.125`, then in cells 2, 5, 14, and 207 as the
sampled parameter decreased through `0.10`, `0.05`, `0.025`, and `0`.
At `omega=0` the candidate lies at `t` about `5.338`, with nearby dangerous
cells clustered around 207--216. This apparent branch cascade is a search
lead only. Finer sampling, higher precision, and exact interval certification
are all still required.

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
