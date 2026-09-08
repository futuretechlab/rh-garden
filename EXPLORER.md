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
```

Other modes are `scan` and `cell`. The cell bounds restrict the reported
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

The numerical candidates currently found for the requested certification
tests are:

```text
omega=1/10, cell 2: t*=0.89237347, Psi=0.04090532, curvature=1.310889
omega=1/20, cell 5: t*=1.7799955,  Psi=0.03788844, curvature=2.2167661
```

Neither cell is Lean-certified yet. Universal curvature is no longer the
obstruction. The first exact missing ingredient is now narrower: rigorous
pointwise lower/upper bounds for `Psi_omega(x)` and
`|Psi_omega'(x)|` at a simple rational sample (starting with `x=9/10` for
cell 2). No decimal approximation is admitted as a certificate.

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
