# RH Garden formal layer

This Lake project pins mathlib `v4.33.0` and uses the Lean toolchain named by
`lean-toolchain` (`leanprover/lean4:v4.33.0`). It imports
`Mathlib.NumberTheory.LSeries.RiemannZeta` and uses mathlib's own
`RiemannHypothesis`; it does not redefine that proposition.

Run:

```text
lake build
```

The Lean files and the successful kernel build are authoritative. The Haskell
`formal-status` command is navigation metadata, not a proof checker.

## Checked declarations

`RHGarden/MathlibAPI.lean` compile-time checks the requested upstream names:
`riemannZeta`, `completedRiemannZeta`, `completedRiemannZeta₀`,
`differentiable_completedZeta₀`, `completedRiemannZeta₀_one_sub`,
`completedRiemannZeta_one_sub`, `completedRiemannZeta_eq`, and
`RiemannHypothesis`.

`RHGarden/Xi.lean`:

- `riemannXi_zero`
- `riemannXi_one`
- `differentiable_riemannXi`
- `riemannXi_one_sub`
- `riemannXi_eq_completedRiemannZeta`

`RHGarden/Mobius.lean`:

- `liMobius_eq_one_sub_liStandard`
- `riemannXi_liMobius_eq_liStandard`

`RHGarden/CriticalLine.lean`:

- `XiT_neg`
- `xiRiemannHypothesis_iff_XiTZerosReal`
- `riemannHypothesis_iff_XiTZerosReal`

`RHGarden/ZetaZeros.lean`:

- `gamma_half_add_one_ne_zero_of_nontrivial`
- `zetaXiDenominator_ne_zero_of_nontrivial`
- `zetaXiNumerator_eq_zero_of_riemannZeta_eq_zero`
- `two_mul_riemannXi_eq_mul_zetaXiNumerator`
- `riemannXi_eq_zero_of_nontrivial_riemannZeta_zero`
- `IsNontrivialZetaZero.riemannXi_eq_zero`
- `riemannHypothesis_iff_nontrivialZero_re`
- `riemannZeta_eq_zero_of_riemannXi_eq_zero`
- `completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero`
- `riemannXi_pos_odd_ne_zero`
- `riemannXi_trivialZetaPoint_ne_zero`
- `isNontrivialZetaZero_of_riemannXi_eq_zero`
- `riemannXi_eq_zero_iff_nontrivialZetaZero`
- `riemannHypothesis_iff_xiRiemannHypothesis`

`RHGarden/LiFormal.lean`:

- `liMobiusSeries_constantCoeff`
- `liMobiusSeries_coeff_zero`
- `liMobiusSeries_coeff_succ`
- `liMobiusSeries_coeff`
- `one_add_liMobiusSeries`
- `geometricSeries_eq_inv_one_sub_X`
- `one_add_liMobiusSeries_eq_inv_one_sub_X`
- `normalizedXiTaylor_constantCoeff`
- `differentiable_normalizedXiAtOne`
- `analyticAt_normalizedXiAtOne`
- `normalizedXiAtOne_hasFPowerSeriesAt`
- `normalizedXiFPowerSeries_coeff`
- `normalizedXiTaylor_hasSum`
- `analyticAt_liMobius`
- `analyticAt_analyticLiXi`
- `liMobiusFPowerSeries_coeff_zero`
- `liMobiusFPowerSeries_coeff_succ`
- `liMobiusFPowerSeries_coeff_eq_powerSeries`
- `liMobius_hasFPowerSeriesAt`
- `analyticLiXi_hasFPowerSeriesAt_comp`
- `analyticLiXiFMS_eq_derivativeTaylor`
- `analyticLiXiPowerSeries_coeff`
- `analyticLiXiPowerSeries_constantCoeff`
- `analyticLiXiPowerSeries_isUnit`
- `analyticLiXiPowerSeries_mul_inv`
- `certifiedLiXiSeries_hasSum`
- `liXiSeries_constantCoeff`
- `liXiSeries_isUnit`
- `liXiSeries_mul_inv`
- `cubicXiAfterFormalMobius_coeff_zero`
- `cubicXiAfterFormalMobius_coeff_one`
- `cubicXiAfterFormalMobius_coeff_two`
- `cubicXiAfterFormalMobius_coeff_three`
- `cubicXiAfterFormalMobius_inv_coeff_zero`
- `cubicXiAfterFormalMobius_inv_coeff_one`
- `cubicXiAfterFormalMobius_inv_coeff_two`
- `cubicLiFormalCoefficient_zero`
- `cubicLiFormalCoefficient_one`
- `cubicLiFormalCoefficient_two`

The formal Li layer defines `normalizedXiTaylor` from iterated derivatives,
`liXiSeries` by formal substitution, and `liFormalLogDerivative` as
`derivative(G) * G⁻¹`. The separate `normalizedXiFPowerSeries` is the analytic
certificate: Lean proves it has the same scalar coefficients as
`normalizedXiTaylor` and converges locally to `normalizedXiAtOne`. A bare
`PowerSeries` still carries no convergence information. Lean also checks the
analyticity at zero of the Möbius coordinate and its composition with normalized
xi. The remaining identification of `PowerSeries.subst` with analytic FMS
composition, equality with an independently defined classical Li sequence,
real-valuedness, and Li's RH criterion remain unproved locally and therefore
`LiteratureCertified` where registered.

The certified composed route does not depend on a general interoperability
theorem. `liMobiusFPowerSeries` explicitly has coefficients `0,1,1,...` and is
certified for `z/(1-z)`. Composing its certificate with
`normalizedXiFPowerSeries`, then using uniqueness of local FMS expansions,
produces `liXiFPowerSeries`. `certifiedLiXiSeries` is the coefficient adapter
used by the authoritative formal logarithmic derivative. The older
`liXiSeries = normalizedXiTaylor.subst liMobiusSeries` remains present as a
second algebraic encoding. `liXiSeries_eq_certifiedLiXiSeries` proves its
equality with `certifiedLiXiSeries` coefficientwise.

`RHGarden/LiClassical.lean` now introduces three independent analytic notions:
the local logarithm germs, `liGeneratingCoefficient`, and Li's normalized
original derivative expression `normalizedClassicalLiCoefficient`. Lean checks
that the latter equals its shifted-coordinate form
`shiftedClassicalLiCoefficient`; this is only affine translation and does not
identify it with the generating sequence. The Taylor FMS for `liLocalLog` and
the composed FMS for `liGeneratingLog` both have local analytic certificates,
and uniqueness identifies the latter with its derivative Taylor FMS.

`RHGarden/LiCombinatorics.lean` proves the general finite identity

```text
[X^(n+1)] H(X/(1-X)) = [X^(n+1)] (1+X)^n H(X)
```

for every complex `PowerSeries H` with zero constant coefficient. It also
proves equality of the corresponding generating and original formal
functionals. `RHGarden/LiComposition.lean` counts compositions by length via
separator sets, proves the specialized scalar FMS/PowerSeries Mobius adapter,
and derives `liGeneratingCoefficient_eq_normalizedClassical`.

`RHGarden/LiNormalization.lean` independently defines the standard classical
coefficient `classicalLiCoefficient` using `log (riemannXi s)`. It proves the
standard xi-log is analytic at one, identifies its logarithmic derivative with
the normalized xi-log derivative on a neighborhood, and shows their difference
is locally constant. The `(n+1)`-st derivative of the resulting term `C*s^n`
vanishes. Consequently `normalizedClassicalLiCoefficient_eq_classical` and
`liGeneratingCoefficient_eq_classical` are `LeanChecked`; no global complex-log
additivity theorem is used. Xi conjugation symmetry and local principal-log
conjugation at `s=1` show the relevant derivatives are fixed by conjugation.
Thus `classicalLiCoefficient_im_eq_zero` and
`classicalLiCoefficient_eq_real` are `LeanChecked`. The zero-based
`classicalLiRealCoefficient n` corresponds to classical `lambda_(n+1)`;
`LiPositive` is defined on this sequence but deliberately unproved.

`RHGarden/PowerSeriesAPI.lean` records the pinned API. In mathlib v4.33.0,
composition is `PowerSeries.subst` under `PowerSeries.HasSubst`, not a method
named `comp`; field inversion uses `PowerSeries.inv`/`(·)⁻¹`.

The global pointwise correspondence
`riemannXi s = 0 ↔ IsNontrivialZetaZero s`, the RH/xi formulation, and the
RH/`XiT` formulation are checked equivalences of open propositions. They do not
prove any of those propositions.

`RHGarden/SuzukiScrew.lean` defines the occurrence-indexed spectral coordinate
`gamma=i*(rho-1/2)`, proves reciprocal-square summability in that coordinate,
and constructs the absolutely convergent zero-side Suzuki function and screw
kernel. The zero-side kernel identity, its critical-line Gram form, finite
height convergence, finite-height PSD, and limiting PSD under `XiTZerosReal`
are LeanChecked. `RHGarden/XiMidpoint.lean` uses the pinned Euler--Maclaurin
formula and remainder bound to prove `Re (riemannZeta (1/2)) < 0`, hence
`riemannXi (1/2) ≠ 0` and unconditional nonvanishing of every Suzuki spectral
denominator.

`RHGarden/XiNevanlinna.lean` defines Suzuki's centered function
`Q_xi(z)=i*logDeriv xi(1/2-i*z)`, proves its corrected occurrence partial
fraction, and LeanChecks `XiTZerosReal ↔ XiNevanlinna`. It also proves compact-
local normal convergence and continuity of the screw function, reduces the
screw axioms exactly to kernel PSD, and establishes the absolutely convergent
high-strip transform `(i/z^2) Q_xi(-z)` for the repository's Fourier and
spectral sign conventions.

`RHGarden/SuzukiPointwise.lean` formalizes the specialized Landau route for
Suzuki's pointwise criterion. It proves all polynomial Laplace-moment bounds,
the all-orders derivative identity, the nonnegative Tonelli/exponential-series
identity, and `nonnegativeLaplaceBoundaryPrinciple`. Analytic continuation of
the resulting full right-half-plane Psi transform then excludes nonreal xi
spectral zeros. Consequently the following are LeanChecked equivalences of
open propositions:

```text
SuzukiPsiNonnegative -> XiTZerosReal
XiTZerosReal <-> KernelPSD riemannScrewKernel
RiemannHypothesis <-> KernelPSD riemannScrewKernel.
```

This discharges the project-specific `ScrewToNevanlinnaBridge`; it does not
formalize general Krein--Langer theory and does not assert kernel positivity
or RH.

`RHGarden/SuzukiShifted.lean` defines Suzuki's equation (1.1) prime-side
components (including a genuinely finite von Mangoldt cutoff) and equation
(11.1) shifted Volterra family. Lean checks the prime contribution vanishes
for `0 <= t < log 2`, continuity/evenness/normalization of the shifted family,
positivity preservation for a nonnegative rightward shift, the parameterized
zero-free half-plane geometry, and
`RiemannHypothesis ↔ 0 ∈ SuzukiShiftedPositivitySet`.
`RHGarden/SuzukiTriangle.lean` proves the zero-side/prime-side identity by
extending pinned Zeta23's `C_c^2` explicit formula to the triangular cutoff
with normalized smooth convolutions. It checks the Fourier transform, uniform
zero-side domination, finite prime-side limit passage, Gamma domination, exact
vertical-digamma integral, and the Basel/Catalan/Lerch constants. The general
Volterra semigroup and shifted transform are LeanChecked in
`RHGarden/SuzukiShiftTransform.lean`. `RHGarden/SuzukiShiftedLandau.lean`
then proves the compact-tail Landau theorem and the checked implication
`SuzukiPsiShiftedEventuallyNonnegative omega -> XiZeroFreeRightOf omega`.
`RHGarden/SuzukiShiftedNevanlinna.lean` proves the translated spectral
partial fraction and the representation equivalence
`XiZeroFreeRightOf omega <-> XiShiftedNevanlinna omega`.
`RHGarden/SuzukiShiftedHerglotz.lean` then reconstructs the positive Cauchy
measure of every lower-half-plane shifted pole, sums those measures, builds
the associated Gram screw kernel, proves its one-sided transform, and uses a
checked Fourier uniqueness argument to identify the screw with
`-suzukiPsiShifted omega`. This discharges
`ShiftedNevanlinnaToPsiNonnegative` and both directions of Suzuki Theorem
11.1. See `SUZUKI_SHIFTED.md`.

`RHGarden/SuzukiLocalPositive.lean` differentiates the unconditional
prime-free formula on `0<t<log 2`. It identifies the quarter-lattice derivative
with `artanh(exp(-t/2)) + arctan(exp(-t/2))`, proves the `artanh` term tends to
`+infinity`, and proves the regular part is continuous and locally bounded.
Consequently Lean checks `exists_suzukiPsi_pos_near_zero`, a symmetric local
nonnegativity interval, and local diagonal nonnegativity of
`riemannScrewKernel`. No positivity claim is made for the whole prime-free
interval, for the full real line, or for off-diagonal kernel quadratic forms.

`RHGarden/SuzukiExplorer.lean` packages the checked global shifted criterion,
the exact shifted prime-side normalization, prime-cell floor/support lemmas,
and `SuzukiCellLowerBoundCertificate`. A certificate contains rational data
and explicit Lean proof fields for cell membership and both inequalities. The theorem
`exists_suzukiPsi_nonnegative_on_firstCertifiedInterval` is an end-to-end
formal smoke test obtained from the existing symbolic local theorem; it does
not import floating-point evidence. The Haskell Explorer and its trust model
are documented separately in `EXPLORER.md`.

The same file now proves cell-interior differentiability for both unshifted
and shifted Psi. Its generic `lowerBound_on_Icc_of_deriv_signs` theorem and
`SuzukiCellConvexCertificate` interface turn a rational critical bracket,
flank derivative signs, and a checked bracket lower bound into a whole-cell
nonnegativity theorem. This is an exact verifier architecture only: no
floating branch, crossing, or decimal minimum is imported into Lean.

`RHGarden/SuzukiConvexity.lean` proves the exact second-derivative identity
for the Volterra shift, the affine nature of each fixed Mangoldt cell sum,
and the closed curvature formula
`Psi''=y+1/y-y^3/(y^4-1)`. Lean checks `Psi''>=1` for every cell `n>=2`, so
all real shifts are strictly convex there, have at most one interior critical
point, and have no interior fold. Its generic
`lower_bound_of_secondDeriv_ge` theorem and
`SuzukiStrongConvexCellCertificate.positive_on_cell` reduce a whole-cell
proof to exact value and derivative bounds at one rational sample plus a
curvature bound.

`RHGarden/SuzukiCellTwo.lean` supplies the first complete certificate for an
actual unshifted prime cell.  It proves the exact cell formula and derivative,
derives rational bounds from pinned Taylor/series theorems, and checks
`Psi(9/10)>1/100` and `|Psi'(9/10)|<=13/100`.  With the curvature lower bound
one, `suzukiPsi_pos_cell_two` proves `Psi(t)>0` throughout the closed interval
`[log 2, log 3]`.  This is finite cell coverage only; no tail theorem follows.

`RHGarden/SuzukiMangoldtState.lean` gives the authoritative general cell
representation. It defines the cumulative slope `S_n` and intercept `C_n`,
proves the exact closed-cell identity `Psi=A-S_n*t+C_n` and sparse successor
updates, then defines the attained restricted archimedean dual `D_n`. The
dual objective is strictly concave with a unique maximizer, and
`suzukiCellMargin_nonneg_iff` reduces complete-cell nonnegativity to the one
scalar inequality `0<=C_n-D_n(S_n)`. Lean also checks the global equivalence
between `SuzukiPsiNonnegative` and the compact initial interval plus all
cell margins, and hence the corresponding RH equivalence. These theorems
re-express the open problem; they do not establish the margin family.

`RHGarden/SuzukiMangoldtBlocks.lean` replaces the unnecessarily fine integer
index by consecutive nonzero-von-Mangoldt events (equivalently prime powers).
It proves state constancy, one endpoint-inclusive formula and strict
convexity on each whole event block, unique attainment of the block minimum,
and identifies the block margin with the finite minimum of its cell margins.
Every natural `n>=2` lies in such a block, yielding the LeanChecked sparse
equivalence `RH <-> initial positivity and all block margins >= 0`. The file
also records the exact global-dual event update; boundedness and attainment
of the unrestricted half-line dual are supplied by
`RHGarden/SuzukiDualDynamics.lean`. That module proves quadratic coercivity,
unique half-line dual attainment, a monotone 1-Lipschitz optimizer,
`AStar'=tStar`, the exact signed-area event update and deficit recurrence,
and the active/inactive block geometry. These results expose a discrete
dynamical system but do not prove any open margin inequality.

`RHGarden/SuzukiKickedFlow.lean` gives the same dynamics in event-boundary
coordinates `B_q=Psi(log q)` and `d_q=A'(log q)-S_q`. It proves the exact
two-dimensional flow/kick recurrence, the bounds `G>=h` and `R>=h^2/2`, and
integral forms for the archimedean drift and remainder. The safety energy
`B_q-max(-d_q,0)^2/2` is checked as a conservative lower bound for the whole
following Mangoldt block and yields a conditional sufficient RH criterion;
no premise of that criterion is asserted. The module also formalizes the
Fenchel-gap explanation, optimizer-displacement sawtooth, active-block
crossing criterion, kick-area bound, and exact global-dual-margin update.

## Open targets

- Prove one of the equivalent RH formulations. No endpoint is discharged.
- Li-test Weil positivity and full Weil-form PSD remain open. The finite and
  infinite Weil-Li identities are checked, including absolute convergence of
  the infinite scalar and its equality to twice the classical Li coefficient.
- Prove one of the equivalent open positivity statements: pointwise
  `SuzukiPsiNonnegative`, `KernelPSD riemannScrewKernel`, Li positivity, or an
  appropriately strong Weil-form positivity theorem. The Suzuki converse and
  its specialized screw-to-Nevanlinna bridge are already checked.
- Move the certified shifted-positivity/zero-free parameter frontier left
  from the unconditional half-line `omega >= 1/2` toward `omega=0`. The
  endpoint is equivalent to RH and is not proved.
- Use the Suzuki Explorer only to discover candidate cell inequalities, then
  certify them independently through `SuzukiCellLowerBoundCertificate`,
  `SuzukiCellConvexCertificate`, or `SuzukiStrongConvexCellCertificate`.
  Universal curvature and unshifted cell 2 are checked; the immediate
  finite-cell task is to scale the exact pointwise value/first-derivative
  bounds to further cells (cell 3 is the next proof-simplicity candidate).
  A separate `SuzukiPsiTailCertificate` remains open and cannot be supplied
  by a finite scan.
- `RHGarden/XiZeroCutoff.lean` defines the global nonnegative xi divisor,
  analytic multiplicity, distinct radial and height `Multiset` cutoffs, exact
  cutoff counts, Lagarias height-ordered partial sums, and the open `Tendsto`
  star-convergence target. Height cutoffs are reflection-stable with
  multiplicity; radial cutoffs remain auxiliary and carry no such claim.
- A Lean derivative theorem for `liMobius`. The rational identity is checked by
  Haskell as `ExactExecutable`; it is not registered as `LeanChecked`.

## Cumulative Suzuki busy-period certificates

`RHGarden/SuzukiBusyPeriods.lean` adds the cumulative multi-event layer. It
defines finite weighted-Mangoldt arrivals, proves their exact interval Abel
identity by subtracting the checked Chebyshev-prefix formula, defines smooth
root service and arrival/service excess, and proves the telescoping
discrepancy/busy-period balance. `weightedBacklogIntegral_le_unweighted` is a
generic interface for converting an unweighted backlog-area estimate into the
actual `2/u` loss. `SuzukiBusyPeriodCertificate` and
`SuzukiExactPrefixPlusTailCertificate` are proof-carrying interfaces only:
they accept exact Lean hypotheses and do not trust generated JSON or floating
point data. No global certificate value or RH conclusion is supplied.

The same module now exposes the missing local arithmetic theorem at two
resolutions. `SuzukiWeightedShortIntervalBound` is the coarse constant-excess
form. `SuzukiWeightedShortIntervalProfileBound` permits a nonnegative prefix
error `E(u)`, and `busyPeriod_safe_of_weightedMangoldt_profile` charges that
error through the exact `2/u` loss weight before concluding positivity on the
whole root interval. This profile theorem is LeanChecked; no global inhabitant
of its arithmetic premise is supplied.

`weightedMangoldtInterval_le_localWidth` is an unconditional, interval-aware
fallback:

```text
sum_{m<k<=n} Lambda(k)/sqrt(k)
  <= (n-m) log(n) / sqrt(m+1).
```

It uses only `vonMangoldt_le_log` and monotonicity of the square root. It is
quantitatively insufficient for the hard long excursions, but it cleanly
separates the remaining short-interval cancellation problem from the earlier
global-prefix loss.

`RHGarden/SuzukiTrueCurvature.lean` retains the growing archimedean
curvature. It kernel-checks the factorized curvature formula and the bound
`A''(t)>=(5/6)exp(t/2)` for `t>=log 2`, yielding block curvature
`(5/6)sqrt(q)`. The resulting curvature safety energy is a certified lower
bound for the exact block margin and gives a conditional sufficient RH
criterion; its universal premise is not proved. The module also proves the
sharp kick-area bounds
`DeltaT^2/2 <= area <= lambda*DeltaT-DeltaT^2/2`, the associated
final-displacement margin bounds and decrease localization, a backlog
recurrence, and the true-curvature response estimate
`DeltaT <= 6*lambda/(5*exp(tStar/2))`.

No proof of RH is claimed.

`RHGarden/SuzukiRootDynamics.lean` introduces
`uStar(S)=exp(tStar(S)/2)` and the elementary curvature factor
`F(u)=1-1/(u^2*(u^4-1))`. It proves `5/6<=F<1`, the interior derivative
`uStar'=1/(2F(uStar))`, and the finite root-response bounds
`lambda/2<=DeltaU<=3lambda/5`. The exact cell-two derivative certificate plus
Mangoldt-slope monotonicity shows that every actual event state is in this
interior regime, so block-level kick bounds need no extra assumption. Event
displacement and normalized ratio obey exact square-root recurrences. Finally,
the module kernel-checks the full change of variables

```text
DeltaM = 4 * integral_{uBefore}^{uAfter}
  F(u) * log(sqrt(r)/u) du.
```

This is a representation of the open margin dynamics, not a proof that the
margins are nonnegative.

`RHGarden/SuzukiRootDiscrepancy.lean` exposes the underlying hybrid sawtooth.
It defines the smooth root slope `P(u)=A'(2 log u)`, the right-continuous
arithmetic slope `S_floor(u^2)`, and their discrepancy `D`. On complete
Mangoldt blocks the file proves

```text
D'(u)=2*F(u),                 5/3 <= D'(u) < 2,
Psi(2 log b)-Psi(2 log a) = integral_a^b 2*D(u)/u du,
```

while event jumps subtract exactly `Lambda(r)/sqrt(r)`. It packages the
blockwise prefix-area form of the RH criterion, defines negative excursions
and their weighted-backlog loss, and proves the service/arrival recurrence.
The public exact Abel identity
`sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi` expresses cumulative weighted
arrival mass through a finite Chebyshev-psi sum and integral. No asymptotic
prime bound, global prefix positivity, or proof of RH is claimed.

No proof of RH is claimed.
