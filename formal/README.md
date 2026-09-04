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

## Open targets

- Prove one of the equivalent RH formulations. No endpoint is discharged.
- Li-test Weil positivity and full Weil-form PSD remain open. The finite and
  infinite Weil-Li identities are checked, including absolute convergence of
  the infinite scalar and its equality to twice the classical Li coefficient.
- Prove one of the equivalent open positivity statements: pointwise
  `SuzukiPsiNonnegative`, `KernelPSD riemannScrewKernel`, Li positivity, or an
  appropriately strong Weil-form positivity theorem. The Suzuki converse and
  its specialized screw-to-Nevanlinna bridge are already checked.
- `RHGarden/XiZeroCutoff.lean` defines the global nonnegative xi divisor,
  analytic multiplicity, distinct radial and height `Multiset` cutoffs, exact
  cutoff counts, Lagarias height-ordered partial sums, and the open `Tendsto`
  star-convergence target. Height cutoffs are reflection-stable with
  multiplicity; radial cutoffs remain auxiliary and carry no such claim.
- A Lean derivative theorem for `liMobius`. The rational identity is checked by
  Haskell as `ExactExecutable`; it is not registered as `LeanChecked`.

No proof of RH is claimed.
