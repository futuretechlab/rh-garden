# zeta-23-lean compatibility reconnaissance

Status: the successful `integration/zeta23-rc2` experiment is merged into
`main`. The RH Garden formal layer uses Zeta23's rc2 Lean and Mathlib pins. The
exact pinned Zeta23 dependency is accepted by the same Lean kernel, and a small
adapter proves `RHGarden.xiLocalZeroCountBound` and hence unconditional
existence of all height-ordered Li star limits.

## Reference revision and pins

Repository: `https://github.com/anthropics/zeta-23-lean`

- inspected commit: `2bafb8c88f177284a2123b5fefa2ff84e2365eb6`
  (`Merge pull request #24 from anthropics/zeta23-authorship`);
- license: Apache-2.0;
- Lean: `leanprover/lean4:v4.33.0-rc2`;
- Mathlib: commit `51e6992efd06126df61a496bebf8f49482a4e129`
  (`v4.33.0-rc2`).

RH Garden `main` uses Lean `v4.33.0-rc2` and Mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129` (`v4.33.0-rc2`), matching the
upstream Zeta23 pins exactly.

The audited Git URL currently checks out a monorepo root at this commit; its
Lake package is in `zeta23/`. Accordingly the pinned dependency records
`subDir = "zeta23"` rather than claiming the dependency source is vendored.

## RC2 integration result

- unchanged RH Garden source build: successful, 3639 jobs;
- source compatibility adaptations required: zero files, zero lines;
- imported theorem: `Zeta23.RvM.zeta_local_zero_count`;
- imported theorem axioms: `propext`, `Classical.choice`, `Quot.sound` only;
- adapter theorems: `zeta23_zerosIn_eq_rhGarden`,
  `zeta23_Ncount_eq_rhGarden`, `xiLocalZeroCountBound`;
- activated result: `liStarConvergence`.

The adapter is externally authored at its analytic input but LeanChecked in
proof trust: Zeta23 remains a pinned dependency and the theorem is checked by
the same kernel invocation as RH Garden. Proof provenance and proof trust are
therefore recorded separately.

## Zero representation

Upstream module `Zeta23.Statement` defines:

```lean
def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def zeroMult (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

def zerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

def Ncount (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ
```

`Zeta23.ZeroConfig` stores a set of distinct points and a separate natural
multiplicity function. Its window convention is `(T₁,T₂]`, not an absolute
height cutoff. The unconditional `zetaZeroConfig` has precisely this carrier
and multiplicity.

## Riemann--von Mangoldt and local count

The cumulative/dyadic result is
`Zeta23.RvM.rvM_main` in `Zeta23/RvM/MainTerm.lean`:

```lean
theorem rvM_main (hΓ : GammaFacts) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ)
        - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T
```

The packaged theorem is `Zeta23.RvM.riemannVonMangoldt` in
`Zeta23/RvM/Statement.lean`:

```lean
theorem riemannVonMangoldt (hΓ : GammaFacts) :
  RiemannVonMangoldt zetaZeroConfig
```

The exact two-sided unit-height theorem is
`Zeta23.RvM.zeta_local_zero_count` in `Zeta23/RvM/LocalCount.lean`:

```lean
theorem zeta_local_zero_count :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
      (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
```

The equivalent abstract-configuration form is
`Zeta23.RvM.zetaZeroConfig_local_count`, with `zetaZeroConfig.N` replacing
`Ncount`.

## Required RH Garden adapters

The representation correspondence is:

| Upstream | RH Garden | Required adapter |
|---|---|---|
| `IsNontrivialZero ρ` (zeta zero plus open strip) | `IsNontrivialZetaZero ρ`, equivalently `riemannXi ρ = 0` | prove equivalence using `riemannXi_eq_zero_iff_nontrivialZetaZero` and `riemannXi_zero_re_mem_Ioo` |
| `zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat` | `xiMultiplicity ρ = analyticOrderNatAt riemannXi ρ` | prove equality of analytic orders at nontrivial zeros by removing the nonvanishing gamma/polynomial factors relating zeta and xi |
| `zerosIn t (t+1)` | xi-divisor support with `t < ρ.im ∧ ρ.im ≤ t+1` | introduce a finite height-window support/count or an equivalent filtered Multiset theorem |
| `Ncount t (t+1)` | sum of `xiMultiplicity` in that window | prove a `finsum`/finite-sum equality from the preceding two adapters |
| symmetric star cutoff `|ρ.im| ≤ T` | `xiZeroHeightCutoff T` | assemble positive and negative windows only after the local window-count adapter; no change to cutoff semantics |

The central multiplicity adapter is now LeanChecked in
`RHGarden.ZetaMultiplicity`:

```text
(analyticOrderAt riemannZeta ρ).toNat
  = analyticOrderNatAt riemannXi ρ
```

under the nontrivial-zero/open-strip hypotheses.

The same module defines the half-open window Multiset/count and proves
`xiHeightWindowMultiplicityCount_eq_zeta`. `RHGarden.Zeta23LocalCount` then
identifies the upstream and RH Garden counts, proves `xiLocalZeroCountBound`,
and derives unconditional `liStarConvergence`.

## Dependency feasibility

A temporary stable-4.33.0 experiment showed that Lake resolves the single
package named `mathlib` to Zeta23's rc2 commit. RH Garden therefore adopted the
matching rc2 Lean and Mathlib pins on `main`; Lake does not install two
revisions of one package side by side.

The transitive `Zeta23.*` import closure of `Zeta23.RvM.LocalCount` contains 21
source modules and approximately 7,846 lines. It includes the large
`FromPNTPlus.ZetaBounds` and residue-calculus stack. There are no extra
non-Mathlib Lake packages beyond dependencies inherited from Mathlib, but this
is not a small copy operation. A selective stable port should start from the
local-count theorem and adapt its proof prerequisites, preserving upstream
headers, rather than vendor the complete repository.

## Explicit formula

The exact unconditional theorem is
`Zeta23.WeilEF.EF_lit_zetaZeroConfig` in `Zeta23/WeilEF/Main.lean`:

```lean
theorem EF_lit_zetaZeroConfig :
  Zeta23.EF.EF_lit zetaZeroConfig
```

`EF_lit Z` quantifies over `k : ℝ → ℂ` with `ContDiff ℝ 2 k` and
`HasCompactSupport k`. It asserts both:

```lean
Summable (fun ρ : Z.carrier =>
  (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ))
```

and equality of that `tsum` with `EF.literatureRHS k`, containing the pole,
prime, and gamma terms. Distinct zeros are represented by the carrier subtype;
multiplicity is the explicit `Z.mult ρ` factor. The paper-form bridge gives
compactly supported `C²` test functions and an absolutely convergent Weil
scalar product.

This is not immediately the RH Garden `weilLiTest`: Lagarias's rational
`G_n(s)` is neither the upstream compactly supported real test function `k`
nor directly its Fourier transform. A test-function/transform adapter would be
a separate analytic development.

## Reciprocal-zero and star-sum inventory

Upstream proves:

- `Zeta23.WeilEF.zero_sum_inv_sq`: summability of
  `zeroMult ρ / (1 + normSq (gammaOf ρ))`;
- `Zeta23.WeilEF.EF_zero_sum_summable`: absolute convergence for the decaying
  Fourier transforms of compactly supported `C²` tests;
- `Zeta23.WeilEF.zero_sum_limit`: convergence of finite height-truncated zero
  sums for those tests to their `tsum`;
- local logarithmic-derivative partial-fraction estimates, including
  `zeta_logDeriv_partial_fraction` and an explicit variant.

No declaration defines Li coefficients, proves convergence of the Lagarias
height-ordered sum of `1/ρ`, or identifies a derivative Li coefficient with a
star zero sum. In particular, `zero_sum_inv_sq` supplies the higher-power
majorant but not the conditionally convergent `k = 1` reciprocal-zero term.

## Integrated star-convergence route

```text
RH Garden LeanChecked
  xi divisor, multiplicity, height cutoff, finite G_n algebra
        |
        v
LeanChecked adapters
  zeta-zero predicate equivalence
  zeta-order = xi-order at nontrivial zeros
  upstream Ncount = RH Garden height-window multiplicity count
        |
        v
upstream, pinned external dependency
  zeta_local_zero_count
  zero_sum_inv_sq / its underlying unit-window summation
        |
        +--> RH Garden convergence algebra
        |      expand G_n(ρ) as a finite sum of ρ⁻ᵏ
        |      absolute convergence for k ≥ 2
        |      paired height convergence of Σ 1/ρ
        |      all integer-indexed Li star limits exist
        |
        +--> remaining Hadamard/log-derivative boundary
               identify its limit through xi's logarithmic derivative
               derivative-defined Li = negative-index star limit
```

The explicit-formula theorem may eventually offer a second route, but its test
class does not contain the non-decaying Li test without an approximation and
limit argument.

## Current analytic boundary

The zero-representation seam, local count, reciprocal-power convergence, and
height-star convergence now build together on `main`. The remaining theorem is
value identification: a xi-specific genus-one Hadamard factorization, locally
uniform logarithmic-derivative passage near `s = 1`, determination of the
linear exponential constant from xi symmetry, and identification of the
classical Li coefficient with the corresponding negative-index star limit.

## Partial-fraction route comparison

`Zeta23.WeilEF.zeta_logDeriv_partial_fraction` is in
`Zeta23/WeilEF/Landau.lean`. It produces, for `|t| ≥ 6`, a finite set of zeta
zeros in a fixed disk about `2+it`, bounds their total analytic multiplicity by
`C log(|t|+3)`, and approximates `logDeriv riemannZeta s` by the finite sum
`Σ mρ/(s-ρ)` on a smaller disk. It is a local finite sum: not a `tsum`, not a
height-symmetric limit, and not a packaged conditionally convergent reciprocal
zero sum.

Its transitive upstream closure is 17 modules and about 7,630 lines. It does
not use `RvM.LocalCount`, but does use the substantial
`FromPNTPlus.StrongPNTPrefix`, zeta-growth, residue-calculus, and zeta-bounds
stack. The numeric theorem
`Zeta23.WeilEF.zeta_logDeriv_partial_fraction_explicit` in `Effective.lean`
has a 36-module, approximately 14,016-line closure and that module also imports
local counting and contour/gamma machinery.

By comparison, `Zeta23.RvM.LocalCount` has a 21-module, approximately
7,846-line closure. Although the non-explicit partial-fraction closure is four
modules smaller, it does not close the global paired `Σ 1/ρ` limit and hence is
not a cheaper Li-star route.

The generic core `zero_sum_inv_sq_gen` is much cheaper than its file-level
closure suggests. The full `ZeroSummability.lean` import closure is 38 modules
and about 12,043 lines because the file also contains zeta-specific and
explicit-formula specializations. The generic proof itself occupies roughly
the first 160 lines and needs only elementary integer-weight summability,
finite-sum grouping, a small abstract local-window-count interface, and the
zero-coordinate bookkeeping. It can be adapted independently once
`XiLocalZeroCountBound` is available. `zero_sum_limit`, by contrast, has a
53-module, approximately 17,142-line file closure because it imports contour
and explicit-formula infrastructure; its underlying monotone finite-set
exhaustion argument is elementary but is specialized to upstream's decaying
Fourier test functions.
