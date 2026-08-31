# zeta-23-lean compatibility reconnaissance

Status: reference-only reconnaissance. No upstream theorem is imported into the
RH Garden build, and no trust classification is upgraded by this note.

## Reference revision and pins

Repository: `https://github.com/anthropics/zeta-23-lean`

- inspected commit: `2bafb8c88f177284a2123b5fefa2ff84e2365eb6`
  (`Merge pull request #24 from anthropics/zeta23-authorship`);
- license: Apache-2.0;
- Lean: `leanprover/lean4:v4.33.0-rc2`;
- Mathlib: commit `51e6992efd06126df61a496bebf8f49482a4e129`
  (`v4.33.0-rc2`).

RH Garden uses Lean `v4.33.0` and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` (`v4.33.0`).

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

The central missing adapter is therefore not set membership but multiplicity:

```text
(analyticOrderAt riemannZeta ρ).toNat
  = analyticOrderNatAt riemannXi ρ
```

under the nontrivial-zero/open-strip hypotheses.

## Dependency feasibility

A temporary stable-4.33.0 Lake project required both Mathlib `v4.33.0` and the
local upstream package. Lake resolved the single package named `mathlib` to the
upstream rc2 commit `51e6992...`, and also selected the upstream rc2-era
transitive package revisions. It warned that these differ from the stable
Mathlib dependency graph. Thus a direct dependency cannot preserve RH Garden's
current stable Mathlib pin; Lake does not install two revisions of one package
side by side.

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

## Minimal star-convergence route

```text
RH Garden LeanChecked
  xi divisor, multiplicity, height cutoff, finite G_n algebra
        |
        v
small adapters
  zeta-zero predicate equivalence
  zeta-order = xi-order at nontrivial zeros
  upstream Ncount = RH Garden height-window multiplicity count
        |
        v
upstream, not yet integrated
  zeta_local_zero_count
  zero_sum_inv_sq / its underlying unit-window summation
        |
        +--> small new algebra
        |      expand G_n(ρ) as a finite sum of ρ⁻ᵏ
        |      absolute convergence for k ≥ 2
        |
        +--> substantial missing analysis
               paired height convergence of Σ 1/ρ
               identify its limit through xi's logarithmic derivative
               derivative-defined Li = negative-index star limit
```

The explicit-formula theorem may eventually offer a second route, but its test
class does not contain the non-decaying Li test without an approximation and
limit argument.

## Recommended integration boundary

First port or adapt only the zero-representation seam and
`zeta_local_zero_count` to stable Mathlib, then expose one RH Garden theorem
whose conclusion is stated directly with `xiMultiplicity` on `(t,t+1]`.
Only after that theorem builds in RH Garden should the graph edge be upgraded.
The next implementation after local counting should extract absolute
convergence for reciprocal powers `k ≥ 2`; the paired `Σ 1/ρ` limit remains a
separate analytic milestone.
