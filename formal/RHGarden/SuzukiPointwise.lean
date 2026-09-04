import RHGarden.KernelIntegral
import Zeta23.FromPNTPlus.ZetaBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology ComplexConjugate

namespace RHGarden

/-- The centered xi Nevanlinna function is odd.  This is a global identity:
`logDeriv` is totalized at the zeros, so no nonvanishing hypothesis is
needed. -/
theorem xiNevanlinnaQ_neg (z : ℂ) :
    xiNevanlinnaQ (-z) = -xiNevanlinnaQ z := by
  rw [xiNevanlinnaQ, xiNevanlinnaQ]
  have harg :
      (1 / 2 : ℂ) - Complex.I * (-z) =
        1 - ((1 / 2 : ℂ) - Complex.I * z) := by
    ring
  rw [harg, logDeriv_riemannXi_one_sub]
  ring

/-- Suzuki's sign-normalized Fourier--Laplace transform of the Riemann
screw function. -/
theorem integral_riemannScrew_exp_eq_xiNevanlinnaQ
    {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t : ℝ in Set.Ioi 0,
        (riemannScrew t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ)) =
      -(Complex.I / z ^ 2) * xiNevanlinnaQ z := by
  rw [integral_riemannScrew_exp_eq_xiNevanlinnaQ_neg hz,
    xiNevanlinnaQ_neg]
  simp

theorem integrableOn_suzukiPsi_exp {z : ℂ}
    (hz : 1 / 2 < z.im) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (suzukiPsi t : ℂ) *
        Complex.exp (Complex.I * z * (t : ℂ)))
      (Set.Ioi 0) := by
  have h := (integrableOn_riemannScrew_exp hz).neg
  apply h.congr
  filter_upwards with t
  simp [riemannScrew]

/-- The Fourier--Laplace transform of Suzuki's nonnegative-side function
`Psi = -g`. -/
theorem integral_suzukiPsi_exp_eq_xiNevanlinnaQ
    {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t : ℝ in Set.Ioi 0,
        (suzukiPsi t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ)) =
      (Complex.I / z ^ 2) * xiNevanlinnaQ z := by
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (suzukiPsi t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        -(∫ t : ℝ in Set.Ioi 0,
          (riemannScrew t : ℂ) *
            Complex.exp (Complex.I * z * (t : ℂ))) := by
      rw [← MeasureTheory.integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      simp [riemannScrew]
    _ = (Complex.I / z ^ 2) * xiNevanlinnaQ z := by
      rw [integral_riemannScrew_exp_eq_xiNevanlinnaQ hz]
      ring

/-- The one-sided complex Laplace transform of Suzuki's zero-side `Psi`. -/
noncomputable def suzukiPsiLaplace (w : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    (suzukiPsi t : ℂ) * Complex.exp (-w * (t : ℂ))

/-- The explicit meromorphic continuation supplied by xi's logarithmic
derivative. -/
noncomputable def suzukiPsiLaplaceContinuation (w : ℂ) : ℂ :=
  -(Complex.I / w ^ 2) * xiNevanlinnaQ (Complex.I * w)

/-- On its initial half-plane of absolute convergence, the Laplace
transform equals the explicit xi continuation. -/
theorem suzukiPsiLaplace_eq_Q {w : ℂ} (hw : 1 / 2 < w.re) :
    suzukiPsiLaplace w = suzukiPsiLaplaceContinuation w := by
  have hz : 1 / 2 < (Complex.I * w).im := by
    simpa [Complex.mul_im] using hw
  rw [suzukiPsiLaplace, suzukiPsiLaplaceContinuation]
  have h := integral_suzukiPsi_exp_eq_xiNevanlinnaQ hz
  rw [show (fun t : ℝ =>
      (suzukiPsi t : ℂ) * Complex.exp (-w * (t : ℂ))) =
      (fun t : ℝ =>
        (suzukiPsi t : ℂ) *
          Complex.exp (Complex.I * (Complex.I * w) * (t : ℂ))) by
    funext t
    congr 2
    simp [← mul_assoc]]
  rw [h]
  have hcoef :
      Complex.I / (Complex.I * w) ^ 2 =
        -(Complex.I / w ^ 2) := by
    rw [mul_pow, I_sq]
    ring
  rw [hcoef]

/-- Pointwise nonnegativity in Suzuki's Theorem 1.7. -/
def SuzukiPsiNonnegative : Prop :=
  ∀ t : ℝ, 0 ≤ suzukiPsi t

/-- The diagonal screw kernel is exactly twice Suzuki's `Psi`. -/
theorem riemannScrewKernel_self (t : ℝ) :
    riemannScrewKernel t t = (2 * suzukiPsi t : ℝ) := by
  rw [riemannScrewKernel, sub_self, riemannScrew_even,
    riemannScrew_zero]
  simp only [riemannScrew]
  push_cast
  ring

/-- Sampled positive semidefiniteness immediately forces Suzuki's
pointwise inequality, by looking at the diagonal. -/
theorem suzukiPsi_nonnegative_of_kernelPSD
    (hPSD : KernelPSD riemannScrewKernel) :
    SuzukiPsiNonnegative := by
  intro t
  have h := riemannScrew_nonpos_of_kernelPSD hPSD t
  rw [riemannScrew] at h
  linarith

/-! ## The positive real Laplace axis -/

private noncomputable def zetaRealRemainder (σ : ℝ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ),
    ((⌊x⌋ : ℂ) + 1 / 2 - x) /
      (x : ℂ) ^ ((σ : ℂ) + 1)

private theorem norm_zetaRealRemainder_le {σ : ℝ} (hσ : 0 < σ) :
    ‖zetaRealRemainder σ‖ ≤ 1 / σ := by
  simpa [zetaRealRemainder] using
    (ZetaBnd_aux1b 1 le_rfl (σ := σ) (t := 0) hσ)

private theorem riemannZeta_real_eq {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≠ 1) :
    riemannZeta (σ : ℂ) =
      ((1 / 2 : ℝ) - 1 / (1 - σ) : ℝ) +
        (σ : ℂ) * zetaRealRemainder σ := by
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hsum :
      (∑ n ∈ Finset.range 2,
        (((n : ℂ) ^ (σ : ℂ))⁻¹)) = 1 := by
    norm_num [Finset.sum_range_succ, Complex.zero_cpow, hσc]
  rw [← Zeta0EqZeta (N := 1) one_pos (s := (σ : ℂ))
    (by simpa using hσ) (by exact_mod_cast hσ1)]
  simp [riemannZeta0, zetaRealRemainder]
  rw [hsum]
  ring

/-- Zeta is strictly negative on the real interval `(1/2, 1)`.  The
`N = 1` Euler--Maclaurin main term is already less than `-3/2`, while the
remainder contributes at most `1`. -/
theorem riemannZeta_real_re_neg_of_half_lt_of_lt_one
    {σ : ℝ} (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hσ : 0 < σ := lt_trans (by norm_num) hhalf
  rw [riemannZeta_real_eq hσ (ne_of_lt hone)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hre : (zetaRealRemainder σ).re ≤ ‖zetaRealRemainder σ‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hrem : σ * (zetaRealRemainder σ).re ≤ 1 := by
    calc
      σ * (zetaRealRemainder σ).re ≤
          σ * ‖zetaRealRemainder σ‖ :=
        mul_le_mul_of_nonneg_left hre hσ.le
      _ ≤ σ * (1 / σ) :=
        mul_le_mul_of_nonneg_left (norm_zetaRealRemainder_le hσ) hσ.le
      _ = 1 := by field_simp
  have hden : 0 < 1 - σ := sub_pos.mpr hone
  have hinv : 2 < 1 / (1 - σ) := by
    rw [lt_div_iff₀ hden]
    linarith
  linarith

theorem riemannZeta_real_ne_zero_of_half_lt_of_lt_one
    {σ : ℝ} (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hzero
  have hneg := riemannZeta_real_re_neg_of_half_lt_of_lt_one hhalf hone
  rw [hzero] at hneg
  norm_num at hneg

/-- Xi has no zero on the positive real Laplace axis, i.e. at any real
point `1/2 + y` with `y ≥ 0`. -/
theorem riemannXi_real_right_half_ne_zero {y : ℝ} (hy : 0 ≤ y) :
    riemannXi (((1 / 2 : ℝ) + y : ℝ) : ℂ) ≠ 0 := by
  by_cases hy0 : y = 0
  · subst y
    norm_num
    exact riemannXi_half_ne_zero
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  by_cases hyhalf : y < 1 / 2
  · have hs0 : (((1 / 2 : ℝ) + y : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith : (1 / 2 : ℝ) + y ≠ 0)
    have hs1 : (((1 / 2 : ℝ) + y : ℝ) : ℂ) ≠ 1 := by
      exact_mod_cast (by linarith : (1 / 2 : ℝ) + y ≠ 1)
    intro hxi
    exact riemannZeta_real_ne_zero_of_half_lt_of_lt_one
      (by linarith) (by linarith)
      (riemannZeta_eq_zero_of_riemannXi_eq_zero hs0 hs1 hxi)
  · have hre : 1 ≤ ((((1 / 2 : ℝ) + y : ℝ) : ℂ)).re := by
      norm_num
      linarith
    by_cases hyhalfEq : y = 1 / 2
    · subst y
      norm_num
    intro hxi
    have hs1real : (1 / 2 : ℝ) + y ≠ 1 := by
      intro hs
      apply hyhalfEq
      linarith
    have hz := riemannZeta_eq_zero_of_riemannXi_eq_zero
      (s := (((1 / 2 : ℝ) + y : ℝ) : ℂ))
      (by exact_mod_cast (by linarith : (1 / 2 : ℝ) + y ≠ 0))
      (by exact_mod_cast hs1real)
      hxi
    exact riemannZeta_ne_zero_of_one_le_re hre hz

/-! ## Elementary convergence theory for nonnegative Laplace transforms -/

/-- Absolute convergence of the one-sided Laplace transform at a real
parameter. -/
def laplaceConvergesAt (f : ℝ → ℝ) (σ : ℝ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun t : ℝ => (f t : ℂ) *
      Complex.exp (-(σ : ℂ) * (t : ℂ)))
    (Set.Ioi 0)

/-- Absolute convergence of a Laplace transform is upward closed on the
real axis. -/
theorem laplaceConvergesAt_mono {f : ℝ → ℝ}
    (hf : Continuous f) {σ τ : ℝ}
    (hσ : laplaceConvergesAt f σ) (hστ : σ ≤ τ) :
    laplaceConvergesAt f τ := by
  change MeasureTheory.Integrable
    (fun t : ℝ => (f t : ℂ) * Complex.exp (-(σ : ℂ) * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0)) at hσ
  change MeasureTheory.Integrable
    (fun t : ℝ => (f t : ℂ) * Complex.exp (-(τ : ℂ) * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  apply hσ.mono
  · exact ((Complex.continuous_ofReal.comp hf).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    gcongr
    exact ht.le

/-- A complex Laplace parameter has the same absolute decay as its real
part. -/
theorem integrableOn_complex_laplace_of_convergesAt_re
    {f : ℝ → ℝ} (hf : Continuous f) {w : ℂ}
    (hw : laplaceConvergesAt f w.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp (-w * (t : ℂ)))
      (Set.Ioi 0) := by
  change MeasureTheory.Integrable
    (fun t : ℝ => (f t : ℂ) *
      Complex.exp (-(w.re : ℂ) * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0)) at hw
  change MeasureTheory.Integrable
    (fun t : ℝ => (f t : ℂ) * Complex.exp (-w * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  apply hw.mono
  · exact ((Complex.continuous_ofReal.comp hf).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, Complex.norm_exp, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    exact le_rfl

theorem laplaceConvergesAt_suzukiPsi_of_half_lt
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    laplaceConvergesAt suzukiPsi σ := by
  have hz : 1 / 2 < (Complex.I * (σ : ℂ)).im := by
    simpa [Complex.mul_im] using hσ
  have h := integrableOn_suzukiPsi_exp hz
  apply h.congr
  filter_upwards with t
  congr 2
  simp [← mul_assoc]

/-- The initial right half-plane on which the integral definition of
`suzukiPsiLaplace` is absolutely convergent. -/
theorem integrableOn_suzukiPsiLaplace_of_half_lt {w : ℂ}
    (hw : 1 / 2 < w.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (suzukiPsi t : ℂ) *
        Complex.exp (-w * (t : ℂ)))
      (Set.Ioi 0) := by
  exact integrableOn_complex_laplace_of_convergesAt_re
    continuous_suzukiPsi
    (laplaceConvergesAt_suzukiPsi_of_half_lt hw)

/-! ## The meromorphic continuation and the Landau boundary -/

/-- The explicit xi expression is meromorphic.  This is the continuation
to which Landau's boundary theorem will be applied. -/
theorem meromorphic_suzukiPsiLaplaceContinuation :
    Meromorphic suzukiPsiLaplaceContinuation := by
  intro w
  have hxi : Meromorphic riemannXi :=
    fun z => (analyticAt_riemannXi z).meromorphicAt
  have hld : Meromorphic (logDeriv riemannXi) := hxi.logDeriv
  let coord : ℂ → ℂ := fun u =>
    (1 / 2 : ℂ) - Complex.I * (Complex.I * u)
  have hcoord : AnalyticAt ℂ coord w := by
    dsimp [coord]
    fun_prop
  have hcomp : MeromorphicAt ((logDeriv riemannXi) ∘ coord) w :=
    (hld (coord w)).comp_analyticAt hcoord
  have hQ := (MeromorphicAt.const Complex.I w).mul hcomp
  have hfac := (MeromorphicAt.const (-Complex.I) w).div
    ((MeromorphicAt.id w).pow 2)
  have hproduct := hfac.mul hQ
  apply hproduct.congr
  filter_upwards with u
  simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply,
    Function.comp_apply, id_eq, suzukiPsiLaplaceContinuation,
    xiNevanlinnaQ, neg_div, coord]

/-- The meromorphic continuation is regular at every positive real point.
This is precisely the real-axis input required by Landau's theorem. -/
theorem analyticAt_suzukiPsiLaplaceContinuation_of_pos
    {σ : ℝ} (hσ : 0 < σ) :
    AnalyticAt ℂ suzukiPsiLaplaceContinuation (σ : ℂ) := by
  have hcenter :
      (1 / 2 : ℂ) - Complex.I * (Complex.I * (σ : ℂ)) =
        (((1 / 2 : ℝ) + σ : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hxi0 :
      riemannXi
        ((1 / 2 : ℂ) - Complex.I * (Complex.I * (σ : ℂ))) ≠ 0 := by
    rw [hcenter]
    exact riemannXi_real_right_half_ne_zero hσ.le
  have hxi : AnalyticAt ℂ riemannXi
      ((1 / 2 : ℂ) - Complex.I * (Complex.I * (σ : ℂ))) :=
    analyticAt_riemannXi _
  have hld : AnalyticAt ℂ (logDeriv riemannXi)
      ((1 / 2 : ℂ) - Complex.I * (Complex.I * (σ : ℂ))) := by
    rw [logDeriv]
    exact hxi.deriv.div hxi hxi0
  let coord : ℂ → ℂ := fun u =>
    (1 / 2 : ℂ) - Complex.I * (Complex.I * u)
  have hcoord : AnalyticAt ℂ coord (σ : ℂ) := by
    dsimp [coord]
    fun_prop
  have hcomp : AnalyticAt ℂ ((logDeriv riemannXi) ∘ coord) (σ : ℂ) :=
    AnalyticAt.comp (g := logDeriv riemannXi) (f := coord) hld hcoord
  have hQ :=
    (analyticAt_const (v := Complex.I) (x := (σ : ℂ))).mul hcomp
  have hσc : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hnum : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) (σ : ℂ) :=
    analyticAt_const
  have hden : AnalyticAt ℂ (fun u : ℂ => u ^ 2) (σ : ℂ) :=
    analyticAt_id.pow 2
  have hfac := hnum.div hden (pow_ne_zero 2 hσc)
  have hproduct := hfac.mul hQ
  apply hproduct.congr
  filter_upwards with u
  simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply,
    suzukiPsiLaplaceContinuation,
    xiNevanlinnaQ, neg_div, coord]

private theorem mul_exp_neg_mul_le {d t : ℝ} (hd : 0 < d) :
    t * Real.exp (-d * t) ≤ Real.exp (-1) / d := by
  rw [le_div_iff₀ hd]
  have h := Real.mul_exp_neg_le_exp_neg_one (d * t)
  have heq :
      t * Real.exp (-d * t) * d =
        d * t * Real.exp (-(d * t)) := by
    rw [show -d * t = -(d * t) by ring]
    ring
  rw [heq]
  exact h

/-- Convergence at a smaller real parameter supplies the first exponential
moment at every larger parameter.  This is the domination needed for the
first derivative in Landau's Taylor argument. -/
theorem integrableOn_laplace_first_moment_of_lt
    {f : ℝ → ℝ} (hf : Continuous f) {σ τ : ℝ}
    (hστ : σ < τ) (hσ : laplaceConvergesAt f σ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => ((t * f t : ℝ) : ℂ) *
        Complex.exp (-(τ : ℂ) * (t : ℂ)))
      (Set.Ioi 0) := by
  let d : ℝ := τ - σ
  let C : ℝ := Real.exp (-1) / d
  have hd : 0 < d := sub_pos.mpr hστ
  have hbase : MeasureTheory.Integrable
      (fun t : ℝ => (f t : ℂ) *
        Complex.exp (-(σ : ℂ) * (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    change MeasureTheory.Integrable
      (fun t : ℝ => (f t : ℂ) *
        Complex.exp (-(σ : ℂ) * (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) at hσ
    exact hσ
  have hmajor : MeasureTheory.Integrable
      (fun t : ℝ => C *
        ‖(f t : ℂ) * Complex.exp (-(σ : ℂ) * (t : ℂ))‖)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    exact hbase.norm.const_mul C
  change MeasureTheory.Integrable
    (fun t : ℝ => ((t * f t : ℝ) : ℂ) *
      Complex.exp (-(τ : ℂ) * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  apply hmajor.mono'
  · exact (((Complex.continuous_ofReal.comp
      (continuous_id.mul hf))).mul
        (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht0 : 0 ≤ t := ht.le
    have hdecay := mul_exp_neg_mul_le (t := t) hd
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      abs_of_nonneg ht0]
    rw [show -τ * t = (-σ * t) + (-d * t) by
      dsimp [d]
      ring, Real.exp_add]
    dsimp [C]
    calc
      t * |f t| *
          (Real.exp (-σ * t) * Real.exp (-d * t)) =
        (|f t| * Real.exp (-σ * t)) *
          (t * Real.exp (-d * t)) := by ring
      _ ≤ (|f t| * Real.exp (-σ * t)) *
          (Real.exp (-1) / d) :=
        mul_le_mul_of_nonneg_left hdecay
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      _ = Real.exp (-1) / d *
          (|f t| * Real.exp (-σ * t)) := by ring

/-- The exact Landau boundary principle still needed by the Suzuki
pointwise route.  It says that a nonnegative continuous Laplace transform
whose meromorphic continuation is regular on the positive real axis cannot
have a positive abscissa of convergence.  Keeping this as a proposition
isolates the historical Landau theorem without assuming it. -/
def NonnegativeLaplaceBoundaryPrinciple : Prop :=
  ∀ (f : ℝ → ℝ) (F : ℂ → ℂ) (a : ℝ),
    0 < a →
    Continuous f →
    (∀ t : ℝ, 0 ≤ t → 0 ≤ f t) →
    Meromorphic F →
    (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F (σ : ℂ)) →
    (∀ σ : ℝ, a < σ → laplaceConvergesAt f σ) →
    (∀ σ : ℝ, a < σ →
      (∫ t : ℝ in Set.Ioi 0,
        (f t : ℂ) * Complex.exp (-(σ : ℂ) * (t : ℂ))) = F (σ : ℂ)) →
    ∀ σ : ℝ, 0 < σ → laplaceConvergesAt f σ

/-- Conditional application of the isolated Landau principle to Suzuki's
`Psi`.  Every hypothesis other than the generic boundary theorem has been
discharged in this file. -/
theorem laplaceConvergesAt_suzukiPsi_of_pos_of_landau
    (hLandau : NonnegativeLaplaceBoundaryPrinciple)
    (hPsi : SuzukiPsiNonnegative) {σ : ℝ} (hσ : 0 < σ) :
    laplaceConvergesAt suzukiPsi σ := by
  apply hLandau suzukiPsi suzukiPsiLaplaceContinuation (1 / 2)
    (by norm_num) continuous_suzukiPsi
    (fun t _ => hPsi t)
    meromorphic_suzukiPsiLaplaceContinuation
    (fun τ hτ => analyticAt_suzukiPsiLaplaceContinuation_of_pos hτ)
    (fun τ hτ => laplaceConvergesAt_suzukiPsi_of_half_lt hτ)
    (fun τ hτ => ?_) σ hσ
  change suzukiPsiLaplace (τ : ℂ) =
    suzukiPsiLaplaceContinuation (τ : ℂ)
  exact suzukiPsiLaplace_eq_Q (by simpa using hτ)

end RHGarden
