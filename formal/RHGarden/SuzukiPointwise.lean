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

/-- Every fixed polynomial power is uniformly dominated by exponential
decay.  This is the quantitative estimate used for all Laplace moments. -/
private theorem pow_mul_exp_neg_mul_le_factorial_div_pow
    {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-d * t) ≤ (n.factorial : ℝ) / d ^ n := by
  have hterm :
      (d * t) ^ n / (n.factorial : ℝ) ≤ Real.exp (d * t) :=
    Real.pow_div_factorial_le_exp (d * t) (mul_nonneg hd.le ht) n
  have hC : 0 ≤ (n.factorial : ℝ) / d ^ n := by positivity
  calc
    t ^ n * Real.exp (-d * t) =
        ((d * t) ^ n / (n.factorial : ℝ)) *
          Real.exp (-d * t) * ((n.factorial : ℝ) / d ^ n) := by
      field_simp [hd.ne']
      ring
    _ ≤ Real.exp (d * t) * Real.exp (-d * t) *
          ((n.factorial : ℝ) / d ^ n) := by
      gcongr
    _ = (n.factorial : ℝ) / d ^ n := by
      rw [← Real.exp_add]
      simp

/-- Convergence at a smaller real parameter supplies every polynomial
Laplace moment at every larger parameter. -/
theorem integrableOn_laplace_moment_of_lt
    {f : ℝ → ℝ} (hf : Continuous f) {σ τ : ℝ}
    (hστ : σ < τ) (hσ : laplaceConvergesAt f σ) (n : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((t ^ n) * f t : ℝ) : ℂ) *
        Complex.exp (-(τ : ℂ) * (t : ℂ)))
      (Set.Ioi 0) := by
  let d : ℝ := τ - σ
  let C : ℝ := (n.factorial : ℝ) / d ^ n
  have hd : 0 < d := sub_pos.mpr hστ
  have hbase : MeasureTheory.Integrable
      (fun t : ℝ => (f t : ℂ) *
        Complex.exp (-(σ : ℂ) * (t : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    exact hσ
  have hmajor : MeasureTheory.Integrable
      (fun t : ℝ => C *
        ‖(f t : ℂ) * Complex.exp (-(σ : ℂ) * (t : ℂ))‖)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    exact hbase.norm.const_mul C
  change MeasureTheory.Integrable
    (fun t : ℝ => (((t ^ n) * f t : ℝ) : ℂ) *
      Complex.exp (-(τ : ℂ) * (t : ℂ)))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  apply hmajor.mono'
  · exact (((Complex.continuous_ofReal.comp
      ((continuous_id.pow n).mul hf))).mul
        (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht0 : 0 ≤ t := ht.le
    have hdecay :=
      pow_mul_exp_neg_mul_le_factorial_div_pow hd ht0 n
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      abs_pow, abs_of_nonneg ht0]
    rw [show -τ * t = (-σ * t) + (-d * t) by
      dsimp [d]
      ring, Real.exp_add]
    dsimp [C]
    calc
      t ^ n * |f t| *
          (Real.exp (-σ * t) * Real.exp (-d * t)) =
        (|f t| * Real.exp (-σ * t)) *
          (t ^ n * Real.exp (-d * t)) := by ring
      _ ≤ (|f t| * Real.exp (-σ * t)) *
          ((n.factorial : ℝ) / d ^ n) :=
        mul_le_mul_of_nonneg_left hdecay
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      _ = (n.factorial : ℝ) / d ^ n *
          (|f t| * Real.exp (-σ * t)) := by ring

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
  simpa only [pow_one] using
    (integrableOn_laplace_moment_of_lt hf hστ hσ 1)

/-- The real `n`th moment of a one-sided Laplace transform.  Its real
codomain makes positivity available without passing through complex real
parts. -/
noncomputable def laplaceMoment
    (f : ℝ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    t ^ n * f t * Real.exp (-σ * t)

/-- Every Laplace moment of a nonnegative function is nonnegative. -/
theorem laplaceMoment_nonneg {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t) (σ : ℝ) (n : ℕ) :
    0 ≤ laplaceMoment f σ n := by
  rw [laplaceMoment]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with t ht
  exact mul_nonneg
    (mul_nonneg (pow_nonneg ht.le n) (hf t ht.le))
    (Real.exp_pos _).le

/-- Coercing a real Laplace moment to `ℂ` gives the corresponding complex
integral on the real axis. -/
theorem laplaceMoment_coe_eq_complexIntegral
    (f : ℝ → ℝ) (σ : ℝ) (n : ℕ) :
    (laplaceMoment f σ n : ℂ) =
      ∫ t : ℝ in Set.Ioi 0,
        (((t ^ n) * f t : ℝ) : ℂ) *
          Complex.exp (-(σ : ℂ) * (t : ℂ)) := by
  rw [laplaceMoment]
  calc
    Complex.ofReal (∫ t : ℝ,
        t ^ n * f t * Real.exp (-σ * t)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) =
        ∫ t : ℝ,
          ((t ^ n * f t * Real.exp (-σ * t) : ℝ) : ℂ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      symm
      exact _root_.integral_ofReal
    _ = ∫ t : ℝ,
        (((t ^ n) * f t : ℝ) : ℂ) *
          Complex.exp (-(σ : ℂ) * (t : ℂ))
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      push_cast
      rfl

/-- The complex one-sided Laplace integral, defined everywhere using
Mathlib's totalized Bochner integral. -/
noncomputable def complexLaplaceIntegral
    (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    (f t : ℂ) * Complex.exp (-z * (t : ℂ))

/-- A strict real convergence margin controls every polynomial moment at a
complex parameter. -/
theorem integrableOn_complex_laplace_moment_of_lt
    {f : ℝ → ℝ} (hf : Continuous f) {σ : ℝ} {z : ℂ}
    (hσz : σ < z.re) (hσ : laplaceConvergesAt f σ) (n : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((t ^ n) * f t : ℝ) : ℂ) *
        Complex.exp (-z * (t : ℂ)))
      (Set.Ioi 0) := by
  apply integrableOn_complex_laplace_of_convergesAt_re
    ((continuous_id.pow n).mul hf)
  exact integrableOn_laplace_moment_of_lt hf hσz hσ n

/-- The integral whose integrand is the `n`th pointwise derivative of the
Laplace kernel. -/
noncomputable def complexLaplaceDerivativeIntegral
    (f : ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    (-(t : ℂ)) ^ n * (f t : ℂ) *
      Complex.exp (-z * (t : ℂ))

/-- Differentiation under the Laplace integral, with a strict real
convergence margin providing a locally uniform integrable majorant. -/
theorem hasDerivAt_complexLaplaceDerivativeIntegral
    {f : ℝ → ℝ} (hf : Continuous f) {σ : ℝ} {z : ℂ}
    (hσz : σ < z.re) (hσ : laplaceConvergesAt f σ) (n : ℕ) :
    HasDerivAt (complexLaplaceDerivativeIntegral f n)
      (complexLaplaceDerivativeIntegral f (n + 1) z) z := by
  let d : ℝ := (z.re - σ) / 2
  let lower : ℝ := z.re - d
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioi 0)
  let F : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ)) ^ n * (f t : ℂ) *
      Complex.exp (-w * (t : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ)) ^ (n + 1) * (f t : ℂ) *
      Complex.exp (-w * (t : ℂ))
  let bound : ℝ → ℝ := fun t =>
    t ^ (n + 1) * |f t| * Real.exp (-lower * t)
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hσlower : σ < lower := by
    dsimp [lower, d]
    linarith
  have hbase :=
    integrableOn_laplace_moment_of_lt hf hσlower hσ (n + 1)
  have hbound : MeasureTheory.Integrable bound μ := by
    have hnorm := hbase.norm
    apply hnorm.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht0 : 0 ≤ t := ht.le
    dsimp [bound, μ]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      abs_pow, abs_of_nonneg ht0]
  have hFint : MeasureTheory.Integrable (F z) μ := by
    have h := integrableOn_complex_laplace_moment_of_lt hf hσz hσ n
    have hc := h.const_mul ((-1 : ℂ) ^ n)
    apply hc.congr
    filter_upwards with t
    dsimp [F, μ]
    rw [neg_pow]
    push_cast
    ring
  have hF'meas : MeasureTheory.AEStronglyMeasurable (F' z) μ := by
    have hc : Continuous (F' z) := by
      dsimp [F']
      fun_prop
    exact hc.aestronglyMeasurable
  have hmajor : ∀ᵐ t ∂μ, ∀ w ∈ Metric.ball z d,
      ‖F' w t‖ ≤ bound t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht w hw
    have ht0 : 0 ≤ t := ht.le
    have hre : lower ≤ w.re := by
      have habs : |w.re - z.re| ≤ ‖w - z‖ := by
        exact (Complex.abs_re_le_norm (w - z)).trans_eq (by
          simp only)
      have hnorm : ‖w - z‖ < d := by
        simpa [dist_eq_norm] using hw
      have hneg : -|w.re - z.re| ≤ w.re - z.re :=
        neg_abs_le (w.re - z.re)
      dsimp [lower]
      linarith
    dsimp [F', bound]
    simp only [norm_mul, norm_pow, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero,
      abs_of_nonneg ht0]
    gcongr
  have hdiff : ∀ᵐ t ∂μ, ∀ w ∈ Metric.ball z d,
      HasDerivAt (F · t) (F' w t) w := by
    filter_upwards with t w hw
    have hinner : HasDerivAt
        (fun u : ℂ => -u * (t : ℂ)) (-(t : ℂ)) w := by
      simpa using (hasDerivAt_id w).neg.mul_const (t : ℂ)
    have hexp : HasDerivAt
        (fun u : ℂ => Complex.exp (-u * (t : ℂ)))
        (Complex.exp (-w * (t : ℂ)) * (-(t : ℂ))) w :=
      hinner.cexp
    have hconst := hexp.const_mul
      ((-(t : ℂ)) ^ n * (f t : ℂ))
    change HasDerivAt
      (fun y : ℂ => (-(t : ℂ)) ^ n * (f t : ℂ) *
        Complex.exp (-y * (t : ℂ)))
      ((-(t : ℂ)) ^ (n + 1) * (f t : ℂ) *
        Complex.exp (-w * (t : ℂ))) w
    have heq :
        (-(t : ℂ)) ^ n * (f t : ℂ) *
            (Complex.exp (-w * (t : ℂ)) * (-(t : ℂ))) =
          (-(t : ℂ)) ^ (n + 1) * (f t : ℂ) *
            Complex.exp (-w * (t : ℂ)) := by
      rw [pow_succ]
      ring
    rw [← heq]
    exact hconst
  have hmeas : ∀ᶠ w in 𝓝 z,
      MeasureTheory.AEStronglyMeasurable (F w) μ := by
    filter_upwards with w
    have hc : Continuous (F w) := by
      dsimp [F]
      fun_prop
    exact hc.aestronglyMeasurable
  have hderiv :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z hd) hmeas hFint hF'meas
      hmajor hbound hdiff
  have hout := hderiv.2
  change HasDerivAt (complexLaplaceDerivativeIntegral f n)
    (complexLaplaceDerivativeIntegral f (n + 1) z) z at hout
  exact hout

/-- A single real convergence parameter gives analyticity of the complex
Laplace integral on the open half-plane to its right. -/
theorem analyticOnNhd_complexLaplaceIntegral_of_convergesAt
    {f : ℝ → ℝ} (hf : Continuous f) {σ : ℝ}
    (hconv : laplaceConvergesAt f σ) :
    AnalyticOnNhd ℂ (complexLaplaceIntegral f)
      {z : ℂ | σ < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    have heq : complexLaplaceDerivativeIntegral f 0 =
        complexLaplaceIntegral f := by
      funext u
      simp [complexLaplaceIntegral, complexLaplaceDerivativeIntegral]
    rw [← heq]
    exact (hasDerivAt_complexLaplaceDerivativeIntegral
      hf hz hconv 0).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

/-- The `n`th iterated derivative of a Laplace integral is obtained by
differentiating the kernel `n` times. -/
theorem iteratedDeriv_complexLaplaceIntegral_eq_integral
    {f : ℝ → ℝ} (hf : Continuous f) {σ : ℝ} {z : ℂ}
    (hσz : σ < z.re) (hσ : laplaceConvergesAt f σ) (n : ℕ) :
    iteratedDeriv n (complexLaplaceIntegral f) z =
      complexLaplaceDerivativeIntegral f n z := by
  have hderiv : ∀ (m : ℕ) {w : ℂ}, σ < w.re →
      HasDerivAt (iteratedDeriv m (complexLaplaceIntegral f))
        (complexLaplaceDerivativeIntegral f (m + 1) w) w := by
    intro m
    induction m with
    | zero =>
        intro w hσw
        have heq : complexLaplaceDerivativeIntegral f 0 =
            complexLaplaceIntegral f := by
          funext u
          simp [complexLaplaceIntegral,
            complexLaplaceDerivativeIntegral]
        rw [← heq]
        exact hasDerivAt_complexLaplaceDerivativeIntegral
          hf hσw hσ 0
    | succ m ih =>
        intro w hσw
        rw [iteratedDeriv_succ]
        have hevent :
            deriv (iteratedDeriv m (complexLaplaceIntegral f)) =ᶠ[𝓝 w]
              complexLaplaceDerivativeIntegral f (m + 1) := by
          have hre : ∀ᶠ u : ℂ in 𝓝 w, σ < u.re :=
            IsOpen.eventually_mem
              (isOpen_lt continuous_const Complex.continuous_re) hσw
          filter_upwards [hre] with u hσu
          exact (ih hσu).deriv
        rw [EventuallyEq.hasDerivAt_iff hevent]
        simpa [Nat.add_assoc] using
          (hasDerivAt_complexLaplaceDerivativeIntegral
            hf hσw hσ (m + 1))
  induction n with
  | zero =>
      simp [complexLaplaceIntegral, complexLaplaceDerivativeIntegral]
  | succ n _ =>
      rw [iteratedDeriv_succ]
      exact (hderiv n hσz).deriv

/-- At a real center, the pointwise derivative integral is the alternating
real Laplace moment. -/
theorem complexLaplaceDerivativeIntegral_ofReal_eq_moment
    (f : ℝ → ℝ) (σ : ℝ) (n : ℕ) :
    complexLaplaceDerivativeIntegral f n (σ : ℂ) =
      (-1 : ℂ) ^ n * (laplaceMoment f σ n : ℂ) := by
  rw [complexLaplaceDerivativeIntegral,
    laplaceMoment_coe_eq_complexIntegral]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [neg_pow]
  push_cast
  ring

/-- The all-orders derivative identity used by Landau's Taylor argument. -/
theorem iteratedDeriv_laplace_eq_moment
    {f : ℝ → ℝ} (hf : Continuous f) {σ₀ σ : ℝ}
    (hσ : σ₀ < σ) (hconv : laplaceConvergesAt f σ₀) (n : ℕ) :
    iteratedDeriv n (complexLaplaceIntegral f) (σ : ℂ) =
      (-1 : ℂ) ^ n * (laplaceMoment f σ n : ℂ) := by
  rw [iteratedDeriv_complexLaplaceIntegral_eq_integral
    hf (by simpa using hσ) hconv n]
  exact complexLaplaceDerivativeIntegral_ofReal_eq_moment f σ n

private noncomputable def laplaceExpSeriesTerm
    (f : ℝ → ℝ) (σ r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  f t * Real.exp (-σ * t) * ((r * t) ^ n / (n.factorial : ℝ))

private theorem summable_laplaceExpSeriesTerm
    (f : ℝ → ℝ) (σ r t : ℝ) :
    Summable (fun n : ℕ => laplaceExpSeriesTerm f σ r n t) := by
  exact (Real.summable_pow_div_factorial (r * t)).mul_left
    (f t * Real.exp (-σ * t))

/-- The pointwise exponential series converts the moment-generating sum
back to the Laplace weight at the shifted parameter. -/
theorem tsum_laplaceExpSeriesTerm
    (f : ℝ → ℝ) (σ r t : ℝ) :
    (∑' n : ℕ, laplaceExpSeriesTerm f σ r n t) =
      f t * Real.exp (-(σ - r) * t) := by
  calc
    (∑' n : ℕ, laplaceExpSeriesTerm f σ r n t) =
        f t * Real.exp (-σ * t) *
          (∑' n : ℕ, (r * t) ^ n / (n.factorial : ℝ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rfl
    _ = f t * Real.exp (-σ * t) * Real.exp (r * t) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (r * t : ℝ)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = f t * Real.exp (-(σ - r) * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Tonelli's theorem for the positive exponential series, expressed as an
identity between an `ENNReal` Laplace integral and the series of real
Laplace moments. -/
theorem lintegral_laplace_exp_series
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {σ₀ σ r : ℝ} (hσ : σ₀ < σ)
    (hconv : laplaceConvergesAt f σ₀) (hr : 0 ≤ r) :
    (∫⁻ t : ℝ in Set.Ioi 0,
        ENNReal.ofReal (f t * Real.exp (-(σ - r) * t))) =
      ∑' n : ℕ, ENNReal.ofReal
        (laplaceMoment f σ n * r ^ n / (n.factorial : ℝ)) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioi 0)
  let q : ℕ → ℝ → ℝ := fun n t =>
    laplaceExpSeriesTerm f σ r n t
  have hq_nonneg : ∀ᵐ t ∂μ, ∀ n : ℕ, 0 ≤ q n t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht n
    dsimp [q, laplaceExpSeriesTerm]
    exact mul_nonneg
      (mul_nonneg (hf_nonneg t ht.le) (Real.exp_pos _).le)
      (div_nonneg (pow_nonneg (mul_nonneg hr ht.le) n)
        (Nat.cast_nonneg _))
  have hq_meas : ∀ n : ℕ,
      AEMeasurable
        (fun t => ENNReal.ofReal (q n t)) μ := by
    intro n
    have hc : Continuous (q n) := by
      dsimp [q, laplaceExpSeriesTerm]
      fun_prop
    exact hc.measurable.ennreal_ofReal.aemeasurable
  have hq_integral (n : ℕ) :
      (∫⁻ t : ℝ, ENNReal.ofReal (q n t) ∂μ) =
        ENNReal.ofReal
          (laplaceMoment f σ n * r ^ n / (n.factorial : ℝ)) := by
    have hmC := integrableOn_laplace_moment_of_lt hf hσ hconv n
    have hmR : MeasureTheory.Integrable
        (fun t : ℝ => t ^ n * f t * Real.exp (-σ * t)) μ := by
      have hmNorm := hmC.norm
      apply hmNorm.congr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with t ht
      have hnonneg : 0 ≤ t ^ n * f t * Real.exp (-σ * t) :=
        mul_nonneg (mul_nonneg (pow_nonneg ht.le n) (hf_nonneg t ht.le))
          (Real.exp_pos _).le
      calc
        ‖(((t ^ n) * f t : ℝ) : ℂ) *
              Complex.exp (-(σ : ℂ) * (t : ℂ))‖ =
            ‖((t ^ n * f t * Real.exp (-σ * t) : ℝ) : ℂ)‖ := by
          congr 1
          push_cast
          rfl
        _ = |t ^ n * f t * Real.exp (-σ * t)| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ = t ^ n * f t * Real.exp (-σ * t) :=
          abs_of_nonneg hnonneg
    have hqint : MeasureTheory.Integrable (q n) μ := by
      have hc := hmR.mul_const (r ^ n / (n.factorial : ℝ))
      apply hc.congr
      filter_upwards with t
      dsimp [q, laplaceExpSeriesTerm]
      rw [mul_pow]
      ring
    have hqn : 0 ≤ᵐ[μ] q n := hq_nonneg.mono (fun _ h => h n)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hqint hqn]
    congr 1
    rw [laplaceMoment]
    change (∫ t : ℝ, q n t ∂μ) =
      (∫ t : ℝ,
        t ^ n * f t * Real.exp (-σ * t) ∂μ) *
          r ^ n / (n.factorial : ℝ)
    calc
      (∫ t : ℝ, q n t ∂μ) =
          ∫ t : ℝ,
            (t ^ n * f t * Real.exp (-σ * t)) *
              (r ^ n / (n.factorial : ℝ)) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        dsimp [q, laplaceExpSeriesTerm]
        rw [mul_pow]
        ring
      _ = (∫ t : ℝ,
          t ^ n * f t * Real.exp (-σ * t) ∂μ) *
            (r ^ n / (n.factorial : ℝ)) :=
        MeasureTheory.integral_mul_const (L := ℝ) (μ := μ)
          (r ^ n / (n.factorial : ℝ))
          (fun t : ℝ => t ^ n * f t * Real.exp (-σ * t))
      _ = (∫ t : ℝ,
          t ^ n * f t * Real.exp (-σ * t) ∂μ) *
            r ^ n / (n.factorial : ℝ) := by ring
  change (∫⁻ t : ℝ,
      ENNReal.ofReal (f t * Real.exp (-(σ - r) * t)) ∂μ) = _
  calc
    (∫⁻ t : ℝ,
        ENNReal.ofReal (f t * Real.exp (-(σ - r) * t)) ∂μ) =
        ∫⁻ t : ℝ, ∑' n : ℕ, ENNReal.ofReal (q n t) ∂μ := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi,
        hq_nonneg] with t ht hnonneg
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
        (summable_laplaceExpSeriesTerm f σ r t)]
      congr 1
      exact (tsum_laplaceExpSeriesTerm f σ r t).symm
    _ = ∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal (q n t) ∂μ :=
      MeasureTheory.lintegral_tsum hq_meas
    _ = ∑' n : ℕ, ENNReal.ofReal
        (laplaceMoment f σ n * r ^ n / (n.factorial : ℝ)) := by
      apply tsum_congr
      exact hq_integral

/-- If the nonnegative moment Taylor series converges at a radius `r`, then
the Laplace integral converges at the real parameter shifted left by `r`.
This is the measure-theoretic half of Landau's local extension argument. -/
theorem laplaceConvergesAt_sub_of_summable_moments
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {σ₀ σ r : ℝ} (hσ : σ₀ < σ)
    (hconv : laplaceConvergesAt f σ₀) (hr : 0 ≤ r)
    (hmoments : Summable (fun n : ℕ =>
      laplaceMoment f σ n * r ^ n / (n.factorial : ℝ))) :
    laplaceConvergesAt f (σ - r) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioi 0)
  let q : ℝ → ℝ := fun t =>
    f t * Real.exp (- (σ - r) * t)
  have hq_meas : MeasureTheory.AEStronglyMeasurable q μ := by
    have hc : Continuous q := by
      dsimp [q]
      fun_prop
    exact hc.aestronglyMeasurable
  have hq_nonneg : 0 ≤ᵐ[μ] q := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    exact mul_nonneg (hf_nonneg t ht.le) (Real.exp_pos _).le
  have hlin : (∫⁻ t : ℝ, ENNReal.ofReal (q t) ∂μ) ≠ ⊤ := by
    change (∫⁻ t : ℝ in Set.Ioi 0,
      ENNReal.ofReal (f t * Real.exp (- (σ - r) * t))) ≠ ⊤
    rw [lintegral_laplace_exp_series hf hf_nonneg hσ hconv hr]
    exact hmoments.tsum_ofReal_ne_top
  have hq_int : MeasureTheory.Integrable q μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hq_meas hq_nonneg).mp hlin
  have hq_complex : MeasureTheory.Integrable
      (fun t : ℝ => (q t : ℂ)) μ := hq_int.ofReal
  change MeasureTheory.Integrable
    (fun t : ℝ => (f t : ℂ) *
      Complex.exp (-((σ - r : ℝ) : ℂ) * (t : ℂ))) μ
  apply hq_complex.congr
  filter_upwards with t
  dsimp [q]
  push_cast
  rfl

/-- An analytic germ whose Taylor coefficients are the Laplace derivatives
provides a genuine interval of convergence to the left of the center.  This
is Landau's local Taylor argument after the positive Tonelli step above. -/
theorem exists_laplaceConvergesAt_sub_of_analytic_derivatives
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {σ₀ σ : ℝ} (hσ : σ₀ < σ)
    (hconv : laplaceConvergesAt f σ₀)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (σ : ℂ))
    (hderiv : ∀ n : ℕ,
      iteratedDeriv n F (σ : ℂ) =
        iteratedDeriv n (complexLaplaceIntegral f) (σ : ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 ≤ r → r < ε →
      laplaceConvergesAt f (σ - r) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n F (σ : ℂ) / (n.factorial : ℂ))
  have hp : HasFPowerSeriesAt F p (σ : ℂ) := by
    dsimp [p]
    exact hF.hasFPowerSeriesAt
  have hevent : ∀ᶠ y : ℂ in nhds 0,
      HasSum (fun n : ℕ => p n (fun _ : Fin n => y))
        (F ((σ : ℂ) + y)) := hp.eventually_hasSum
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε
  have hyr : (- (r : ℂ)) ∈ Metric.ball (0 : ℂ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact hrε
  have hs := (hball hyr).summable
  have hs' : Summable (fun n : ℕ =>
      ((laplaceMoment f σ n * r ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    apply hs.congr
    intro n
    dsimp [p]
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, hderiv n,
      iteratedDeriv_laplace_eq_moment hf hσ hconv n]
    push_cast
    have hneg : (-1 : ℂ) ^ (n * 2) = 1 := by
      rw [Nat.mul_comm, pow_mul]
      norm_num
    rw [smul_eq_mul, neg_pow]
    ring_nf
    rw [hneg]
    ring
  have hsReal : Summable (fun n : ℕ =>
      laplaceMoment f σ n * r ^ n / (n.factorial : ℝ)) :=
    Complex.summable_ofReal.mp hs'
  exact laplaceConvergesAt_sub_of_summable_moments
    hf hf_nonneg hσ hconv hr hsReal

/-- Explicit-radius version of the local Landau lemma.  Its radius can be
transported by `HasFPowerSeriesOnBall.changeOrigin`, which is what lets the
global boundary argument cross a putative abscissa. -/
theorem laplaceConvergesAt_sub_of_hasFPowerSeriesOnBall
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {σ₀ σ r : ℝ} (hσ : σ₀ < σ)
    (hconv : laplaceConvergesAt f σ₀) (hr : 0 ≤ r)
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {R : ENNReal}
    (hF : HasFPowerSeriesOnBall F p (σ : ℂ) R)
    (hrR : ((‖(r : ℂ)‖₊ : ENNReal) < R))
    (hderiv : ∀ n : ℕ,
      iteratedDeriv n F (σ : ℂ) =
        iteratedDeriv n (complexLaplaceIntegral f) (σ : ℂ)) :
    laplaceConvergesAt f (σ - r) := by
  have hyr : (- (r : ℂ)) ∈ Metric.eball (0 : ℂ) R := by
    rw [mem_eball_zero_iff]
    simpa [enorm_eq_nnnorm] using hrR
  have hs := (hF.hasSum_iteratedFDeriv hyr).summable
  have hs' : Summable (fun n : ℕ =>
      ((laplaceMoment f σ n * r ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    apply hs.congr
    intro n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      hderiv n, iteratedDeriv_laplace_eq_moment hf hσ hconv n,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    have hneg : (-1 : ℂ) ^ (n * 2) = 1 := by
      rw [Nat.mul_comm, pow_mul]
      norm_num
    rw [smul_eq_mul, neg_pow]
    ring_nf
    rw [hneg]
    ring
  exact laplaceConvergesAt_sub_of_summable_moments
    hf hf_nonneg hσ hconv hr (Complex.summable_ofReal.mp hs')

private theorem eventuallyEq_of_analyticAt_of_eq_real_gt
    {F G : ℂ → ℂ} {b : ℝ}
    (hF : AnalyticAt ℂ F (b : ℂ))
    (hG : AnalyticAt ℂ G (b : ℂ))
    (hagree : ∀ τ : ℝ, b < τ → F (τ : ℂ) = G (τ : ℂ)) :
    F =ᶠ[nhds (b : ℂ)] G := by
  apply (hF.frequently_eq_iff_eventually_eq hG).mp
  rw [frequently_iff_seq_forall]
  refine ⟨fun n : ℕ =>
      ((b + 1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ), ?_, ?_⟩
  · rw [tendsto_nhdsWithin_iff]
    constructor
    · rw [tendsto_ofReal_iff]
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      norm_cast
      have hpos : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
      linarith
  · intro n
    apply hagree (b + 1 / (((n + 1 : ℕ) : ℝ)))
    have hpos : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
    linarith

/-- A holomorphic continuation agreeing with the Laplace integral on a real
right interval supplies the derivative hypothesis in the preceding local
Landau lemma. -/
theorem exists_laplaceConvergesAt_sub_of_analytic_continuation
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {a σ : ℝ} (haσ : a < σ)
    (hconv : ∀ τ : ℝ, a < τ → laplaceConvergesAt f τ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (σ : ℂ))
    (hagree : ∀ τ : ℝ, a < τ →
      complexLaplaceIntegral f (τ : ℂ) = F (τ : ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 ≤ r → r < ε →
      laplaceConvergesAt f (σ - r) := by
  let σ₀ : ℝ := (a + σ) / 2
  have ha₀ : a < σ₀ := by
    dsimp [σ₀]
    linarith
  have h₀σ : σ₀ < σ := by
    dsimp [σ₀]
    linarith
  have hconv₀ : laplaceConvergesAt f σ₀ := hconv σ₀ ha₀
  have hL : AnalyticAt ℂ (complexLaplaceIntegral f) (σ : ℂ) :=
    (analyticOnNhd_complexLaplaceIntegral_of_convergesAt
      hf hconv₀) (σ : ℂ) (by simpa using h₀σ)
  have hfreq : ∃ᶠ z : ℂ in
      nhdsWithin (σ : ℂ) ({(σ : ℂ)} : Set ℂ)ᶜ,
      F z = complexLaplaceIntegral f z := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n : ℕ =>
        ((σ + 1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ), ?_, ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · rw [tendsto_ofReal_iff]
        simpa [Nat.cast_add, Nat.cast_one] using
          (tendsto_const_nhds.add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        norm_cast
        have hpos : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
        linarith
    · intro n
      apply (hagree (σ + 1 / (((n + 1 : ℕ) : ℝ))) ?_).symm
      have hpos : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
      linarith
  have heq : F =ᶠ[nhds (σ : ℂ)] complexLaplaceIntegral f :=
    (hF.frequently_eq_iff_eventually_eq hL).mp hfreq
  apply exists_laplaceConvergesAt_sub_of_analytic_derivatives
    hf hf_nonneg h₀σ hconv₀ hF
  intro n
  exact heq.iteratedDeriv_eq n

/-- A positive good threshold for a nonnegative Laplace transform is never
minimal: analyticity at the threshold and positivity of all Taylor moments
move both convergence and agreement a definite distance to the left. -/
theorem exists_laplaceThreshold_lt_of_analytic
    {f : ℝ → ℝ} (hf : Continuous f)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    {F : ℂ → ℂ} {b : ℝ}
    (hF : AnalyticAt ℂ F (b : ℂ))
    (habove : ∀ τ : ℝ, b < τ →
      laplaceConvergesAt f τ ∧
        complexLaplaceIntegral f (τ : ℂ) = F (τ : ℂ)) :
    ∃ c : ℝ, c < b ∧ ∀ τ : ℝ, c < τ →
      laplaceConvergesAt f τ ∧
        complexLaplaceIntegral f (τ : ℂ) = F (τ : ℂ) := by
  rcases hF with ⟨p, R, hp⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos with
    ⟨d, hdpos, hdR⟩
  let e : ℝ := (d : ℝ) / 4
  have hdposR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hepos : 0 < e := by
    dsimp [e]
    positivity
  have hed : e < (d : ℝ) := by
    dsimp [e]
    linarith
  have hshift : ‖(e : ℂ)‖ₑ < R := by
    calc
      ‖(e : ℂ)‖ₑ = ENNReal.ofReal e := by
        rw [← ofReal_norm]
        simp [abs_of_nonneg hepos.le]
      _ < ENNReal.ofReal (d : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff hdposR).mpr hed
      _ = (d : ENNReal) := by simp
      _ < R := hdR
  let center : ℝ := b + e
  let left : ℝ := b - e
  let base : ℝ := b + e / 2
  have hbbase : b < base := by
    dsimp [base]
    linarith
  have hbasecenter : base < center := by
    dsimp [base, center]
    linarith
  have hconvBase : laplaceConvergesAt f base :=
    (habove base hbbase).1
  have hpCenter : HasFPowerSeriesOnBall F
      (p.changeOrigin (e : ℂ)) (center : ℂ)
      (R - ‖(e : ℂ)‖ₑ) := by
    simpa [center, enorm_eq_nnnorm] using hp.changeOrigin hshift
  have hFCenter : AnalyticAt ℂ F (center : ℂ) :=
    hpCenter.hasFPowerSeriesAt.analyticAt
  have hLCenter : AnalyticAt ℂ (complexLaplaceIntegral f)
      (center : ℂ) :=
    (analyticOnNhd_complexLaplaceIntegral_of_convergesAt
      hf hconvBase) (center : ℂ) (by simpa using hbasecenter)
  have heqCenter : F =ᶠ[nhds (center : ℂ)] complexLaplaceIntegral f :=
    eventuallyEq_of_analyticAt_of_eq_real_gt hFCenter hLCenter
      (fun τ hτ => (habove τ (lt_trans (by
        dsimp [center] at hτ ⊢
        linarith) hτ)).2.symm)
  have htwoe : 0 ≤ 2 * e := by positivity
  have htwoeR : ‖((2 * e : ℝ) : ℂ)‖ₑ <
      R - ‖(e : ℂ)‖ₑ := by
    rw [lt_tsub_iff_right]
    apply lt_trans ?_ hdR
    have hthree : 3 * e < (d : ℝ) := by
      dsimp [e]
      linarith
    calc
      ‖((2 * e : ℝ) : ℂ)‖ₑ + ‖(e : ℂ)‖ₑ =
          ENNReal.ofReal (3 * e) := by
        rw [show ‖((2 * e : ℝ) : ℂ)‖ₑ =
            ENNReal.ofReal (2 * e) by
          rw [← ofReal_norm]
          simp [abs_of_nonneg hepos.le],
          show ‖(e : ℂ)‖ₑ = ENNReal.ofReal e by
            rw [← ofReal_norm]
            simp [abs_of_nonneg hepos.le],
          ← ENNReal.ofReal_add htwoe hepos.le]
        congr 2
        ring
      _ < ENNReal.ofReal (d : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff hdposR).mpr hthree
      _ = (d : ENNReal) := by simp
  have hconvLeftRaw : laplaceConvergesAt f (center - 2 * e) :=
    laplaceConvergesAt_sub_of_hasFPowerSeriesOnBall
      hf hf_nonneg hbasecenter hconvBase htwoe hpCenter htwoeR
        (fun n => heqCenter.iteratedDeriv_eq n)
  have hcenterLeft : center - 2 * e = left := by
    dsimp [center, left]
    ring
  have hconvLeft : laplaceConvergesAt f left := by
    rwa [hcenterLeft] at hconvLeftRaw
  have hleftb : left < b := by
    dsimp [left]
    linarith
  have hLB : AnalyticAt ℂ (complexLaplaceIntegral f) (b : ℂ) :=
    (analyticOnNhd_complexLaplaceIntegral_of_convergesAt
      hf hconvLeft) (b : ℂ) (by simpa using hleftb)
  have heqB : F =ᶠ[nhds (b : ℂ)] complexLaplaceIntegral f :=
    eventuallyEq_of_analyticAt_of_eq_real_gt hp.hasFPowerSeriesAt.analyticAt
      hLB (fun τ hτ => (habove τ hτ).2.symm)
  rcases Metric.mem_nhds_iff.mp heqB with ⟨δ, hδ, hball⟩
  let q : ℝ := min e δ / 2
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqle : q ≤ e := by
    dsimp [q]
    linarith [min_le_left e δ]
  have hqδ : q < δ := by
    dsimp [q]
    have hm : 0 < min e δ := lt_min hepos hδ
    have hle := min_le_right e δ
    linarith
  refine ⟨b - q, by linarith, ?_⟩
  intro τ hτ
  have hleftτ : left ≤ τ := by
    dsimp [left] at ⊢
    linarith
  have hconvτ := laplaceConvergesAt_mono hf hconvLeft hleftτ
  refine ⟨hconvτ, ?_⟩
  by_cases hbτ : b < τ
  · exact (habove τ hbτ).2
  · symm
    apply hball
    have hτb : τ ≤ b := le_of_not_gt hbτ
    simp only [Metric.mem_ball, dist_eq_norm]
    have hcast : (τ : ℂ) - (b : ℂ) = ((τ - b : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hτb)]
    linarith

/-- The project-facing Landau boundary principle.  It says that a
nonnegative continuous Laplace transform whose meromorphic continuation is
regular on the positive real axis cannot have a positive abscissa of
convergence.  The proposition is discharged immediately below. -/
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

/-- Landau's boundary theorem for continuous nonnegative one-sided Laplace
transforms.  The proof uses the infimum of thresholds carrying both
convergence and agreement, and contradicts minimality with the explicit
Taylor-radius crossing lemma. -/
theorem nonnegativeLaplaceBoundaryPrinciple :
    NonnegativeLaplaceBoundaryPrinciple := by
  intro f F a ha hf hf_nonneg _hFmero hFanalytic hconv hagree
  intro σ hσ
  by_contra hnotconv
  let Good : ℝ → Prop := fun c => ∀ τ : ℝ, c < τ →
    laplaceConvergesAt f τ ∧
      complexLaplaceIntegral f (τ : ℂ) = F (τ : ℂ)
  let S : Set ℝ := {c | Good c}
  have haS : a ∈ S := by
    intro τ haτ
    refine ⟨hconv τ haτ, ?_⟩
    simpa [complexLaplaceIntegral] using hagree τ haτ
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hσlower : σ ∈ lowerBounds S := by
    intro c hc
    by_contra hnot
    have hcσ : c < σ := lt_of_not_ge hnot
    exact hnotconv (hc σ hcσ).1
  have hSbdd : BddBelow S := ⟨σ, hσlower⟩
  let b : ℝ := sInf S
  have hσb : σ ≤ b := by
    dsimp [b]
    exact (le_csInf_iff hSbdd hSne).mpr (fun c hc => hσlower hc)
  have hbpos : 0 < b := lt_of_lt_of_le hσ hσb
  have hbGood : Good b := by
    intro τ hbτ
    have hinfτ : sInf S < τ := by simpa [b] using hbτ
    rcases (csInf_lt_iff hSbdd hSne).mp hinfτ with ⟨c, hcS, hcτ⟩
    exact hcS τ hcτ
  rcases exists_laplaceThreshold_lt_of_analytic hf hf_nonneg
      (hFanalytic b hbpos) hbGood with ⟨c, hcb, hcGood⟩
  have hcS : c ∈ S := hcGood
  have hbc : b ≤ c := by
    dsimp [b]
    exact csInf_le hSbdd hcS
  exact (not_lt_of_ge hbc) hcb

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

/-- Suzuki pointwise positivity pushes the real Laplace transform all the
way down to every positive decay parameter. -/
theorem laplaceConvergesAt_suzukiPsi_of_pos
    (hPsi : SuzukiPsiNonnegative) {σ : ℝ} (hσ : 0 < σ) :
    laplaceConvergesAt suzukiPsi σ :=
  laplaceConvergesAt_suzukiPsi_of_pos_of_landau
    nonnegativeLaplaceBoundaryPrinciple hPsi hσ

/-- Complex Suzuki-Psi Laplace kernels are integrable throughout the open
right half-plane under pointwise positivity. -/
theorem integrableOn_suzukiPsiLaplace_of_pos
    (hPsi : SuzukiPsiNonnegative) {w : ℂ} (hw : 0 < w.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (suzukiPsi t : ℂ) *
        Complex.exp (-w * (t : ℂ)))
      (Set.Ioi 0) :=
  integrableOn_complex_laplace_of_convergesAt_re continuous_suzukiPsi
    (laplaceConvergesAt_suzukiPsi_of_pos hPsi hw)

/-- Under pointwise positivity, Suzuki's Laplace integral is analytic on
the full open right half-plane. -/
theorem analyticOnNhd_suzukiPsiLaplace_rightHalfPlane
    (hPsi : SuzukiPsiNonnegative) :
    AnalyticOnNhd ℂ suzukiPsiLaplace {w : ℂ | 0 < w.re} := by
  have heq : complexLaplaceIntegral suzukiPsi = suzukiPsiLaplace := by
    funext w
    rfl
  rw [← heq]
  intro w hw
  change 0 < w.re at hw
  let σ : ℝ := w.re / 2
  have hσ : 0 < σ := by
    dsimp [σ]
    linarith
  have hσw : σ < w.re := by
    dsimp [σ]
    linarith
  exact (analyticOnNhd_complexLaplaceIntegral_of_convergesAt
    continuous_suzukiPsi
    (laplaceConvergesAt_suzukiPsi_of_pos hPsi hσ)) w hσw

/-- Meromorphic uniqueness on the connected right half-plane shows that
the explicit xi continuation has no poles there.  The statement is phrased
as nonnegativity of its meromorphic order, so it is insensitive to the
totalized point values of meromorphic functions. -/
theorem meromorphicOrderAt_suzukiPsiLaplaceContinuation_nonneg
    (hPsi : SuzukiPsiNonnegative) {w : ℂ} (hw : 0 < w.re) :
    0 ≤ meromorphicOrderAt suzukiPsiLaplaceContinuation w := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let D : ℂ → ℂ := fun z =>
    suzukiPsiLaplaceContinuation z - suzukiPsiLaplace z
  have hFOn : MeromorphicOn suzukiPsiLaplaceContinuation U :=
    fun z _ => meromorphic_suzukiPsiLaplaceContinuation z
  have hLOn : MeromorphicOn suzukiPsiLaplace U :=
    (analyticOnNhd_suzukiPsiLaplace_rightHalfPlane hPsi).meromorphicOn
  have hDOn : MeromorphicOn D U := hFOn.sub hLOn
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hbaseU : (1 : ℂ) ∈ U := by
    change 0 < (1 : ℂ).re
    norm_num
  have heqBase : D =ᶠ[nhdsWithin (1 : ℂ) ({(1 : ℂ)} : Set ℂ)ᶜ] 0 := by
    have hhigh : ∀ᶠ z : ℂ in nhds (1 : ℂ), 1 / 2 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
        (by norm_num)
    filter_upwards [hhigh.filter_mono nhdsWithin_le_nhds] with z hz
    dsimp [D]
    rw [← suzukiPsiLaplace_eq_Q hz]
    simp
  have hbaseTop : meromorphicOrderAt D (1 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr heqBase
  have hDTop : meromorphicOrderAt D w = ⊤ := by
    by_contra hne
    have hbaseNe := hDOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (x := w) (y := (1 : ℂ)) hU (by simpa [U] using hw) hbaseU hne
    exact hbaseNe hbaseTop
  have hDeq := meromorphicOrderAt_eq_top_iff.mp hDTop
  have heqPunct : suzukiPsiLaplaceContinuation =ᶠ[
      nhdsWithin w ({w} : Set ℂ)ᶜ] suzukiPsiLaplace := by
    filter_upwards [hDeq] with z hz
    exact sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr heqPunct]
  exact (analyticOnNhd_suzukiPsiLaplace_rightHalfPlane hPsi
    w (by simpa using hw)).meromorphicOrderAt_nonneg

/-- Away from the harmless Laplace coordinate `w = 0`, the explicit
continuation recovers xi's logarithmic derivative by multiplication with
`w²`. -/
theorem logDeriv_riemannXi_half_add_eq_sq_mul_laplaceContinuation
    {w : ℂ} (hw : w ≠ 0) :
    logDeriv riemannXi ((1 / 2 : ℂ) + w) =
      w ^ 2 * suzukiPsiLaplaceContinuation w := by
  rw [suzukiPsiLaplaceContinuation, xiNevanlinnaQ]
  have harg : (1 / 2 : ℂ) - Complex.I * (Complex.I * w) =
      (1 / 2 : ℂ) + w := by
    simp [← mul_assoc]
  rw [harg]
  field_simp [hw]
  rw [I_sq]
  ring

private theorem xiSpectralParameter_im_nonpos_of_suzukiPsi_nonneg
    (hPsi : SuzukiPsiNonnegative) (a : XiZeroOccurrence) :
    (xiSpectralParameter a).im ≤ 0 := by
  by_contra hnot
  have hgamma : 0 < (xiSpectralParameter a).im := lt_of_not_ge hnot
  let ρ : ℂ := a.value
  let w : ℂ := ρ - (1 / 2 : ℂ)
  have hwre : 0 < w.re := by
    dsimp [w, ρ]
    rw [xiSpectralParameter_im] at hgamma
    simpa using hgamma
  have hwne : w ≠ 0 := by
    intro hw
    have hρhalf : ρ = (1 / 2 : ℂ) := sub_eq_zero.mp hw
    have hzero : riemannXi ρ = 0 := a.1.xi_eq_zero
    rw [hρhalf] at hzero
    exact riemannXi_half_ne_zero hzero
  have horder :=
    meromorphicOrderAt_suzukiPsiLaplaceContinuation_nonneg hPsi hwre
  obtain ⟨c, hlim⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg
    (meromorphic_suzukiPsiLaplaceContinuation w) horder
  let coord : ℂ → ℂ := fun s => s - (1 / 2 : ℂ)
  have hcoordNhds : Tendsto coord (nhds ρ) (nhds w) := by
    have hc : ContinuousAt coord ρ := by
      dsimp [coord]
      fun_prop
    simpa [coord, w] using hc.tendsto
  have hcoord : Tendsto coord
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ)
      (nhdsWithin w ({w} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordNhds.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    intro heq
    apply hs
    exact sub_left_inj.mp heq
  have hcoordPunct : Tendsto coord
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds w) :=
    hcoordNhds.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto
      (fun s => coord s ^ 2 * suzukiPsiLaplaceContinuation (coord s))
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds (w ^ 2 * c)) :=
    (hcoordPunct.pow 2).mul (hlim.comp hcoord)
  have hρhalf : ρ ≠ (1 / 2 : ℂ) := by
    intro hhalf
    have hzero : riemannXi ρ = 0 := a.1.xi_eq_zero
    rw [hhalf] at hzero
    exact riemannXi_half_ne_zero hzero
  have hcoordne : ∀ᶠ s in nhdsWithin ρ ({ρ} : Set ℂ)ᶜ,
      coord s ≠ 0 := by
    filter_upwards [eventually_ne_nhdsWithin hρhalf] with s hs
    exact sub_ne_zero.mpr hs
  have heqLog : (logDeriv riemannXi) =ᶠ[
      nhdsWithin ρ ({ρ} : Set ℂ)ᶜ]
      (fun s => coord s ^ 2 *
        suzukiPsiLaplaceContinuation (coord s)) := by
    filter_upwards [hcoordne] with s hs
    have h :=
      logDeriv_riemannXi_half_add_eq_sq_mul_laplaceContinuation hs
    dsimp [coord] at h ⊢
    rw [show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring] at h
    exact h
  have hld : Tendsto (logDeriv riemannXi)
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds (w ^ 2 * c)) :=
    hprod.congr' heqLog.symm
  exact not_tendsto_logDeriv_riemannXi_of_zero a.1.xi_eq_zero _ hld

/-- Suzuki's pointwise inequality forces every xi spectral parameter to be
real.  Landau supplies pole-freeness in one half-plane and xi reflection
excludes the other half-plane. -/
theorem XiTZerosReal_of_suzukiPsi_nonneg
    (hPsi : SuzukiPsiNonnegative) : XiTZerosReal := by
  rw [xiTZerosReal_iff_spectralParameters_real]
  intro a
  have hupper :=
    xiSpectralParameter_im_nonpos_of_suzukiPsi_nonneg hPsi a
  have hlower := xiSpectralParameter_im_nonpos_of_suzukiPsi_nonneg hPsi
    (xiOccurrenceOneSubEquiv a)
  rw [xiSpectralParameter_oneSubOccurrence] at hlower
  simp only [Complex.neg_im] at hlower
  linarith

/-- Positive semidefiniteness of the Riemann screw kernel forces all xi
spectral parameters to be real.  This is Suzuki's specialized converse,
proved here through pointwise positivity and the Landau boundary principle. -/
theorem riemannScrewKernel_psd_implies_XiTZerosReal
    (hPSD : KernelPSD riemannScrewKernel) : XiTZerosReal :=
  XiTZerosReal_of_suzukiPsi_nonneg
    (suzukiPsi_nonnegative_of_kernelPSD hPSD)

/-- The critical-line formulation is equivalent to positive
semidefiniteness of the Riemann screw kernel. -/
theorem xiTZerosReal_iff_riemannScrewKernel_psd :
    XiTZerosReal ↔ KernelPSD riemannScrewKernel :=
  ⟨riemannScrewKernel_psd_of_XiTZerosReal,
    riemannScrewKernel_psd_implies_XiTZerosReal⟩

/-- Suzuki's screw-kernel criterion for the Riemann hypothesis.  This is an
equivalence of propositions; it does not assert either side. -/
theorem riemannHypothesis_iff_screwKernelPSD :
    RiemannHypothesis ↔ KernelPSD riemannScrewKernel :=
  riemannHypothesis_iff_XiTZerosReal.trans
    xiTZerosReal_iff_riemannScrewKernel_psd

/-- The project-specific screw-to-Nevanlinna implication, obtained through
Suzuki's pointwise criterion rather than a general Krein--Langer theorem. -/
theorem xiNevanlinna_of_screwKernelPSD
    (hPSD : KernelPSD riemannScrewKernel) : XiNevanlinna :=
  xiNevanlinna_of_XiTZerosReal
    (riemannScrewKernel_psd_implies_XiTZerosReal hPSD)

/-- The formerly open project-facing screw-to-Nevanlinna boundary. -/
theorem screwToNevanlinnaBridge : ScrewToNevanlinnaBridge :=
  xiNevanlinna_of_screwKernelPSD

end RHGarden
