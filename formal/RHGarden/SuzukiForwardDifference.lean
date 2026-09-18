import RHGarden.SuzukiShiftedLandau
import RHGarden.SuzukiInitialInterval

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

Forward differences of the actual Suzuki function. The divided differences
below assign the removable value at zero, rather than using a totalized
quotient with an incorrect value there. No zero-location hypothesis is used.
-/

noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology Interval
namespace RHGarden

theorem xiZeroOccurrence_nonempty : Nonempty XiZeroOccurrence := by
  by_contra hn
  have : IsEmpty XiZeroOccurrence := not_nonempty_iff.mp hn
  have hz : suzukiPsi (Real.log 2) = 0 := by
    simp [suzukiPsi, suzukiPsiZero]
  have hp := suzukiPsi_pos_zero_to_log_three
    (t := Real.log 2) (Real.log_pos (by norm_num))
    (Real.log_le_log (by norm_num) (by norm_num : (2 : ℝ) ≤ 3))
  linarith

theorem deriv_riemannXi_half_eq_zero : deriv riemannXi (1 / 2 : ℂ) = 0 := by
  have h := deriv_riemannXi_one_sub (1 / 2 : ℂ)
  norm_num at h
  linear_combination h / 2

def suzukiCenteredLogDeriv (z : ℂ) : ℂ := logDeriv riemannXi ((1 / 2 : ℂ) + z)

@[simp] theorem suzukiCenteredLogDeriv_zero : suzukiCenteredLogDeriv 0 = 0 := by
  rw [suzukiCenteredLogDeriv, add_zero, logDeriv_apply, deriv_riemannXi_half_eq_zero,
    zero_div]

theorem analyticAt_suzukiCenteredLogDeriv_real (x : ℝ) :
    AnalyticAt ℂ suzukiCenteredLogDeriv (x : ℂ) := by
  have ha := analyticAt_riemannXi ((1 / 2 : ℂ) + (x : ℂ))
  have hn : riemannXi ((1 / 2 : ℂ) + (x : ℂ)) ≠ 0 := by
    simpa using riemannXi_real_ne_zero (1 / 2 + x)
  exact (ha.deriv.div ha hn).comp (by fun_prop :
    AnalyticAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + z) (x : ℂ))

private theorem analyticAt_dslope_same {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) : AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

private theorem analyticAt_dslope_ne {f : ℂ → ℂ} {a z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ≠ a) : AnalyticAt ℂ (dslope f a) z := by
  have h : AnalyticAt ℂ (fun w => (f w - f a) / (w - a)) z :=
    (hf.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hz)
  apply h.congr
  filter_upwards [dslope_eventuallyEq_slope_of_ne f hz] with w hw
  simp [hw, slope, smul_eq_mul, div_eq_mul_inv, mul_comm]

def suzukiForwardDifference (ell t : ℝ) : ℝ := suzukiPsi (t + ell) - suzukiPsi t

theorem continuous_suzukiForwardDifference (ell : ℝ) :
    Continuous (suzukiForwardDifference ell) :=
  (continuous_suzukiPsi.comp (continuous_id.add continuous_const)).sub continuous_suzukiPsi

/-- The analytic extension, including its divided-difference value at zero. -/
def suzukiForwardLaplaceContinuation (ell : ℝ) (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) 0 z *
    dslope suzukiCenteredLogDeriv 0 z -
  Complex.exp ((ell : ℂ) * z) * compactLaplaceInitial suzukiPsi ell z

theorem suzukiForwardLaplaceContinuation_of_ne (ell : ℝ) {z : ℂ} (hz : z ≠ 0) :
    suzukiForwardLaplaceContinuation ell z =
      (Complex.exp ((ell : ℂ) * z) - 1) *
        suzukiPsiShiftedLaplaceContinuation 0 z -
      Complex.exp ((ell : ℂ) * z) * compactLaplaceInitial suzukiPsi ell z := by
  simp only [suzukiForwardLaplaceContinuation, dslope_of_ne _ hz, slope,
    sub_zero, mul_zero, Complex.exp_zero, suzukiCenteredLogDeriv_zero, smul_eq_mul,
    vsub_eq_sub]
  simp only [suzukiCenteredLogDeriv, suzukiPsiShiftedLaplaceContinuation,
    add_zero, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem analyticAt_suzukiForwardLaplaceContinuation_real (ell x : ℝ) :
    AnalyticAt ℂ (suzukiForwardLaplaceContinuation ell) (x : ℂ) := by
  have hE : AnalyticAt ℂ (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) (x : ℂ) := by
    fun_prop
  have hL := analyticAt_suzukiCenteredLogDeriv_real x
  have hEd : AnalyticAt ℂ (dslope (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) 0)
      (x : ℂ) := by
    by_cases hx : (x : ℂ) = 0
    · rw [hx] at hE ⊢
      exact analyticAt_dslope_same hE
    · exact analyticAt_dslope_ne hE hx
  have hLd : AnalyticAt ℂ (dslope suzukiCenteredLogDeriv 0) (x : ℂ) := by
    by_cases hx : (x : ℂ) = 0
    · rw [hx] at hL ⊢
      exact analyticAt_dslope_same hL
    · exact analyticAt_dslope_ne hL hx
  exact (hEd.mul hLd).sub (hE.mul
    ((differentiable_compactLaplaceInitial continuous_suzukiPsi ell).analyticAt _))

theorem suzukiForwardLaplaceContinuation_zero (ell : ℝ) :
    suzukiForwardLaplaceContinuation ell 0 =
      (ell : ℂ) * (deriv (deriv riemannXi) (1 / 2 : ℂ) /
        riemannXi (1 / 2 : ℂ)) - compactLaplaceInitial suzukiPsi ell 0 := by
  have hE : HasDerivAt (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) (ell : ℂ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (ell : ℂ)).cexp)
  have hxi := (analyticAt_riemannXi (1 / 2 : ℂ))
  have hld := hxi.deriv.differentiableAt.hasDerivAt.div
    hxi.differentiableAt.hasDerivAt riemannXi_half_ne_zero
  have hld' : HasDerivAt (logDeriv riemannXi)
      (deriv (deriv riemannXi) (1 / 2 : ℂ) / riemannXi (1 / 2 : ℂ)) (1 / 2 : ℂ) := by
    convert hld using 1 <;> first | rfl |
      (rw [deriv_riemannXi_half_eq_zero];
       simp only [zero_mul, sub_zero];
       rw [pow_two, mul_div_mul_right _ _ riemannXi_half_ne_zero])
  have hc := (by simpa only [id_eq, add_zero] using hld' :
      HasDerivAt (logDeriv riemannXi)
      (deriv (deriv riemannXi) (1 / 2 : ℂ) / riemannXi (1 / 2 : ℂ))
      ((1 / 2 : ℂ) + id 0)).comp (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_add (1 / 2 : ℂ))
  have hc' : deriv suzukiCenteredLogDeriv 0 =
      deriv (deriv riemannXi) (1 / 2 : ℂ) / riemannXi (1 / 2 : ℂ) := by
    change deriv (fun z : ℂ => logDeriv riemannXi ((1 / 2 : ℂ) + z)) (0 : ℂ) = _
    simpa only [suzukiCenteredLogDeriv, Function.comp_def, mul_one, id_eq] using hc.deriv
  simp [suzukiForwardLaplaceContinuation, dslope_same, hE.deriv, hc']

theorem meromorphic_suzukiForwardLaplaceContinuation (ell : ℝ) :
    Meromorphic (suzukiForwardLaplaceContinuation ell) := by
  intro z
  by_cases hz : z = 0
  · subst z
    exact (analyticAt_suzukiForwardLaplaceContinuation_real ell 0).meromorphicAt
  · have hE : AnalyticAt ℂ (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) z := by
      fun_prop
    have hC := (differentiable_compactLaplaceInitial continuous_suzukiPsi ell).analyticAt z
    have h := ((hE.sub (analyticAt_const (v := (1 : ℂ)))).meromorphicAt.mul
      (meromorphic_suzukiPsiShiftedLaplaceContinuation 0 z)).sub (hE.mul hC).meromorphicAt
    apply h.congr
    filter_upwards [(eventually_ne_nhds hz).filter_mono nhdsWithin_le_nhds] with w hw
    exact (suzukiForwardLaplaceContinuation_of_ne ell hw).symm

theorem laplaceConvergesAt_suzukiForwardDifference {ell σ : ℝ}
    (hell : 0 ≤ ell) (hσ : 1 / 2 < σ) :
    laplaceConvergesAt (suzukiForwardDifference ell) σ := by
  have h := laplaceConvergesAt_suzukiPsi_of_half_lt hσ
  have ht := laplaceConvergesAt_laplaceTail_of_convergesAt hell h
  exact (ht.sub h).congr (Filter.Eventually.of_forall fun t => by
    simp [suzukiForwardDifference, laplaceTail, sub_mul])

/-- Translation is justified by absolute convergence and splitting the
compact initial interval; no differentiation of the zero series is used. -/
theorem complexLaplaceIntegral_suzukiForwardDifference {ell : ℝ}
    (hell : 0 ≤ ell) {z : ℂ} (hz : 1 / 2 < z.re) :
    complexLaplaceIntegral (suzukiForwardDifference ell) z =
      suzukiForwardLaplaceContinuation ell z := by
  have hc := laplaceConvergesAt_suzukiPsi_of_half_lt hz
  have hi := integrableOn_complex_laplace_of_convergesAt_re continuous_suzukiPsi hc
  have ht := integrableOn_complex_laplace_of_convergesAt_re
    (continuous_laplaceTail continuous_suzukiPsi ell)
    (laplaceConvergesAt_laplaceTail_of_convergesAt hell hc)
  have hs := complexLaplaceIntegral_eq_compactInitial_add_tail
    continuous_suzukiPsi hell hi
  have hbase : complexLaplaceIntegral suzukiPsi z =
      suzukiPsiShiftedLaplaceContinuation 0 z := by
    have hfun : suzukiPsiShifted 0 = suzukiPsi := funext suzukiPsiShifted_zero_parameter
    simpa only [hfun] using complexLaplaceIntegral_suzukiPsiShifted_eq_continuation_of_re
      0 (by linarith : 0 < z.re) (by simpa using hz)
  have he : Complex.exp ((ell : ℂ) * z) * Complex.exp (-z * (ell : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp [mul_comm]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  rw [suzukiForwardLaplaceContinuation_of_ne ell hz0]
  have hsub : complexLaplaceIntegral (suzukiForwardDifference ell) z =
      complexLaplaceIntegral (laplaceTail suzukiPsi ell) z -
        complexLaplaceIntegral suzukiPsi z := by
    unfold complexLaplaceIntegral
    rw [← integral_sub ht hi]
    apply integral_congr_ae
    filter_upwards with t
    simp [suzukiForwardDifference, laplaceTail, sub_mul]
  rw [hsub, ← hbase]
  linear_combination -Complex.exp ((ell : ℂ) * z) * hs +
    -complexLaplaceIntegral (laplaceTail suzukiPsi ell) z * he

/-! A reusable consequence of Landau and uniqueness of meromorphic
continuation. This lemma is analytic infrastructure, not an arithmetic
or positivity hypothesis for the Suzuki function. -/
theorem meromorphicOrderAt_nonneg_of_eventual_nonneg
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a) (hf : Continuous f)
    (hsign : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ f t)
    (hF : Meromorphic F)
    (hreal : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F (σ : ℂ))
    (hconv : ∀ σ : ℝ, a < σ → laplaceConvergesAt f σ)
    (hagree : ∀ z : ℂ, a < z.re → complexLaplaceIntegral f z = F z)
    {w : ℂ} (hw : 0 < w.re) : 0 ≤ meromorphicOrderAt F w := by
  have hall : ∀ σ : ℝ, 0 < σ → laplaceConvergesAt f σ := by
    intro σ hσ
    exact eventuallyNonnegativeLaplaceBoundaryPrinciple ha hf hsign hF hreal hconv
      (fun τ hτ => hagree (τ : ℂ) hτ) hσ
  have hL : AnalyticOnNhd ℂ (complexLaplaceIntegral f) {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    exact analyticOnNhd_complexLaplaceIntegral_of_convergesAt hf
      (hall (z.re / 2) (by linarith)) z (show z.re / 2 < z.re by linarith)
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let d : ℂ → ℂ := fun z => F z - complexLaplaceIntegral f z
  have hFU : MeromorphicOn F U := fun z _ => hF z
  have hd : MeromorphicOn d U := hFU.sub hL.meromorphicOn
  have hb : ((a + 1 : ℝ) : ℂ) ∈ U := by change 0 < a + 1; linarith
  have hbase : d =ᶠ[𝓝[≠] ((a + 1 : ℝ) : ℂ)] 0 := by
    have he : ∀ᶠ z : ℂ in 𝓝 ((a + 1 : ℝ) : ℂ), a < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem (by simp)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    simp [d, hagree z hz]
  have htop : meromorphicOrderAt d w = ⊤ := by
    by_contra hn
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected
      (x := w) (y := ((a + 1 : ℝ) : ℂ))
      (convex_halfSpace_re_gt 0).isPreconnected hw hb hn)
      (meromorphicOrderAt_eq_top_iff.mpr hbase)
  have heq : F =ᶠ[𝓝[≠] w] complexLaplaceIntegral f := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with z hz
    exact sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr heq]
  exact (hL w hw).meromorphicOrderAt_nonneg

/-- A genuine nonreal zero supplies a positive difference length whose
exponential factor does not cancel its pole. Only the critical strip,
not the critical line, is used. -/
theorem exists_suzukiForward_surviving_zero :
    ∃ (ell : ℝ) (rho : ℂ), 0 < ell ∧ riemannXi rho = 0 ∧
      rho.im ≠ 0 ∧ ell = Real.pi / |rho.im| ∧
      (Complex.exp ((ell : ℂ) * (rho - 1 / 2))).im = 0 ∧
      (Complex.exp ((ell : ℂ) * (rho - 1 / 2))).re < 0 ∧
      0 < (rho - 1 / 2 + 1).re := by
  obtain ⟨a⟩ := xiZeroOccurrence_nonempty
  let rho : ℂ := a.value
  have hz : riemannXi rho = 0 := a.1.xi_eq_zero
  have him : rho.im ≠ 0 := by
    intro hi
    have he : rho = (rho.re : ℂ) := by apply Complex.ext <;> simp [hi]
    exact riemannXi_real_ne_zero rho.re (he ▸ hz)
  let ell : ℝ := Real.pi / |rho.im|
  have hell : 0 < ell := div_pos Real.pi_pos (abs_pos.mpr him)
  have hphase : ell * rho.im = Real.pi ∨ ell * rho.im = -Real.pi := by
    rcases lt_or_gt_of_ne him with h | h
    · right
      dsimp [ell]
      rw [abs_of_neg h]
      field_simp
    · left
      simp [ell, abs_of_pos h, him]
  have hcos : Real.cos (ell * rho.im) = -1 := by
    rcases hphase with h | h <;> rw [h] <;> simp
  have hsin : Real.sin (ell * rho.im) = 0 := by
    rcases hphase with h | h <;> rw [h] <;> simp
  refine ⟨ell, rho, hell, hz, him, rfl, ?_, ?_, ?_⟩
  · rw [Complex.exp_im]
    have hi : ((ell : ℂ) * (rho - 1 / 2)).im = ell * rho.im := by
      simp [Complex.mul_im]
    rw [hi, hsin, mul_zero]
  · rw [Complex.exp_re]
    have hi : ((ell : ℂ) * (rho - 1 / 2)).im = ell * rho.im := by
      simp [Complex.mul_im]
    rw [hi, hcos]
    nlinarith [Real.exp_pos (((ell : ℂ) * (rho - 1 / 2)).re)]
  · have hr := a.1.re_mem_Ioo.1
    change 0 < (rho - 1 / 2 + 1).re
    simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    change 0 < rho.re - 1 / 2 + 1
    change 0 < rho.re at hr
    linarith

theorem not_tendsto_suzukiForwardLaplaceContinuation_of_zero
    {ell : ℝ} {rho : ℂ} (hrho : riemannXi rho = 0)
    (hz : rho - 1 / 2 ≠ 0)
    (he : Complex.exp ((ell : ℂ) * (rho - 1 / 2)) ≠ 1) (c : ℂ) :
    ¬ Tendsto (suzukiForwardLaplaceContinuation ell) (𝓝[≠] (rho - 1 / 2)) (𝓝 c) := by
  intro hlim
  let coord : ℂ → ℂ := fun s => s - 1 / 2
  let z : ℂ := rho - 1 / 2
  have hcoordN : Tendsto coord (𝓝 rho) (𝓝 z) := by
    exact (continuousAt_id.sub continuousAt_const).tendsto
  have hcoord : Tendsto coord (𝓝[≠] rho) (𝓝[≠] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordN.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_compl_iff, mem_singleton_iff] at hs ⊢
    exact fun h => hs (sub_left_inj.mp h)
  let correction : ℂ → ℂ := fun w =>
    Complex.exp ((ell : ℂ) * w) * compactLaplaceInitial suzukiPsi ell w
  have hcorr : ContinuousAt correction z := by
    exact (by fun_prop : ContinuousAt (fun w : ℂ => Complex.exp ((ell : ℂ) * w)) z).mul
      (differentiable_compactLaplaceInitial continuous_suzukiPsi ell).continuous.continuousAt
  have hfac : ContinuousAt (fun w : ℂ => w ^ 2 /
      (Complex.exp ((ell : ℂ) * w) - 1)) z := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact sub_ne_zero.mpr he
  have hL := ((hfac.tendsto.comp hcoordN).mono_left nhdsWithin_le_nhds).mul
    ((hlim.comp hcoord).add ((hcorr.tendsto.comp hcoordN).mono_left nhdsWithin_le_nhds))
  have hne : ∀ᶠ s in 𝓝[≠] rho, coord s ≠ 0 ∧
      Complex.exp ((ell : ℂ) * coord s) ≠ 1 := by
    have h0 := hcoordN.eventually (eventually_ne_nhds hz)
    have h1 := ((by fun_prop : ContinuousAt
      (fun s : ℂ => Complex.exp ((ell : ℂ) * coord s)) rho).eventually_ne he)
    exact (h0.and h1).filter_mono nhdsWithin_le_nhds
  have heq : (logDeriv riemannXi) =ᶠ[𝓝[≠] rho]
      (fun s => coord s ^ 2 / (Complex.exp ((ell : ℂ) * coord s) - 1) *
        (suzukiForwardLaplaceContinuation ell (coord s) + correction (coord s))) := by
    filter_upwards [hne] with s hs
    rw [suzukiForwardLaplaceContinuation_of_ne ell hs.1]
    simp only [correction, sub_add_cancel, suzukiPsiShiftedLaplaceContinuation,
      add_zero, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    have hc : (1 / 2 : ℂ) + coord s = s := by dsimp [coord]; ring
    rw [hc]
    field_simp [hs.1, sub_ne_zero.mpr hs.2]
    rw [mul_div_cancel_right₀ _ (by simpa [mul_comm] using sub_ne_zero.mpr hs.2)]
  exact not_tendsto_logDeriv_riemannXi_of_zero hrho _ (hL.congr' heq.symm)

/-- Multiplication by a real exponential translates the complex Laplace
parameter; the real scalar is retained, including its sign. -/
theorem complexLaplaceIntegral_exp_mul (f : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    complexLaplaceIntegral (fun t => c * Real.exp t * f t) z =
      (c : ℂ) * complexLaplaceIntegral f (z - 1) := by
  unfold complexLaplaceIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  have he : (t : ℂ) + -z * (t : ℂ) = -(z - 1) * (t : ℂ) := by ring
  rw [show (c : ℂ) * Complex.exp (t : ℂ) * (f t : ℂ) * Complex.exp (-z * (t : ℂ)) =
      (c : ℂ) * (f t : ℂ) * (Complex.exp (t : ℂ) * Complex.exp (-z * (t : ℂ))) by ring,
    ← Complex.exp_add, he]
  ring

theorem laplaceConvergesAt_exp_mul {f : ℝ → ℝ} {σ : ℝ}
    (h : laplaceConvergesAt f (σ - 1)) (c : ℝ) :
    laplaceConvergesAt (fun t => c * Real.exp t * f t) σ := by
  apply (h.const_mul (c : ℂ)).congr
  filter_upwards with t
  push_cast
  have he : -(↑σ - 1) * (t : ℂ) = (t : ℂ) + -(↑σ) * (t : ℂ) := by ring
  rw [he, Complex.exp_add]
  ring

theorem not_eventually_nonnegative_suzukiForwardDifference_mul
    {ell : ℝ} (hell : 0 ≤ ell) {rho : ℂ} (hrho : riemannXi rho = 0)
    (hz : rho - 1 / 2 ≠ 0)
    (he : Complex.exp ((ell : ℂ) * (rho - 1 / 2)) ≠ 1)
    (hstrip : 0 < (rho - 1 / 2 + 1).re)
    {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ c * suzukiForwardDifference ell t := by
  rintro ⟨T, hT⟩
  let g : ℝ → ℝ := fun t => c * Real.exp t * suzukiForwardDifference ell t
  let G : ℂ → ℂ := fun z => (c : ℂ) * suzukiForwardLaplaceContinuation ell (z - 1)
  have hg : Continuous g :=
    (continuous_const.mul Real.continuous_exp).mul (continuous_suzukiForwardDifference ell)
  have hgsign : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ g t := by
    refine ⟨T, fun t ht => ?_⟩
    dsimp [g]
    nlinarith [hT t ht, Real.exp_pos t]
  have hG : Meromorphic G := by
    intro z
    exact (MeromorphicAt.const (c : ℂ) z).mul
      ((meromorphic_suzukiForwardLaplaceContinuation ell (z - 1)).comp_analyticAt (g := fun w : ℂ => w - 1)
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) z))
  have hreal : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G (σ : ℂ) := by
    intro σ _
    have hh := analyticAt_suzukiForwardLaplaceContinuation_real ell (σ - 1)
    have hh' : AnalyticAt ℂ (suzukiForwardLaplaceContinuation ell) ((σ : ℂ) - 1) := by
      simpa using hh
    exact analyticAt_const.mul (hh'.comp (f := fun w : ℂ => w - 1) (by fun_prop :
      AnalyticAt ℂ (fun w : ℂ => w - 1) (σ : ℂ)))
  have hconv : ∀ σ : ℝ, (2 : ℝ) < σ → laplaceConvergesAt g σ := by
    intro σ hσ
    exact laplaceConvergesAt_exp_mul
      (laplaceConvergesAt_suzukiForwardDifference hell (by linarith)) c
  have hagree : ∀ z : ℂ, (2 : ℝ) < z.re → complexLaplaceIntegral g z = G z := by
    intro z hzre
    rw [complexLaplaceIntegral_exp_mul]
    rw [complexLaplaceIntegral_suzukiForwardDifference hell (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)]
  have horder := meromorphicOrderAt_nonneg_of_eventual_nonneg (by norm_num : (0 : ℝ) < 2)
    hg hgsign hG hreal hconv hagree hstrip
  obtain ⟨v, hv⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg
    (hG (rho - 1 / 2 + 1)) horder
  have hshift : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (rho - 1 / 2))
      (𝓝[≠] (rho - 1 / 2 + 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz'
    simp only [mem_compl_iff, mem_singleton_iff] at hz' ⊢
    exact fun h => hz' (add_right_cancel h)
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hlim := (hv.comp hshift).const_mul (c : ℂ)⁻¹
  have hlim' : Tendsto (suzukiForwardLaplaceContinuation ell)
      (𝓝[≠] (rho - 1 / 2)) (𝓝 ((c : ℂ)⁻¹ * v)) := by
    simpa [G, ← mul_assoc, hc'] using hlim
  exact not_tendsto_suzukiForwardLaplaceContinuation_of_zero hrho hz he _ hlim'

/-- Unconditional cofinal oscillation of one continuous forward difference.
The exponential shift moves the selected pole strictly into the half-plane
controlled by Landau, even if the zero lies on the critical line. -/
theorem suzukiForwardDifference_cofinal_signs :
    ∃ ell : ℝ, 0 < ell ∧
      (∀ T : ℝ, ∃ t : ℝ, T < t ∧ 0 < suzukiForwardDifference ell t) ∧
      (∀ T : ℝ, ∃ t : ℝ, T < t ∧ suzukiForwardDifference ell t < 0) := by
  obtain ⟨ell, rho, hell, hrho, him, _, _, hneg, hstrip⟩ :=
    exists_suzukiForward_surviving_zero
  have hz : rho - 1 / 2 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact him hi
  have he : Complex.exp ((ell : ℂ) * (rho - 1 / 2)) ≠ 1 := by
    intro h
    rw [h] at hneg
    norm_num at hneg
  refine ⟨ell, hell, ?_, ?_⟩
  · intro T
    by_contra hn
    push Not at hn
    apply not_eventually_nonnegative_suzukiForwardDifference_mul hell.le hrho hz he hstrip
      (by norm_num : (-1 : ℝ) ≠ 0)
    exact ⟨T + 1, fun t ht => by have := hn t (by linarith); linarith⟩
  · intro T
    by_contra hn
    push Not at hn
    apply not_eventually_nonnegative_suzukiForwardDifference_mul hell.le hrho hz he hstrip
      (by norm_num : (1 : ℝ) ≠ 0)
    exact ⟨T + 1, fun t ht => by simpa using hn t (by linarith)⟩

theorem suzukiPsi_not_eventually_monotone :
    ¬ ∃ T : ℝ, MonotoneOn suzukiPsi (Ici T) := by
  rintro ⟨T, hT⟩
  obtain ⟨ell, hell, _, hneg⟩ := suzukiForwardDifference_cofinal_signs
  obtain ⟨t, ht, hd⟩ := hneg T
  have h := hT (show t ∈ Ici T from ht.le)
    (show t + ell ∈ Ici T by change T ≤ t + ell; linarith)
    (by linarith : t ≤ t + ell)
  dsimp [suzukiForwardDifference] at hd
  linarith

theorem suzukiPsi_not_eventually_antitone :
    ¬ ∃ T : ℝ, AntitoneOn suzukiPsi (Ici T) := by
  rintro ⟨T, hT⟩
  obtain ⟨ell, hell, hpos, _⟩ := suzukiForwardDifference_cofinal_signs
  obtain ⟨t, ht, hd⟩ := hpos T
  have h := hT (show t ∈ Ici T from ht.le)
    (show t + ell ∈ Ici T by change T ≤ t + ell; linarith)
    (by linarith : t ≤ t + ell)
  dsimp [suzukiForwardDifference] at hd
  linarith

/-- The actual residue, with the zero's multiplicity retained. The compact
correction is entire and has zero residue. -/
theorem suzukiForwardLaplaceContinuation_residue (ell : ℝ) {rho : ℂ}
    (hz : rho - 1 / 2 ≠ 0) :
    Tendsto (fun z : ℂ => (z - (rho - 1 / 2)) * suzukiForwardLaplaceContinuation ell z)
      (𝓝[≠] (rho - 1 / 2))
      (𝓝 ((xiMultiplicity rho : ℂ) *
        (Complex.exp ((ell : ℂ) * (rho - 1 / 2)) - 1) / (rho - 1 / 2) ^ 2)) := by
  let z0 : ℂ := rho - 1 / 2
  let coord : ℂ → ℂ := fun z => (1 / 2 : ℂ) + z
  have hcoordN : Tendsto coord (𝓝 z0) (𝓝 rho) := by
    have hc : ContinuousAt coord z0 := continuousAt_const.add continuousAt_id
    have he : coord z0 = rho := by dsimp [coord, z0]; ring
    simpa only [he] using hc.tendsto
  have hcoord : Tendsto coord (𝓝[≠] z0) (𝓝[≠] rho) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordN.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hne
    simp only [mem_compl_iff, mem_singleton_iff] at hne ⊢
    intro he
    apply hne
    dsimp [coord] at he
    dsimp [z0]
    linear_combination he
  have hld := (tendsto_mul_logDeriv_riemannXi rho).comp hcoord
  let fac : ℂ → ℂ := fun z => (Complex.exp ((ell : ℂ) * z) - 1) / z ^ 2
  have hfac : ContinuousAt fac z0 := by
    exact (by fun_prop : ContinuousAt (fun z : ℂ => Complex.exp ((ell : ℂ) * z) - 1) z0).div
      (by fun_prop) (pow_ne_zero 2 hz)
  let corr : ℂ → ℂ := fun z => Complex.exp ((ell : ℂ) * z) * compactLaplaceInitial suzukiPsi ell z
  have hcorr : ContinuousAt corr z0 :=
    (by fun_prop : ContinuousAt (fun z : ℂ => Complex.exp ((ell : ℂ) * z)) z0).mul
      (differentiable_compactLaplaceInitial continuous_suzukiPsi ell).continuous.continuousAt
  have hzero : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    have hh : Tendsto (fun z : ℂ => z - z0) (𝓝 z0) (𝓝 0) := by
      have hc' : ContinuousAt (fun z : ℂ => z - z0) z0 :=
        continuousAt_id.sub continuousAt_const
      simpa using hc'.tendsto
    exact hh.mono_left nhdsWithin_le_nhds
  have h := (hld.mul (hfac.tendsto.mono_left nhdsWithin_le_nhds)).sub
    (hzero.mul (hcorr.tendsto.mono_left nhdsWithin_le_nhds))
  have hlim : Tendsto
      (fun z : ℂ => ((coord z - rho) * logDeriv riemannXi (coord z)) * fac z - (z - z0) * corr z)
      (𝓝[≠] z0)
      (𝓝 ((xiMultiplicity rho : ℂ) * (Complex.exp ((ell : ℂ) * z0) - 1) / z0 ^ 2)) := by
    simpa only [zero_mul, sub_zero, fac, mul_div_assoc, Function.comp_apply] using h
  apply hlim.congr'
  filter_upwards [(eventually_ne_nhds hz).filter_mono nhdsWithin_le_nhds] with z hzne
  rw [suzukiForwardLaplaceContinuation_of_ne ell hzne]
  dsimp [fac, corr, coord, z0, suzukiPsiShiftedLaplaceContinuation]
  push_cast
  simp only [add_zero]
  ring

theorem suzukiForward_residue_ne_zero {ell : ℝ} {rho : ℂ}
    (hrho : riemannXi rho = 0) (hz : rho - 1 / 2 ≠ 0)
    (he : Complex.exp ((ell : ℂ) * (rho - 1 / 2)) ≠ 1) :
    (xiMultiplicity rho : ℂ) * (Complex.exp ((ell : ℂ) * (rho - 1 / 2)) - 1) /
      (rho - 1 / 2) ^ 2 ≠ 0 := by
  have hk : xiMultiplicity rho ≠ 0 := by
    intro h
    have hc := xiMultiplicity_cast rho
    rw [h] at hc
    exact ((xiDivisor_ne_zero_iff rho).mpr hrho) (by simpa using hc.symm)
  exact div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hk) (sub_ne_zero.mpr he))
    (pow_ne_zero 2 hz)

end RHGarden
