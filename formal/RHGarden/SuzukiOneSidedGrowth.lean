import RHGarden.SuzukiForwardDifference

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

One-sided exponential lower growth of the original Suzuki function forces
a zero-free half-plane. Ordinary exponential damping here is NOT the
Volterra-transformed `suzukiPsiShifted` family. The lower bound is a premise,
not a new arithmetic estimate or a proof of RH.
-/
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology
namespace RHGarden

theorem complexLaplaceIntegral_exp_damp (f : ℝ → ℝ) (σ : ℝ) (z : ℂ) :
    complexLaplaceIntegral (fun t => Real.exp (-σ * t) * f t) z =
      complexLaplaceIntegral f (z + (σ : ℂ)) := by
  unfold complexLaplaceIntegral
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  rw [show Complex.exp (-(σ : ℂ) * (t : ℂ)) * (f t : ℂ) *
      Complex.exp (-z * (t : ℂ)) =
      (f t : ℂ) * (Complex.exp (-(σ : ℂ) * (t : ℂ)) *
        Complex.exp (-z * (t : ℂ))) by ring, ← Complex.exp_add]
  congr 2
  ring

theorem laplaceConvergesAt_exp_damp {f : ℝ → ℝ} {σ τ : ℝ}
    (h : laplaceConvergesAt f (τ + σ)) :
    laplaceConvergesAt (fun t => Real.exp (-σ * t) * f t) τ := by
  apply h.congr
  filter_upwards with t
  push_cast
  rw [show -((τ : ℂ) + (σ : ℂ)) * (t : ℂ) =
    -(σ : ℂ) * (t : ℂ) + -(τ : ℂ) * (t : ℂ) by ring, Complex.exp_add]
  ring

theorem laplaceConvergesAt_const (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    laplaceConvergesAt (fun _ => C) τ := by
  exact (integrableOn_exp_mul_complex_Ioi
    (a := -(τ : ℂ)) (by simpa using neg_neg_of_pos hτ) 0).const_mul (C : ℂ)

theorem complexLaplaceIntegral_const (C : ℝ) {z : ℂ} (hz : 0 < z.re) :
    complexLaplaceIntegral (fun _ => C) z = (C : ℂ) / z := by
  unfold complexLaplaceIntegral
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hz)]
  simp [div_eq_mul_inv]

/-- This is exponential damping plus a constant, not Suzuki's special shift. -/
def suzukiDampedWithConstant (σ C t : ℝ) : ℝ :=
  Real.exp (-σ * t) * suzukiPsi t + C

def suzukiDampedLaplaceContinuation (σ C : ℝ) (z : ℂ) : ℂ :=
  suzukiPsiShiftedLaplaceContinuation 0 (z + (σ : ℂ)) + (C : ℂ) / z

theorem continuous_suzukiDampedWithConstant (σ C : ℝ) :
    Continuous (suzukiDampedWithConstant σ C) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_suzukiPsi).add continuous_const

theorem laplaceConvergesAt_suzukiDampedWithConstant (σ C : ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hstrip : 1 / 2 < τ + σ) :
    laplaceConvergesAt (suzukiDampedWithConstant σ C) τ := by
  exact ((laplaceConvergesAt_exp_damp
    (laplaceConvergesAt_suzukiPsi_of_half_lt hstrip)).add
    (laplaceConvergesAt_const C hτ)).congr (Filter.Eventually.of_forall fun t => by
      simp [suzukiDampedWithConstant, add_mul])

/-- Initial transform: both the constant and the damped original term
are absolutely integrable under the displayed half-plane conditions. -/
theorem complexLaplaceIntegral_suzukiDampedWithConstant (σ C : ℝ) {z : ℂ}
    (hz : 0 < z.re) (hstrip : 1 / 2 < z.re + σ) :
    complexLaplaceIntegral (suzukiDampedWithConstant σ C) z =
      suzukiDampedLaplaceContinuation σ C z := by
  have hd := integrableOn_complex_laplace_of_convergesAt_re
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_suzukiPsi)
    (laplaceConvergesAt_exp_damp (laplaceConvergesAt_suzukiPsi_of_half_lt hstrip))
  have hc := integrableOn_complex_laplace_of_convergesAt_re continuous_const
    (laplaceConvergesAt_const C hz)
  change IntegrableOn (fun t : ℝ => ((Real.exp (-σ * t) * suzukiPsi t : ℝ) : ℂ) *
    Complex.exp (-z * (t : ℂ))) (Ioi 0) at hd
  have hadd : complexLaplaceIntegral (suzukiDampedWithConstant σ C) z =
      complexLaplaceIntegral (fun t => Real.exp (-σ * t) * suzukiPsi t) z +
      complexLaplaceIntegral (fun _ => C) z := by
    unfold complexLaplaceIntegral
    rw [← integral_add hd hc]
    apply integral_congr_ae
    filter_upwards with t
    simp [suzukiDampedWithConstant, add_mul]
  rw [hadd, complexLaplaceIntegral_exp_damp, complexLaplaceIntegral_const C hz]
  have hfun : suzukiPsiShifted 0 = suzukiPsi := funext suzukiPsiShifted_zero_parameter
  have heq := complexLaplaceIntegral_suzukiPsiShifted_eq_continuation_of_re
    0 (w := z + (σ : ℂ)) (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
    (by simpa using hstrip)
  simpa only [hfun, suzukiDampedLaplaceContinuation] using congrArg
    (fun v => v + (C : ℂ) / z) heq

theorem meromorphic_suzukiDampedLaplaceContinuation (σ C : ℝ) :
    Meromorphic (suzukiDampedLaplaceContinuation σ C) := by
  intro z
  exact ((meromorphic_suzukiPsiShiftedLaplaceContinuation 0 (z + (σ : ℂ))).comp_analyticAt
    (g := fun w : ℂ => w + (σ : ℂ)) (by fun_prop)).add
    ((MeromorphicAt.const (C : ℂ) z).div (MeromorphicAt.id z))

theorem analyticAt_suzukiDampedLaplaceContinuation_pos {σ : ℝ} (hσ : 0 ≤ σ)
    (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    AnalyticAt ℂ (suzukiDampedLaplaceContinuation σ C) (τ : ℂ) := by
  have hbase := analyticAt_suzukiPsiShiftedLaplaceContinuation_of_pos 0
    (show 0 < τ + σ by linarith)
  have hbase' : AnalyticAt ℂ (suzukiPsiShiftedLaplaceContinuation 0)
      ((τ : ℂ) + (σ : ℂ)) := by simpa using hbase
  exact (hbase'.comp (f := fun w : ℂ => w + (σ : ℂ)) (by fun_prop)).add
    (analyticAt_const.div analyticAt_id (Complex.ofReal_ne_zero.mpr hτ.ne'))

/-- The genuine xi residue survives the added constant transform. -/
theorem suzukiDampedLaplaceContinuation_residue (σ C : ℝ) {ρ : ℂ}
    (hz : ρ - 1 / 2 - (σ : ℂ) ≠ 0) (hρ : ρ - 1 / 2 ≠ 0) :
    Tendsto (fun z : ℂ => (z - (ρ - 1 / 2 - (σ : ℂ))) *
      suzukiDampedLaplaceContinuation σ C z)
      (𝓝[≠] (ρ - 1 / 2 - (σ : ℂ)))
      (𝓝 ((xiMultiplicity ρ : ℂ) / (ρ - 1 / 2) ^ 2)) := by
  let z0 : ℂ := ρ - 1 / 2 - (σ : ℂ)
  let coord : ℂ → ℂ := fun z => 1 / 2 + (z + (σ : ℂ))
  have hcoordN : Tendsto coord (𝓝 z0) (𝓝 ρ) := by
    have hc : ContinuousAt coord z0 := by dsimp [coord]; fun_prop
    have he : coord z0 = ρ := by dsimp [coord, z0]; ring
    simpa only [he] using hc.tendsto
  have hcoord : Tendsto coord (𝓝[≠] z0) (𝓝[≠] ρ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordN.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hn
    simp only [mem_compl_iff, mem_singleton_iff] at hn ⊢
    intro he
    apply hn
    dsimp [coord] at he
    dsimp [z0]
    linear_combination he
  have hden : z0 + (σ : ℂ) ≠ 0 := by
    simpa [z0, sub_add_cancel] using hρ
  have hfac : ContinuousAt (fun z : ℂ => (z + (σ : ℂ)) ^ 2) z0 := by fun_prop
  have hcorr : ContinuousAt (fun z : ℂ => (C : ℂ) / z) z0 :=
    continuousAt_const.div continuousAt_id hz
  have hzero : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => z - z0) z0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (((tendsto_mul_logDeriv_riemannXi ρ).comp hcoord).div
    (hfac.tendsto.mono_left nhdsWithin_le_nhds) (pow_ne_zero 2 hden)).add
    (hzero.mul (hcorr.tendsto.mono_left nhdsWithin_le_nhds))
  have hlim' : Tendsto (fun z : ℂ =>
      ((coord z - ρ) * logDeriv riemannXi (coord z)) / (z + (σ : ℂ)) ^ 2 +
        (z - z0) * ((C : ℂ) / z)) (𝓝[≠] z0)
      (𝓝 ((xiMultiplicity ρ : ℂ) / (ρ - 1 / 2) ^ 2)) := by
    simpa only [Pi.div_apply, Function.comp_apply, z0, sub_add_cancel, zero_mul, add_zero] using hlim
  apply hlim'.congr'
  filter_upwards with z
  dsimp [coord, z0, suzukiDampedLaplaceContinuation, suzukiPsiShiftedLaplaceContinuation]
  push_cast
  simp only [add_zero]
  ring

/-- A one-sided lower bound on the ORIGINAL Suzuki function constrains
all xi zeros. The bound is not asserted unconditionally. -/
theorem xiZeroFreeRightOf_of_suzukiPsi_exp_lower {σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → -C * Real.exp (σ * t) ≤ suzukiPsi t) :
    XiZeroFreeRightOf σ := by
  obtain ⟨C, _, T, _, hbound⟩ := hbound
  have hsign : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ suzukiDampedWithConstant σ C t := by
    refine ⟨T, fun t ht => ?_⟩
    have hmul := mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_nonneg (-σ * t))
    have he : Real.exp (-σ * t) * Real.exp (σ * t) = 1 := by
      rw [← Real.exp_add]
      simp
    dsimp [suzukiDampedWithConstant]
    nlinarith [he]
  intro ρ hzero
  by_contra hn
  have hright : 1 / 2 + σ < ρ.re := lt_of_not_ge hn
  let z0 : ℂ := ρ - 1 / 2 - (σ : ℂ)
  have hzre : 0 < z0.re := by dsimp [z0]; simp only [div_ofNat_re, one_re]; linarith
  have hz : z0 ≠ 0 := by intro h; simp [h] at hzre
  have hρ : ρ - 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re, div_ofNat_re, one_re, zero_re] at hh
    linarith
  have horder := meromorphicOrderAt_nonneg_of_eventual_nonneg (by norm_num : (0 : ℝ) < 1)
    (continuous_suzukiDampedWithConstant σ C) hsign
    (meromorphic_suzukiDampedLaplaceContinuation σ C)
    (fun τ hτ => analyticAt_suzukiDampedLaplaceContinuation_pos hσ C hτ)
    (fun τ hτ => laplaceConvergesAt_suzukiDampedWithConstant σ C (by linarith) (by linarith))
    (fun z hz => complexLaplaceIntegral_suzukiDampedWithConstant σ C (by linarith) (by linarith))
    hzre
  obtain ⟨v, hv⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg
    (meromorphic_suzukiDampedLaplaceContinuation σ C z0) horder
  have hzeroLim : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => z - z0) z0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z => (z - z0) * suzukiDampedLaplaceContinuation σ C z)
      (𝓝[≠] z0) (𝓝 0) := by simpa using hzeroLim.mul hv
  have heq := tendsto_nhds_unique hprod (suzukiDampedLaplaceContinuation_residue σ C hz hρ)
  have hk : xiMultiplicity ρ ≠ 0 := by
    intro hk
    have hc := xiMultiplicity_cast ρ
    rw [hk] at hc
    exact ((xiDivisor_ne_zero_iff ρ).mpr hzero) (by simpa using hc.symm)
  exact (div_ne_zero (Nat.cast_ne_zero.mpr hk) (pow_ne_zero 2 hρ)) heq.symm

theorem xi_strip_of_suzukiPsi_exp_lower {σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → -C * Real.exp (σ * t) ≤ suzukiPsi t)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) : |ρ.re - 1 / 2| ≤ σ := by
  have h := xiZeroFreeRightOf_of_suzukiPsi_exp_lower hσ hbound
  have hr := h ρ hρ
  have hl := h (1 - ρ) (by rw [riemannXi_one_sub, hρ])
  simp only [sub_re, one_re] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem riemannHypothesis_iff_suzukiPsi_eventually_bounded_below :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → -C ≤ suzukiPsi t := by
  constructor
  · intro hRH
    refine ⟨0, le_rfl, 0, le_rfl, fun t _ => ?_⟩
    have hp := riemannHypothesis_iff_shifted_zero_nonnegative.mp hRH t
    simpa using hp
  · intro h
    apply riemannHypothesis_iff_xiZeroFreeRightOf_zero.mpr
    apply xiZeroFreeRightOf_of_suzukiPsi_exp_lower (by norm_num)
    simpa using h

theorem polynomial_le_exp_with_constant {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (N : ℕ) :
    (1 + t) ^ N ≤ ((N.factorial : ℝ) / σ ^ N * Real.exp σ) * Real.exp (σ * t) := by
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (σ * (1 + t)) (show 0 ≤ σ * (1 + t) by positivity) N)
  calc
    (1 + t) ^ N = (σ * (1 + t)) ^ N / σ ^ N := by
      rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero N hσ.ne')]
    _ ≤ (Real.exp (σ * (1 + t)) * (N.factorial : ℝ)) / σ ^ N :=
      div_le_div_of_nonneg_right h (pow_nonneg hσ.le N)
    _ = _ := by rw [show σ * (1 + t) = σ + σ * t by ring, Real.exp_add]; ring

/-- Any eventual polynomial lower bound for the original function is
already RH-strength. No such arithmetic lower bound is asserted here. -/
theorem riemannHypothesis_of_suzukiPsi_polynomial_lower {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hbound : ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → -C * (1 + t) ^ N ≤ suzukiPsi t) :
    RiemannHypothesis := by
  obtain ⟨T, hT, hbound⟩ := hbound
  have hstrip : ∀ σ : ℝ, 0 < σ → XiZeroFreeRightOf σ := by
    intro σ hσ
    apply xiZeroFreeRightOf_of_suzukiPsi_exp_lower hσ.le
    refine ⟨C * ((N.factorial : ℝ) / σ ^ N * Real.exp σ), by positivity,
      T, hT, fun t ht => ?_⟩
    have hp := mul_le_mul_of_nonneg_left
      (polynomial_le_exp_with_constant hσ (hT.trans ht) N) hC
    have hb := hbound t ht
    nlinarith
  apply riemannHypothesis_iff_xiZeroFreeRightOf_zero.mpr
  intro ρ hρ
  by_contra hn
  have hp : 0 < (ρ.re - 1 / 2) / 2 := by simp only [add_zero] at hn; linarith
  have hh := hstrip _ hp ρ hρ
  linarith

end RHGarden
