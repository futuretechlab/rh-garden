import RHGarden.LiHadamardInfinite
import Zeta23.RvM.ZetaGrowth

noncomputable section

open Complex

namespace RHGarden

/-- Euler's integral bounds complex Gamma by real Gamma in the right half-plane. -/
theorem norm_Complex_Gamma_le_Real_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral,
    Real.Gamma_eq_integral hz]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ =
    Real.exp (-x) * x ^ (z.re - 1)
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- A deliberately crude Euler-integral bound for real Gamma. -/
theorem Real.Gamma_le_one_add_ceil_pow {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ 1 + (Nat.ceil x : ℝ) ^ Nat.ceil x := by
  let n : ℕ := Nat.ceil x
  have hnpos : 0 < n := by
    rw [Nat.ceil_pos]
    linarith
  have hxn : x ≤ (n : ℝ) := by exact Nat.le_ceil x
  have hpoint : ∀ t : ℝ, 0 < t →
      t ^ (x - 1) ≤ 1 + t ^ ((n : ℝ) - 1) := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hx0 : 0 ≤ x - 1 := by linarith
      exact (Real.rpow_le_one ht.le ht1 hx0).trans (le_add_of_nonneg_right (by positivity))
    · have hone : 1 ≤ t := le_of_not_ge ht1
      have hexp : x - 1 ≤ (n : ℝ) - 1 := by linarith
      exact (Real.rpow_le_rpow_of_exponent_le hone hexp).trans
        (le_add_of_nonneg_left zero_le_one)
  rw [Real.Gamma_eq_integral (lt_of_lt_of_le zero_lt_one hx)]
  have hleft : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ (x - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent (lt_of_lt_of_le zero_lt_one hx)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hright : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * (1 + t ^ ((n : ℝ) - 1))) (Set.Ioi 0) := by
    rw [show (fun t : ℝ => Real.exp (-t) * (1 + t ^ ((n : ℝ) - 1))) =
      (fun t : ℝ => Real.exp (-t)) +
        (fun t : ℝ => Real.exp (-t) * t ^ ((n : ℝ) - 1)) by
          funext t
          simp only [Pi.add_apply]
          ring]
    exact (integrableOn_exp_neg_Ioi 0).add (Real.GammaIntegral_convergent hnreal)
  calc
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1))
        ≤ ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t) * (1 + t ^ ((n : ℝ) - 1)) := by
          apply MeasureTheory.setIntegral_mono_on hleft hright measurableSet_Ioi
          intro t ht
          exact mul_le_mul_of_nonneg_left (hpoint t ht) (Real.exp_pos _).le
    _ = 1 + Real.Gamma n := by
          simp_rw [mul_add]
          rw [MeasureTheory.integral_add]
          · rw [Real.Gamma_eq_integral hnreal]
            simp only [mul_one]
            rw [integral_exp_neg_Ioi_zero]
          · rw [show (fun t : ℝ => Real.exp (-t) * 1) =
              (fun t : ℝ => Real.exp (-t)) by funext t; simp]
            exact integrableOn_exp_neg_Ioi 0
          · exact Real.GammaIntegral_convergent hnreal
    _ ≤ 1 + (n : ℝ) ^ n := by
          have hGamma : Real.Gamma n = ((n - 1).factorial : ℕ) := by
            have hnsub : n - 1 + 1 = n :=
              Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
            calc
              Real.Gamma n = Real.Gamma ((n - 1 : ℕ) + 1) := by
                congr 1
                exact_mod_cast hnsub.symm
              _ = ((n - 1).factorial : ℕ) := Real.Gamma_nat_eq_factorial (n - 1)
          rw [hGamma]
          gcongr
          norm_cast
          exact (Nat.factorial_le_pow (n - 1)).trans
              ((Nat.pow_le_pow_left (Nat.sub_le n 1) (n - 1)).trans
                (Nat.pow_le_pow_right hnpos (Nat.sub_le n 1)))

/-- Gamma is bounded on the compact interval needed below. -/
theorem Real.exists_pos_Gamma_bound_Icc :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (1 / 4 : ℝ) 1, Real.Gamma x ≤ M := by
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1 / 4 : ℝ) 1) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx
      simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢
      linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_right _ _)

/-- The ceiling bound is absorbed by a coarse `exp (x log x)` majorant. -/
theorem Real.Gamma_coarse_exp_bound_large {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp (2 * (1 + x) * Real.log (2 + x)) := by
  let n : ℕ := Nat.ceil x
  have hnpos : 0 < n := by
    rw [Nat.ceil_pos]
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnx : (n : ℝ) ≤ x + 1 := by
    exact (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hbase : 1 ≤ x + 1 := by linarith
  have hpowbase : (n : ℝ) ^ n ≤ (x + 1) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hnx n
  have hpowexp : (x + 1) ^ (n : ℝ) ≤ (x + 1) ^ (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le hbase hnx
  have hnpow : (n : ℝ) ^ n ≤ Real.exp ((x + 1) * Real.log (x + 1)) := by
    calc
      (n : ℝ) ^ n ≤ (x + 1) ^ n := hpowbase
      _ = (x + 1) ^ (n : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (x + 1) ^ (x + 1) := hpowexp
      _ = Real.exp ((x + 1) * Real.log (x + 1)) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        ring_nf
  have hlog : Real.log (x + 1) ≤ Real.log (x + 2) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hlognonneg : 0 ≤ Real.log (x + 2) :=
    Real.log_nonneg (by linarith)
  have hA : 0 ≤ (x + 1) * Real.log (x + 2) :=
    mul_nonneg (by linarith) hlognonneg
  have hpow : (n : ℝ) ^ n ≤ Real.exp ((x + 1) * Real.log (x + 2)) :=
    hnpow.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by linarith)))
  have htwo : 2 ≤ Real.exp ((x + 1) * Real.log (x + 2)) := by
    have hlog2 : Real.log 2 ≤ Real.log (x + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2pos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((x + 1) * Real.log (x + 2)) := Real.exp_le_exp.mpr <| by
        calc
          Real.log 2 ≤ (x + 1) * Real.log 2 := by nlinarith
          _ ≤ (x + 1) * Real.log (x + 2) :=
            mul_le_mul_of_nonneg_left hlog2 (by linarith)
  calc
    Real.Gamma x ≤ 1 + (n : ℝ) ^ n := Real.Gamma_le_one_add_ceil_pow hx
    _ ≤ 2 * Real.exp ((x + 1) * Real.log (x + 2)) := by nlinarith
    _ ≤ Real.exp (2 * (x + 1) * Real.log (x + 2)) := by
      rw [show 2 * (x + 1) * Real.log (x + 2) =
        (x + 1) * Real.log (x + 2) + (x + 1) * Real.log (x + 2) by ring,
        Real.exp_add]
      nlinarith [Real.exp_pos ((x + 1) * Real.log (x + 2))]
    _ = Real.exp (2 * (1 + x) * Real.log (2 + x)) := by ring_nf

/-- A global positive-half-line Gamma bound, with no Stirling asymptotics. -/
theorem Real.Gamma_coarse_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 / 4 ≤ x →
      Real.Gamma x ≤ Real.exp (C * (1 + x) * Real.log (2 + x)) := by
  obtain ⟨M, hMpos, hM⟩ := Real.exists_pos_Gamma_bound_Icc
  let C : ℝ := max 2 (2 * M)
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogmono : Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2 + x) :=
    (Real.log_nonneg (by linarith))
  have hFnonneg : 0 ≤ (1 + x) * Real.log (2 + x) :=
    mul_nonneg (by linarith) hlognonneg
  by_cases hx1 : x ≤ 1
  · have hsmall := hM x ⟨hx, hx1⟩
    have hFhalf : (1 / 2 : ℝ) ≤ (1 + x) * Real.log (2 + x) := by
      have hloghalf : (1 / 2 : ℝ) ≤ Real.log (2 + x) := hlog2.trans hlogmono
      nlinarith
    have hMC : M ≤ C * ((1 + x) * Real.log (2 + x)) := by
      have hC : 2 * M ≤ C := le_max_right _ _
      nlinarith
    have hMexp : M ≤ Real.exp M := by
      linarith [Real.add_one_le_exp M]
    exact hsmall.trans <| hMexp.trans <| Real.exp_le_exp.mpr (by
      simpa [mul_assoc] using hMC)
  · have hxlarge : 1 ≤ x := le_of_not_ge hx1
    refine (Real.Gamma_coarse_exp_bound_large hxlarge).trans (Real.exp_le_exp.mpr ?_)
    have hC : 2 ≤ C := le_max_left _ _
    nlinarith

/-- Coarse global growth of the real Gamma factor used in the completed zeta
function. The factor `π^(-s/2)` has norm at most one in this half-plane. -/
theorem norm_GammaR_coarse :
    ∃ CΓ : ℝ, 0 < CΓ ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖Complex.Gammaℝ s‖ ≤
        Real.exp (CΓ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨CΓ, hCΓ, hGamma⟩ := Real.Gamma_coarse_exp_bound
  refine ⟨CΓ, hCΓ, ?_⟩
  intro s hs
  have hsre0 : 0 ≤ s.re := by linarith
  have hsdiv : (s / 2).re = s.re / 2 := by norm_num [div_re]
  have hhalf : (1 / 4 : ℝ) ≤ (s / 2).re := by
    rw [hsdiv]
    linarith
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpiexp : 0 ≥ (-s / 2).re := by
    norm_num [div_re]
    linarith
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hpi1 hpiexp
  have hcomplexGamma : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s / 2).re :=
    norm_Complex_Gamma_le_Real_Gamma_re (lt_of_lt_of_le (by norm_num) hhalf)
  have hrealGamma := hGamma (s / 2).re hhalf
  have hre_norm : (s / 2).re ≤ ‖s‖ := by
    have hre := Complex.re_le_norm s
    rw [hsdiv]
    linarith
  have hlog : Real.log (2 + (s / 2).re) ≤ Real.log (2 + ‖s‖) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2 + ‖s‖) :=
    Real.log_nonneg (by linarith [norm_nonneg s])
  have hfactor :
      (1 + (s / 2).re) * Real.log (2 + (s / 2).re) ≤
        (1 + ‖s‖) * Real.log (2 + ‖s‖) := by
    calc
      (1 + (s / 2).re) * Real.log (2 + (s / 2).re)
          ≤ (1 + (s / 2).re) * Real.log (2 + ‖s‖) :=
            mul_le_mul_of_nonneg_left hlog (by linarith)
      _ ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) :=
            mul_le_mul_of_nonneg_right (by linarith) hlognonneg
  rw [Complex.Gammaℝ_def, norm_mul]
  calc
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * Real.Gamma (s / 2).re :=
          mul_le_mul hpi hcomplexGamma (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (CΓ * (1 + (s / 2).re) * Real.log (2 + (s / 2).re)) := by
          simpa using hrealGamma
    _ ≤ Real.exp (CΓ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) :=
          Real.exp_le_exp.mpr <| by nlinarith [hfactor]

/-- On the right half-plane, the explicit pole term in the zeta estimate is
cancelled by xi's factor `s - 1`. -/
theorem norm_riemannXi_le_poly_mul_Gammaℝ {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖riemannXi s‖ ≤ 3 * (1 + ‖s‖) ^ 3 * ‖Complex.Gammaℝ s‖ := by
  by_cases hs1 : s = 1
  · subst s
    simp [riemannXi_one, Complex.Gammaℝ_one]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsre : 0 < s.re := by linarith
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hcompleted : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp
  have hzeta := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hsre hs1
  have hre_inv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    have hsre0 : 0 < s.re := hsre
    apply (div_le_iff₀ hsre0).2
    nlinarith [norm_nonneg s]
  have hzeta' : ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + 2 * ‖s‖ :=
    hzeta.trans (by linarith)
  have hdpos : 0 < ‖1 - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs1))
  have hd : ‖1 - s‖ ≤ 1 + ‖s‖ := by
    calc
      ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by norm_num
  have hdzeta :
      ‖1 - s‖ * ‖riemannZeta s‖ ≤
        ‖1 - s‖ / 2 + 1 + 2 * ‖s‖ * ‖1 - s‖ := by
    calc
      ‖1 - s‖ * ‖riemannZeta s‖
          ≤ ‖1 - s‖ * (1 / 2 + 1 / ‖1 - s‖ + 2 * ‖s‖) :=
            mul_le_mul_of_nonneg_left hzeta' (norm_nonneg _)
      _ = ‖1 - s‖ / 2 + 1 + 2 * ‖s‖ * ‖1 - s‖ := by
            field_simp [ne_of_gt hdpos]
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1,
    hcompleted]
  simp only [norm_mul, norm_div, norm_ofNat, norm_one]
  rw [norm_sub_rev] at hdzeta
  have hr := norm_nonneg s
  have hpoly :
      (1 / 2 : ℝ) * ‖s‖ *
          (‖s - 1‖ / 2 + 1 + 2 * ‖s‖ * ‖s - 1‖) ≤
        3 * (1 + ‖s‖) ^ 3 := by
    rw [norm_sub_rev]
    nlinarith [sq_nonneg ‖s‖, sq_nonneg (1 + ‖s‖)]
  calc
    1 / 2 * ‖s‖ * ‖s - 1‖ * (‖Complex.Gammaℝ s‖ * ‖riemannZeta s‖)
        = ((1 / 2) * ‖s‖ * (‖s - 1‖ * ‖riemannZeta s‖)) *
            ‖Complex.Gammaℝ s‖ := by ring
    _ ≤ ((1 / 2) * ‖s‖ *
          (‖s - 1‖ / 2 + 1 + 2 * ‖s‖ * ‖s - 1‖)) *
            ‖Complex.Gammaℝ s‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdzeta (by positivity)) (norm_nonneg _)
    _ ≤ (3 * (1 + ‖s‖) ^ 3) * ‖Complex.Gammaℝ s‖ :=
      mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)

/-- Coarse xi growth in the half-plane `Re s ≥ 1/2`. -/
theorem riemannXi_coarse_growth_right :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖riemannXi s‖ ≤
        Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨CΓ, hCΓ, hG⟩ := norm_GammaR_coarse
  refine ⟨CΓ + 5, by linarith, ?_⟩
  intro s hs
  let r : ℝ := ‖s‖
  let F : ℝ := (1 + r) * Real.log (2 + r)
  have hr : 0 ≤ r := norm_nonneg s
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hF : 0 ≤ F := mul_nonneg (by linarith) hlog
  have hthree : 3 ≤ (2 + r) ^ 2 := by nlinarith [sq_nonneg r]
  have hpow : (1 + r) ^ 3 ≤ (2 + r) ^ 3 := by
    gcongr
    linarith
  have hpoly_alg : 3 * (1 + r) ^ 3 ≤ (2 + r) ^ 5 := by
    calc
      3 * (1 + r) ^ 3 ≤ (2 + r) ^ 2 * (2 + r) ^ 3 :=
        mul_le_mul hthree hpow (by positivity) (by positivity)
      _ = (2 + r) ^ 5 := by ring
  have hlog_le_F : Real.log (2 + r) ≤ F := by
    dsimp [F]
    nlinarith
  have hpoly_exp : 3 * (1 + r) ^ 3 ≤ Real.exp (5 * F) := by
    refine hpoly_alg.trans ((Real.log_le_iff_le_exp (pow_pos (by linarith) 5)).mp ?_)
    rw [Real.log_pow]
    norm_num
    exact hlog_le_F
  have hGamma := hG s hs
  have hxi := norm_riemannXi_le_poly_mul_Gammaℝ hs
  rw [show (CΓ + 5) * (1 + ‖s‖) * Real.log (2 + ‖s‖) =
    (CΓ + 5) * F by simp [F, r, mul_assoc]]
  calc
    ‖riemannXi s‖ ≤ 3 * (1 + r) ^ 3 * ‖Complex.Gammaℝ s‖ := by
      simpa [r] using hxi
    _ ≤ Real.exp (5 * F) * Real.exp (CΓ * F) :=
      mul_le_mul hpoly_exp (by simpa [r, F, mul_assoc] using hGamma)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((CΓ + 5) * F) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The functional equation reflects the right-half-plane estimate to all of ℂ. -/
theorem riemannXi_coarse_growth_global :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖riemannXi s‖ ≤
        Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hright⟩ := riemannXi_coarse_growth_right
  refine ⟨4 * C, by positivity, ?_⟩
  intro s
  have hr : 0 ≤ ‖s‖ := norm_nonneg s
  have hlog : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  by_cases hs : 1 / 2 ≤ s.re
  · refine (hright s hs).trans (Real.exp_le_exp.mpr ?_)
    have hF : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) :=
      mul_nonneg (by linarith) hlog
    nlinarith
  · let t : ℂ := 1 - s
    have ht : 1 / 2 ≤ t.re := by
      dsimp [t]
      linarith
    have htnorm : ‖t‖ ≤ 1 + ‖s‖ := by
      dsimp [t]
      calc
        ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by norm_num
    have hlogt : Real.log (2 + ‖t‖) ≤ 2 * Real.log (2 + ‖s‖) := by
      have hbasepos : 0 < 2 + ‖s‖ := by positivity
      have harg : 2 + ‖t‖ ≤ (2 + ‖s‖) ^ 2 := by
        calc
          2 + ‖t‖ ≤ 3 + ‖s‖ := by linarith
          _ ≤ (2 + ‖s‖) ^ 2 := by nlinarith [sq_nonneg ‖s‖]
      calc
        Real.log (2 + ‖t‖) ≤ Real.log ((2 + ‖s‖) ^ 2) :=
          Real.log_le_log (by positivity) harg
        _ = 2 * Real.log (2 + ‖s‖) := by rw [Real.log_pow]; norm_num
    have hfactor :
        (1 + ‖t‖) * Real.log (2 + ‖t‖) ≤
          4 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      have hlogt0 : 0 ≤ Real.log (2 + ‖t‖) :=
        Real.log_nonneg (by linarith [norm_nonneg t])
      calc
        (1 + ‖t‖) * Real.log (2 + ‖t‖)
            ≤ (2 * (1 + ‖s‖)) * Real.log (2 + ‖t‖) := by
              apply mul_le_mul_of_nonneg_right _ hlogt0
              linarith
        _ ≤ (2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖)) :=
              mul_le_mul_of_nonneg_left hlogt (by positivity)
        _ = 4 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by ring
    have htbound := hright t ht
    rw [riemannXi_one_sub s] at htbound
    refine htbound.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [hfactor]

/-- The logarithmic factor is bounded by a square root, uniformly on the
nonnegative real axis. -/
theorem one_add_mul_log_le_four_rpow_three_halves {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) * Real.log (2 + r) ≤ 4 * (1 + r) ^ (3 / 2 : ℝ) := by
  have hlog := Real.log_le_rpow_div (show 0 ≤ 2 + r by linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hbase : 2 + r ≤ 4 * (1 + r) := by linarith
  have hroot : (2 + r) ^ (1 / 2 : ℝ) ≤ 2 * (1 + r) ^ (1 / 2 : ℝ) := by
    calc
      (2 + r) ^ (1 / 2 : ℝ) ≤ (4 * (1 + r)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hbase (by norm_num)
      _ = 4 ^ (1 / 2 : ℝ) * (1 + r) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
      _ = 2 * (1 + r) ^ (1 / 2 : ℝ) := by norm_num
  have hlog' : Real.log (2 + r) ≤ 4 * (1 + r) ^ (1 / 2 : ℝ) := by
    calc
      Real.log (2 + r) ≤ (2 + r) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
      _ = 2 * (2 + r) ^ (1 / 2 : ℝ) := by ring
      _ ≤ 4 * (1 + r) ^ (1 / 2 : ℝ) := by linarith
  calc
    (1 + r) * Real.log (2 + r)
        ≤ (1 + r) * (4 * (1 + r) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog' (by linarith)
    _ = 4 * (1 + r) ^ (3 / 2 : ℝ) := by
      calc
        (1 + r) * (4 * (1 + r) ^ (1 / 2 : ℝ)) =
            4 * ((1 + r) ^ (1 : ℝ) * (1 + r) ^ (1 / 2 : ℝ)) := by
              rw [Real.rpow_one]
              ring
        _ = 4 * (1 + r) ^ ((1 : ℝ) + 1 / 2) := by
              rw [Real.rpow_add (by positivity)]
        _ = 4 * (1 + r) ^ (3 / 2 : ℝ) := by norm_num

/-- A fixed order strictly between one and two. Any such order makes the
Hadamard polynomial affine; `3 / 2` is a convenient concrete choice. -/
def xiGrowthOrder : ℝ := 3 / 2

theorem one_le_xiGrowthOrder : 1 ≤ xiGrowthOrder := by
  norm_num [xiGrowthOrder]

theorem xiGrowthOrder_lt_two : xiGrowthOrder < 2 := by
  norm_num [xiGrowthOrder]

theorem floor_xiGrowthOrder : Nat.floor xiGrowthOrder = 1 := by
  apply (Nat.floor_eq_iff (by norm_num [xiGrowthOrder] : 0 ≤ xiGrowthOrder)).2
  constructor <;> norm_num [xiGrowthOrder]

/-- The coarse global growth estimate needed from the analytic theory of the
completed zeta function. The exponent `3 / 2 + ε` is deliberately weaker than
the classical order-one estimate. Since `⌊3 / 2⌋ = 1`, it is still sufficient
to force the polynomial in Hadamard factorization to be affine. -/
def XiSubquadraticGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))

/-- The proved coarse global estimate has order at most `3/2`, hence satisfies
the subquadratic growth interface. -/
theorem riemannXi_subquadratic_growth : XiSubquadraticGrowth := by
  obtain ⟨C, hC, hglobal⟩ := riemannXi_coarse_growth_global
  intro ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro z
  let r : ℝ := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have hlog := one_add_mul_log_le_four_rpow_three_halves hr
  have hpow : (1 + r) ^ (3 / 2 : ℝ) ≤
      (1 + r) ^ ((3 / 2 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hexponent :
      C * ((1 + r) * Real.log (2 + r)) ≤
        (4 * C) * (1 + r) ^ ((3 / 2 : ℝ) + ε) := by
    have hC0 : 0 ≤ C := hC.le
    nlinarith [mul_le_mul_of_nonneg_left hlog hC0,
      mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 * C by positivity)]
  have hexponent' :
      C * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤
        (4 * C) * (1 + ‖z‖) ^ ((3 / 2 : ℝ) + ε) := by
    simpa [r, mul_assoc] using hexponent
  exact (hglobal z).trans (Real.exp_le_exp.mpr hexponent')

/-- The general quotient-polynomial principle still needed after constructing
RH Garden's intrinsic canonical product. It is deliberately stated for an
arbitrary zero-free entire function and is therefore not a disguised xi
factorization assumption. -/
def SubquadraticZeroFreeEntireIsExpAffine : Prop :=
  ∀ H : ℂ → ℂ,
    Differentiable ℂ H →
    (∀ z : ℂ, H z ≠ 0) →
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))) →
    ∃ A B : ℂ, ∀ z : ℂ, H z = Complex.exp (A + B * z)

/-- Opposite centered zeros cancel the exponential corrections in the two
genus-one primary factors. No assertion that `α` is a zero is needed. -/
theorem primaryFactorOne_mul_primaryFactorOne_neg (w α : ℂ) :
    primaryFactorOne (w / α) * primaryFactorOne (w / (-α)) =
      1 - (w / α) ^ 2 := by
  have hneg : w / (-α) = -(w / α) := by ring
  rw [hneg]
  simp only [primaryFactorOne]
  rw [show
    (1 - w / α) * Complex.exp (w / α) *
        ((1 - -(w / α)) * Complex.exp (-(w / α))) =
      ((1 - w / α) * (1 - -(w / α))) *
        (Complex.exp (w / α) * Complex.exp (-(w / α))) by ring]
  rw [← Complex.exp_add]
  simp
  ring

end RHGarden
