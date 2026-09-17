import RHGarden.SuzukiSurchargeSplit
import RHGarden.SuzukiSurchargeLogProfile

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite quantitative calibration of the entire surcharge profile.
Only the stated finite theta-error bound is an arithmetic input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace RHGarden

theorem sqrt_log_window {m : ℕ} (hm : 1 ≤ m) (s : ℝ) :
    Real.log (Real.sqrt ((m : ℝ) * Real.exp s) / Real.sqrt m) = s / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.log_div (Real.sqrt_pos.mpr (by positivity)).ne'
      (Real.sqrt_pos.mpr hm0).ne', Real.log_sqrt (by positivity),
    Real.log_sqrt hm0.le, Real.log_mul hm0.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem sqrt_log_window_mono {m : ℕ} {s S : ℝ} (hsS : s ≤ S) :
    Real.sqrt ((m : ℝ) * Real.exp s) ≤ Real.sqrt ((m : ℝ) * Real.exp S) :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsS) (Nat.cast_nonneg m))

theorem sqrt_anchor_le_log_window {m : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt m ≤ Real.sqrt ((m : ℝ) * Real.exp s) := by
  simpa using (sqrt_log_window_mono (m := m) hs)

theorem primeSquare_log_window_error {m : ℕ} {s S epsilon : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) (hsS : s ≤ S) (hepsilon : 0 ≤ epsilon)
    (htheta : ∀ x ∈ Icc (Real.sqrt m) (Real.sqrt ((m : ℝ) * Real.exp S)),
      |Chebyshev.theta x - x| ≤ epsilon * x) :
    |suzukiPrimeReciprocalWindow (Real.sqrt m) (Real.sqrt ((m : ℝ) * Real.exp s)) - s / 2| ≤
      epsilon * (2 + s / 2) := by
  have h := primeReciprocalWindow_error (Real.sqrt_pos.mpr (by exact_mod_cast hm))
    (sqrt_anchor_le_log_window hs) hepsilon (fun x hx =>
      htheta x ⟨hx.1, hx.2.trans (sqrt_log_window_mono hsS)⟩)
  rwa [sqrt_log_window hm] at h

/-- Finite Delta estimate, including both theta endpoint errors and the entire higher-power tail. -/
theorem primePowerDelta_log_window_error {m : ℕ} {s S epsilon : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) (hsS : s ≤ S) (hepsilon : 0 ≤ epsilon)
    (htheta : ∀ x ∈ Icc (Real.sqrt m) (Real.sqrt ((m : ℝ) * Real.exp S)),
      |Chebyshev.theta x - x| ≤ epsilon * x) :
    |suzukiPrimePowerDelta m ((m : ℝ) * Real.exp s) - s / 2| ≤
      epsilon * (2 + s / 2) + suzukiHigherPowerTail m := by
  rw [primePowerDelta_eq_square_add_higher m (by positivity), add_sub_right_comm]
  exact (abs_add_le _ _).trans (add_le_add
    (primeSquare_log_window_error hm hs hsS hepsilon htheta)
    (by rw [abs_of_nonneg (higherPowerWindow_nonneg _ _)]; exact higherPowerWindow_le_tail _ _))

/-- Integration of a linear pointwise error envelope; no integrability premise is hidden here. -/
theorem integral_surcharge_error_envelope (epsilon H s : ℝ) :
    (∫ r in 0..s, epsilon * (2 + r / 2) + H) =
      epsilon * (2 * s + s ^ 2 / 4) + s * H := by
  have he : (fun r : ℝ => epsilon * (2 + r / 2) + H) =
      (fun r : ℝ => (2 * epsilon + H) + (epsilon / 2) * r) := by
    funext r
    ring
  have hi : IntervalIntegrable (fun r : ℝ => (epsilon / 2) * r) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

/-- The finite J estimate is obtained by integrating the Delta estimate once. -/
theorem primePowerSurcharge_log_window_error {m : ℕ} {s S epsilon : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) (hsS : s ≤ S) (hepsilon : 0 ≤ epsilon)
    (htheta : ∀ x ∈ Icc (Real.sqrt m) (Real.sqrt ((m : ℝ) * Real.exp S)),
      |Chebyshev.theta x - x| ≤ epsilon * x) :
    |suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) - s ^ 2 / 4| ≤
      epsilon * (2 * s + s ^ 2 / 4) + s * suzukiHigherPowerTail m := by
  have hi := intervalIntegrable_logEventProfile m hm suzukiPrimePowerOvercharge hs
  change IntervalIntegrable (fun r => suzukiPrimePowerDelta m ((m : ℝ) * Real.exp r)) volume 0 s at hi
  have hlin : IntervalIntegrable (fun r : ℝ => r / 2) volume 0 s :=
    (continuous_id.intervalIntegrable 0 s).div_const 2
  have he : (∫ r in 0..s, suzukiPrimePowerDelta m ((m : ℝ) * Real.exp r) - r / 2) =
      suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) - s ^ 2 / 4 := by
    rw [intervalIntegral.integral_sub hi hlin, ← primePowerSurcharge_eq_integral_logDelta hm hs,
      intervalIntegral.integral_div, integral_id]
    ring
  rw [← he]
  calc
    _ ≤ ∫ r in 0..s, |suzukiPrimePowerDelta m ((m : ℝ) * Real.exp r) - r / 2| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun r => suzukiPrimePowerDelta m ((m : ℝ) * Real.exp r) - r / 2) hs
    _ ≤ ∫ r in 0..s, epsilon * (2 + r / 2) + suzukiHigherPowerTail m := by
      apply intervalIntegral.integral_mono_on hs (hi.sub hlin).abs
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro r hr
      exact primePowerDelta_log_window_error hm hr.1 (hr.2.trans hsS) hepsilon htheta
    _ = _ := integral_surcharge_error_envelope _ _ _

end RHGarden
