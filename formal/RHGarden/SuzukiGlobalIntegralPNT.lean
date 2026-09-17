import RHGarden.SuzukiTwoScale
import RHGarden.SuzukiThetaPNT

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Uniform fixed-relative-width control from the pinned global PNT. This gives
neither an effective threshold nor control at the moving width m^(2/3). -/
noncomputable section
open Set Filter
open scoped Topology
namespace RHGarden

theorem anchoredError_le_global_error {m : ℕ} {x delta : ℝ}
    (hmx : (m : ℝ) ≤ x)
    (hb : ∀ y ∈ Icc (m : ℝ) x, |suzukiChebyshevPsi y - y| ≤ delta * y) :
    ∀ y ∈ Icc (m : ℝ) x, suzukiAnchoredError m y ≤ delta * (y - m) + 2 * delta * m := by
  intro y hy
  have ha := abs_le.mp (hb m ⟨le_rfl, hmx⟩)
  have hc := abs_le.mp (hb y hy)
  unfold suzukiAnchoredError
  linarith

theorem integratedMainTerm_lower_relative {m : ℕ} {h : ℝ}
    (hm : 1 ≤ m) (hh : 0 ≤ h) (hhm : h ≤ (m : ℝ) / 8) :
    h ^ 2 / (3 * (m : ℝ) * Real.sqrt m) ≤ suzukiIntegratedMainTerm m (m + h) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 < (m : ℝ) + h := by linarith
  have hs : Real.sqrt (m + h) ≤ (9 / 8 : ℝ) * Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm0.le, Real.sq_sqrt hx0.le, Real.sqrt_nonneg (m + h), Real.sqrt_nonneg m]
  have hp := mul_le_mul (show (m : ℝ) + h ≤ 9 / 8 * m by linarith) hs
    (Real.sqrt_nonneg (m + h)) (by positivity : (0 : ℝ) ≤ 9 / 8 * m)
  apply le_trans _ (integratedMainTerm_lower hm hh)
  apply div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
  nlinarith [mul_pos hm0 (Real.sqrt_pos.mpr hm0)]

/-- A finite global-error input, with both anchored endpoint errors retained. -/
theorem anchoredIntegral_le_global_relative {m : ℕ} {h rho delta : ℝ}
    (hm : 1 ≤ m) (hr : 0 < rho) (hh : rho * m ≤ h) (hhm : h ≤ (m : ℝ) / 8)
    (hd : 0 ≤ delta)
    (hb : ∀ y ∈ Icc (m : ℝ) (m + h), |suzukiChebyshevPsi y - y| ≤ delta * y) :
    suzukiAnchoredIntegral m (m + h) ≤
      delta * (1 + 6 / rho) * suzukiIntegratedMainTerm m (m + h) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hh0 : 0 < h := (mul_pos hr hm0).trans_le hh
  have hs0 := Real.sqrt_pos.mpr hm0
  have hC := integratedMainTerm_lower_relative hm hh0.le hhm
  have hC0 := integratedMainTerm_pos hm hh0
  have hb' := anchoredIntegral_le_accuracy_budget hm (by linarith : (m : ℝ) ≤ m + h)
    hd (by positivity : 0 ≤ 2 * delta * (m : ℝ))
    (anchoredError_le_global_error (by linarith) hb)
  have hl := log_one_add_width_le hm hh0.le
  have hburst : (2 * delta * (m : ℝ)) / Real.sqrt m * Real.log (((m : ℝ) + h) / m) ≤
      2 * delta * h / Real.sqrt m := by
    calc
      _ ≤ (2 * delta * (m : ℝ)) / Real.sqrt m * (h / m) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  have hCl : h ^ 2 ≤ 3 * (m : ℝ) * Real.sqrt m * suzukiIntegratedMainTerm m (m + h) := by
    have := (div_le_iff₀ (by positivity : 0 < 3 * (m : ℝ) * Real.sqrt m)).mp hC
    nlinarith
  have hCh : rho * h ≤ 3 * Real.sqrt m * suzukiIntegratedMainTerm m (m + h) := by
    have hmul := mul_le_mul_of_nonneg_right hh hh0.le
    have haux : (m : ℝ) * (rho * h) ≤ m * (3 * Real.sqrt m * suzukiIntegratedMainTerm m (m + h)) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hm0).mp haux
  have hcomp : 2 * h / Real.sqrt m ≤ 6 / rho * suzukiIntegratedMainTerm m (m + h) := by
    apply (div_le_iff₀ hs0).mpr
    apply (mul_le_mul_iff_right₀ hr).mp
    field_simp
    nlinarith
  have hdcomp := mul_le_mul_of_nonneg_left hcomp hd
  calc
    _ ≤ delta * suzukiIntegratedMainTerm m (m + h) + 2 * delta * h / Real.sqrt m :=
      hb'.trans (add_le_add le_rfl hburst)
    _ = delta * suzukiIntegratedMainTerm m (m + h) + delta * (2 * h / Real.sqrt m) := by ring
    _ ≤ delta * suzukiIntegratedMainTerm m (m + h) +
        delta * (6 / rho * suzukiIntegratedMainTerm m (m + h)) := add_le_add le_rfl hdcomp
    _ = _ := by ring

theorem eventually_psi_relative_bound {delta : ℝ} (hd : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, |suzukiChebyshevPsi x - x| ≤ delta * x := by
  have h := (Metric.tendsto_nhds.mp tendsto_psi_relative_error) delta hd
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : |Chebyshev.psi x - x| / x < delta := by
    simpa [Real.dist_eq, abs_mul, abs_inv, abs_of_pos hx0, div_eq_mul_inv] using hx
  exact ((div_lt_iff₀ hx0).mp he).le

/-- Unconditional, uniform in h on a fixed relative range, but non-effective. -/
theorem anchoredIntegral_eventually_le_relative_main {rho eta : ℝ}
    (hr : 0 < rho) (_hr8 : rho ≤ 1 / 8) (he : 0 < eta) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ h : ℝ, rho * m ≤ h → h ≤ (m : ℝ) / 8 →
      suzukiAnchoredIntegral m (m + h) ≤ eta * suzukiIntegratedMainTerm m (m + h) := by
  let delta := eta / (1 + 6 / rho)
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨X, hX⟩ := eventually_atTop.mp (eventually_psi_relative_bound hd)
  have hm : ∀ᶠ m : ℕ in atTop, X ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X)
  have hall : ∀ᶠ m : ℕ in atTop, ∀ h : ℝ, rho * m ≤ h → h ≤ (m : ℝ) / 8 →
      suzukiAnchoredIntegral m (m + h) ≤ eta * suzukiIntegratedMainTerm m (m + h) := by
    filter_upwards [hm, eventually_ge_atTop (1 : ℕ)] with m hm hm1 h hhl hhu
    have hb := anchoredIntegral_le_global_relative hm1 hr hhl hhu hd.le
      (fun y hy => hX y (hm.trans hy.1))
    have heq : delta * (1 + 6 / rho) = eta := by
      dsimp [delta]
      exact div_mul_cancel₀ eta (by positivity)
    rwa [heq] at hb
  exact eventually_atTop.mp hall

end RHGarden
