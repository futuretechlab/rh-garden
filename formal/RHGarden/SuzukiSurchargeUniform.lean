import RHGarden.SuzukiSurchargeQuantitative
import RHGarden.SuzukiThetaPNT

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Unconditional uniform absolute convergence on bounded logarithmic windows.
These theorems calibrate an artificial overcharge, not the true Suzuki reserve. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RHGarden

theorem eventually_uniform_primePowerDelta_log_window {S delta : ℝ}
    (hS : 0 ≤ S) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Icc 0 S,
      |suzukiPrimePowerDelta m ((m : ℝ) * Real.exp s) - s / 2| < delta := by
  let epsilon := delta / (4 + S)
  have he : 0 < epsilon := div_pos hdelta (by linarith)
  have ht := eventually_theta_log_window_bound S he
  have hH : ∀ᶠ m : ℕ in atTop, suzukiHigherPowerTail m < delta / 2 :=
    tendsto_suzukiHigherPowerTail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < delta / 2))
  filter_upwards [ht, hH, eventually_ge_atTop (1 : ℕ)] with m hm htail hm1 s hs
  calc
    _ ≤ epsilon * (2 + s / 2) + suzukiHigherPowerTail m :=
      primePowerDelta_log_window_error hm1 hs.1 hs.2 he.le hm
    _ ≤ epsilon * (2 + S / 2) + suzukiHigherPowerTail m := by gcongr; exact hs.2
    _ = delta / 2 + suzukiHigherPowerTail m := by
      congr 1
      dsimp [epsilon]
      field_simp
      ring
    _ < delta := by linarith

theorem uniform_primePowerDelta_log_window {S delta : ℝ}
    (hS : 0 ≤ S) (hdelta : 0 < delta) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s ∈ Icc 0 S,
      |suzukiPrimePowerDelta m ((m : ℝ) * Real.exp s) - s / 2| < delta :=
  eventually_atTop.mp (eventually_uniform_primePowerDelta_log_window hS hdelta)

theorem eventually_uniform_primePowerSurcharge_log_window {S delta : ℝ}
    (hS : 0 ≤ S) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Icc 0 S,
      |suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) - s ^ 2 / 4| < delta := by
  let C := 2 * S + S ^ 2 / 4
  let epsilon := delta / (2 * (C + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 0 < epsilon := div_pos hdelta (by positivity)
  have hS1 : 0 < S + 1 := by positivity
  have ht := eventually_theta_log_window_bound S he
  have hH : ∀ᶠ m : ℕ in atTop, suzukiHigherPowerTail m < delta / (2 * (S + 1)) :=
    tendsto_suzukiHigherPowerTail.eventually (gt_mem_nhds (by positivity))
  filter_upwards [ht, hH, eventually_ge_atTop (1 : ℕ)] with m hm htail hm1 s hs
  have hcoef : 2 * s + s ^ 2 / 4 ≤ C + 1 := by
    have hsq := pow_le_pow_left₀ hs.1 hs.2 2
    dsimp [C]
    nlinarith
  have hbudget : epsilon * (C + 1) = delta / 2 := by
    dsimp [epsilon]
    field_simp
  have htailbudget : (S + 1) * (delta / (2 * (S + 1))) = delta / 2 := by
    field_simp
  calc
    _ ≤ epsilon * (2 * s + s ^ 2 / 4) + s * suzukiHigherPowerTail m :=
      primePowerSurcharge_log_window_error hm1 hs.1 hs.2 he.le hm
    _ ≤ epsilon * (C + 1) + (S + 1) * suzukiHigherPowerTail m :=
      add_le_add (mul_le_mul_of_nonneg_left hcoef he.le)
        (mul_le_mul_of_nonneg_right (by linarith [hs.2]) (suzukiHigherPowerTail_nonneg m))
    _ < delta / 2 + (S + 1) * (delta / (2 * (S + 1))) := by
      rw [hbudget]
      linarith [mul_lt_mul_of_pos_left htail hS1]
    _ = delta := by rw [htailbudget]; ring

/-- The entire surcharge profile converges uniformly on every bounded nonnegative log window. -/
theorem uniform_primePowerSurcharge_log_window {S delta : ℝ}
    (hS : 0 ≤ S) (hdelta : 0 < delta) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ s ∈ Icc 0 S,
      |suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) - s ^ 2 / 4| < delta :=
  eventually_atTop.mp (eventually_uniform_primePowerSurcharge_log_window hS hdelta)

theorem tendsto_primePowerDelta_fixed_ratio {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (fun m : ℕ => suzukiPrimePowerDelta m (lam * m))
      atTop (𝓝 (Real.log lam / 2)) := by
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have h := eventually_uniform_primePowerDelta_log_window (Real.log_nonneg hlam.le) hdelta
  filter_upwards [h] with m hm
  simpa [Real.dist_eq, Real.exp_log (by linarith : 0 < lam), mul_comm]
    using hm (Real.log lam) ⟨Real.log_nonneg hlam.le, le_rfl⟩

theorem tendsto_primePowerSurcharge_fixed_ratio {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (fun m : ℕ => suzukiPrimePowerSurcharge m (Real.sqrt (lam * m)))
      atTop (𝓝 ((Real.log lam) ^ 2 / 4)) := by
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have h := eventually_uniform_primePowerSurcharge_log_window (Real.log_nonneg hlam.le) hdelta
  filter_upwards [h] with m hm
  simpa [Real.dist_eq, Real.exp_log (by linarith : 0 < lam), mul_comm]
    using hm (Real.log lam) ⟨Real.log_nonneg hlam.le, le_rfl⟩

end RHGarden
