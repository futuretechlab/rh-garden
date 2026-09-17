import Zeta23.FromPNTPlus.MediumPNT
import RHGarden.SuzukiSurchargeSummability

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Adapter from the unchanged pinned unconditional psi PNT to theta relative error.
No effective threshold is extracted from its existential Big-O constants. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RHGarden

theorem tendsto_psi_relative_error :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - x) * x⁻¹) atTop (𝓝 0) := by
  obtain ⟨c, hc, hPNT⟩ := MediumPNT
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have ht : Tendsto (fun x : ℝ => (x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))) * x⁻¹)
      atTop (𝓝 0) := by
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  exact (hPNT.mul (isBigO_refl (fun x : ℝ => x⁻¹) atTop)).trans_tendsto ht

theorem tendsto_psi_theta_relative_gap :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) * x⁻¹) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.sqrt x * x⁻¹) atTop (𝓝 0) := by
    apply (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs := Real.sq_sqrt hx.le
    have hs0 := (Real.sqrt_pos.mpr hx).ne'
    dsimp only [Function.comp_def]
    field_simp
    nlinarith
  exact (Chebyshev.isBigO_psi_sub_theta_sqrt.mul
    (isBigO_refl (fun x : ℝ => x⁻¹) atTop)).trans_tendsto ht

theorem tendsto_theta_relative_error :
    Tendsto (fun x : ℝ => (Chebyshev.theta x - x) * x⁻¹) atTop (𝓝 0) := by
  convert tendsto_psi_relative_error.sub tendsto_psi_theta_relative_gap using 1
  · funext x
    ring
  · simp

/-- The actual theta/x PNT, derived from the pinned psi PNT and the unconditional sqrt gap. -/
theorem tendsto_theta_div_self :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have h := tendsto_theta_relative_error.add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

theorem eventually_theta_relative_bound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ epsilon * x := by
  have h := (Metric.tendsto_nhds.mp tendsto_theta_relative_error) epsilon hepsilon
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : |Chebyshev.theta x - x| / x < epsilon := by
    simpa [Real.dist_eq, abs_mul, abs_inv, abs_of_pos hx0, div_eq_mul_inv] using hx
  exact ((div_lt_iff₀ hx0).mp he).le

theorem eventually_theta_log_window_bound (S : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x ∈ Set.Icc (Real.sqrt m) (Real.sqrt ((m : ℝ) * Real.exp S)),
        |Chebyshev.theta x - x| ≤ epsilon * x := by
  obtain ⟨X, hX⟩ := (eventually_atTop.mp (eventually_theta_relative_bound hepsilon))
  have hm : ∀ᶠ m : ℕ in atTop, X ≤ Real.sqrt (m : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  filter_upwards [hm] with m hm x hx
  exact hX x (hm.trans hx.1)

end RHGarden
