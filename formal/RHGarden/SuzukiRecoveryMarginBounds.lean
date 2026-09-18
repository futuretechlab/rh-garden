import RHGarden.SuzukiRecoveryFloor
import RHGarden.SuzukiPinnedEventBound

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

An unconditional but quantitatively insufficient recovery-margin estimate.
The logarithmic moment and mass are kept correlated before a global upper
bound is applied. No future local prime samples, fitted errors, recovery-time
bound, or short-interval PNT is an input. The explicit floor below is NOT
uniformly bounded, and must not be supplied to the constant-floor criterion.
-/
noncomputable section
open Set
open scoped BigOperators
namespace RHGarden

theorem mangoldt_correlated_moment_surplus (q : ℕ) :
    suzukiMangoldtIntercept q - Real.log 2 * suzukiMangoldtSlope q =
      ∑ n ∈ Finset.Icc 1 q, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (Real.log n - Real.log 2) := by
  simp only [suzukiMangoldtIntercept, suzukiMangoldtSlope,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A correlated mass/moment bound, not independent absolute-error bounds. -/
theorem log_two_mul_mangoldtSlope_le_intercept (q : ℕ) :
    Real.log 2 * suzukiMangoldtSlope q ≤ suzukiMangoldtIntercept q := by
  apply sub_nonneg.mp
  rw [mangoldt_correlated_moment_surplus]
  apply Finset.sum_nonneg
  intro n hn
  by_cases hn1 : n = 1
  · simp [hn1]
  · have hn2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (sub_nonneg.mpr (Real.log_le_log (by norm_num) (by exact_mod_cast hn2)))

def suzukiRecoverySupportFloor (t : ℝ) : ℝ :=
  suzukiPsiArchimedean t - (t - Real.log 2) * deriv suzukiPsiArchimedean t

/-- Use the actual active optimizer constraint A'(t)=S_q before estimating
the correlated moment T_q-log(2)*S_q. This floor is not constant. -/
theorem active_margin_ge_correlated_support {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiRecoverySupportFloor (suzukiArchDualOptimizer (suzukiMangoldtSlope q)) ≤
      suzukiGlobalDualMargin q := by
  let t := suzukiArchDualOptimizer (suzukiMangoldtSlope q)
  have ht := h.optimizer_mem_Ioo
  have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num)
    (by exact_mod_cast h.1.left_event.two_le)
  have hslope := deriv_archimedean_at_dualOptimizer_of_lt (hlog2.trans_lt ht.1)
  have hm := log_two_mul_mangoldtSlope_le_intercept q
  rw [← suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active h,
    suzukiMangoldtBlockMargin_eq_psi_optimizer_of_active h,
    suzukiPsi_eq_mangoldtBlock h.1 ht.1.le ht.2.le]
  dsimp [suzukiRecoverySupportFloor]
  rw [hslope]
  linarith

def suzukiRecoveryExplicitFloor (t : ℝ) : ℝ :=
  (151 / 20000 : ℝ) * (Real.exp (t / 2) - 1) -
    (t - Real.log 2) * (2 * Real.log 4 * Real.exp (t / 2) + 2 * t + t ^ 2 / 2)

theorem pinnedPrefix_le_log_endpoint {q : ℕ} (hq : 1 ≤ q) {t : ℝ}
    (hqt : Real.log q ≤ t) :
    suzukiPinnedPrefixUpper q ≤
      2 * Real.log 4 * Real.exp (t / 2) + 2 * t + t ^ 2 / 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have ht0 : 0 ≤ t := hlog0.trans hqt
  have hsqrt : Real.sqrt q ≤ Real.exp (t / 2) := by
    have heq : Real.exp (Real.log q / 2) = Real.sqrt q := by
      rw [← Real.log_sqrt hq0.le, Real.exp_log (Real.sqrt_pos.mpr hq0)]
    rw [← heq]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcoef : 0 ≤ 2 * Real.log 4 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hsqrt hcoef
  have hsq : Real.log q ^ 2 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqt) (add_nonneg ht0 hlog0)]
  dsimp [suzukiPinnedPrefixUpper]
  linarith

/-- Explicit all-active-block bound from proved archimedean growth,
correlated moment positivity, and the pinned global Chebyshev bound. -/
theorem active_margin_ge_explicit_floor {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiRecoveryExplicitFloor (suzukiArchDualOptimizer (suzukiMangoldtSlope q)) ≤
      suzukiGlobalDualMargin q := by
  let t := suzukiArchDualOptimizer (suzukiMangoldtSlope q)
  have ht := h.optimizer_mem_Ioo
  have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num)
    (by exact_mod_cast h.1.left_event.two_le)
  have ht2 : Real.log 2 ≤ t := hlog2.trans ht.1.le
  have ht0 : 0 ≤ t := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans ht2
  have hslope := deriv_archimedean_at_dualOptimizer_of_lt (hlog2.trans_lt ht.1)
  have hS := (mangoldtSlope_le_pinnedPrefix (by have := h.1.left_event.two_le; omega)).trans
    (pinnedPrefix_le_log_endpoint (by have := h.1.left_event.two_le; omega) ht.1.le)
  have hA := suzukiPsiArchimedean_ge_exp_sub_one ht0
  have hmul := mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr ht2)
  apply le_trans _ (active_margin_ge_correlated_support h)
  dsimp [suzukiRecoveryExplicitFloor, suzukiRecoverySupportFloor]
  rw [hslope]
  change _ ≤ suzukiPsiArchimedean t - (t - Real.log 2) * suzukiMangoldtSlope q
  linarith

theorem recovery_reserve_ge_explicit_floor {U b : ℝ} (hU : Real.sqrt 2 ≤ U)
    (hb : SuzukiRecoveryEndpoint U b) :
    suzukiRecoveryExplicitFloor (2 * Real.log b) ≤ suzukiPsiRoot b := by
  obtain ⟨q, r, hactive, hopt, _, _, hmargin⟩ := recoveryEndpoint_active_block hU hb
  rw [hopt, hmargin]
  exact active_margin_ge_explicit_floor hactive

/-- Reuse the stronger state-local energy, retaining the actual left
reserve and signed slope. No uniform lower bound for these data is inferred. -/
theorem active_margin_ge_existing_curvature_energy {q r : ℕ}
    (h : IsActiveMangoldtBlock q r) :
    suzukiEventCurvatureSafetyEnergy q ≤ suzukiGlobalDualMargin q := by
  rw [← suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active h]
  exact curvatureSafetyEnergy_le_blockMargin h.1

/-- Quantified inadequacy of THIS explicit estimate: its lower-bound
function is already at most -exp(t/2) for t>=2. This is not an upper bound
on the actual reserve and does not refute other arithmetic estimates. -/
theorem recoveryExplicitFloor_le_neg_exp {t : ℝ} (ht : 2 ≤ t) :
    suzukiRecoveryExplicitFloor t ≤ -Real.exp (t / 2) := by
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog4 : 1 ≤ Real.log 4 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [heq]
    linarith [Real.log_two_gt_d9]
  have hexp := Real.exp_pos (t / 2)
  have hprod := mul_le_mul_of_nonneg_right hlog4 hexp.le
  have hP : 2 * Real.exp (t / 2) ≤
      2 * Real.log 4 * Real.exp (t / 2) + 2 * t + t ^ 2 / 2 := by
    nlinarith [sq_nonneg t]
  have hW := mul_le_mul_of_nonneg_right (show 1 ≤ t - Real.log 2 by linarith)
    (show 0 ≤ 2 * Real.log 4 * Real.exp (t / 2) + 2 * t + t ^ 2 / 2 by linarith)
  dsimp [suzukiRecoveryExplicitFloor]
  nlinarith

theorem recoveryExplicitFloor_has_no_constant_floor {B : ℝ} (hB : 0 ≤ B) :
    ∃ t : ℝ, 2 ≤ t ∧ suzukiRecoveryExplicitFloor t < -B := by
  let t := max 2 (2 * Real.log (B + 1))
  have ht : 2 ≤ t := le_max_left _ _
  have hexp : B + 1 ≤ Real.exp (t / 2) := by
    rw [← Real.exp_log (by linarith : 0 < B + 1)]
    apply Real.exp_le_exp.mpr
    have := le_max_right (2 : ℝ) (2 * Real.log (B + 1))
    change 2 * Real.log (B + 1) ≤ t at this
    linarith
  exact ⟨t, ht, lt_of_le_of_lt (recoveryExplicitFloor_le_neg_exp ht) (by linarith)⟩

/-- The estimate's scale deficit persists on actual recovery endpoints,
which are cofinal. Only the ESTIMATE is below -B here, not the true reserve. -/
theorem explicit_floor_unbounded_on_actual_recoveries {U B : ℝ}
    (hU : Real.sqrt 2 ≤ U) (_hB : 0 ≤ B) :
    ∃ b : ℝ, SuzukiRecoveryEndpoint U b ∧
      suzukiRecoveryExplicitFloor (2 * Real.log b) < -B := by
  obtain ⟨a, hMa, haNeg⟩ := suzukiRootSlopeDiscrepancy_cofinal_neg
    (hU.trans (le_max_left U (max (B + 1) (Real.exp 1))))
  have hUa : U ≤ a := (le_max_left U (max (B + 1) (Real.exp 1))).trans hMa.le
  obtain ⟨b, hab, hb0, hbefore⟩ := suzukiRootSlopeDiscrepancy_first_recovery
    (hU.trans hUa) haNeg
  have hbB : B < b := by
    have hh := (le_max_left (B + 1) (Real.exp 1)).trans
      (le_max_right U (max (B + 1) (Real.exp 1)))
    linarith
  have hbExp : Real.exp 1 < b :=
    ((le_max_right (B + 1) (Real.exp 1)).trans
      (le_max_right U (max (B + 1) (Real.exp 1)))).trans_lt (hMa.trans hab)
  have hbpos := (Real.exp_pos 1).trans hbExp
  have hlog : 1 < Real.log b := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hbExp
  have hf := recoveryExplicitFloor_le_neg_exp (show 2 ≤ 2 * Real.log b by linarith)
  rw [show 2 * Real.log b / 2 = Real.log b by ring, Real.exp_log hbpos] at hf
  exact ⟨b, ⟨a, hUa, haNeg, hab, hb0, hbefore⟩, lt_of_le_of_lt hf (by linarith)⟩

end RHGarden
