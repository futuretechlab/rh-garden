import RHGarden.SuzukiPrimeSubset

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Rational enclosures of the two finite counterexample endpoints. -/
noncomputable section
namespace RHGarden
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def suzukiOnePercentTarget (m : ℕ) (x : ℝ) : ℝ :=
  suzukiIntegratedMainTerm m x / 100 + Real.log x / Real.sqrt m * Real.log (x / m)

theorem onePercent_log_m1 :
    (12689828147 / 1000000000 : ℝ) ≤ Real.log 324431 := by
  have hn : (213178907614 / 1000000000000 : ℝ) ≤ Real.log (324431 / 2 ^ 18) ∧
      Real.log (324431 / 2 ^ 18) ≤ 213178907615 / 1000000000000 :=
    log_rational_bounds (by norm_num) 12 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  exact (log_scaled_bounds 18 (by norm_num) hn (by norm_num)
    (by norm_num) (by norm_num : (18 : ℝ) * (693147181 / 1000000000) +
      213178907615 / 1000000000000 ≤ 13)).1

theorem onePercent_log_m2 :
    (15964157319 / 1000000000 : ℝ) ≤ Real.log 8573249 := by
  have hn : (21772179035 / 1000000000000 : ℝ) ≤ Real.log (8573249 / 2 ^ 23) ∧
      Real.log (8573249 / 2 ^ 23) ≤ 21772179036 / 1000000000000 :=
    log_rational_bounds (by norm_num) 12 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  exact (log_scaled_bounds 23 (by norm_num) hn (by norm_num)
    (by norm_num) (by norm_num : (23 : ℝ) * (693147181 / 1000000000) +
      21772179036 / 1000000000000 ≤ 16)).1

private theorem endpoint_upper {m : ℕ} {x a b l u L : ℝ}
    (ha : 0 < a) (hl : 0 ≤ l) (_hu : 0 ≤ u) (hL : 0 ≤ L)
    (hm : a ≤ Real.sqrt m) (hx : Real.sqrt x ≤ b)
    (hr : l ≤ Real.log (x / m) ∧ Real.log (x / m) ≤ u)
    (hlog : Real.log x ≤ L) :
    suzukiIntegratedMainTerm m x ≤ 4 * (b - a) - 2 * a * l ∧
      Real.log x / Real.sqrt m * Real.log (x / m) ≤ L / a * u := by
  have hs0 := ha.trans_le hm
  have hprod := mul_le_mul hm hr.1 hl (Real.sqrt_nonneg m)
  constructor
  · unfold suzukiIntegratedMainTerm
    nlinarith
  · have hdiv : Real.log x / Real.sqrt m ≤ L / a :=
      div_le_div₀ hL hlog ha hm
    exact mul_le_mul hdiv hr.2 (hl.trans hr.1) (div_nonneg hL ha.le)

theorem onePercent_endpoint1_bounds :
    suzukiIntegratedMainTerm 324431 339360 ≤ (58076291 / 100000000 : ℝ) ∧
    Real.log 339360 / Real.sqrt 324431 * Real.log (339360 / 324431) ≤
      (100586 / 100000000 : ℝ) := by
  have hm : (569588447916 / 1000000000 : ℝ) ≤ Real.sqrt 324431 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 324431), Real.sqrt_nonneg (324431 : ℝ)]
  have hx : Real.sqrt 339360 ≤ (582546135513 / 1000000000 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 339360), Real.sqrt_nonneg (339360 : ℝ)]
  have hr : (44988612105 / 1000000000000 : ℝ) ≤ Real.log (339360 / 324431) ∧
      Real.log (339360 / 324431) ≤ 44988612106 / 1000000000000 :=
    log_rational_bounds (by norm_num) 4 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  have hn : (258167519719 / 1000000000000 : ℝ) ≤ Real.log (339360 / 2 ^ 18) ∧
      Real.log (339360 / 2 ^ 18) ≤ 258167519720 / 1000000000000 :=
    log_rational_bounds (by norm_num) 12 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  have hlog : Real.log 339360 ≤ (12734816778 / 1000000000 : ℝ) :=
    (log_scaled_bounds 18 (by norm_num) hn (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 18 * (693147180 / 1000000000) + 258167519719 / 1000000000000)
      (by norm_num)).2
  have hb := endpoint_upper (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm hx hr hlog
  norm_num at hb
  constructor <;> linarith [hb.1, hb.2]

theorem onePercent_endpoint2_bounds :
    suzukiIntegratedMainTerm 8573249 8620438 ≤ (4415155 / 100000000 : ℝ) ∧
    Real.log 8620438 / Real.sqrt 8573249 * Real.log (8620438 / 8573249) ≤
      (2994 / 100000000 : ℝ) := by
  have hm : (2928011099705 / 1000000000 : ℝ) ≤ Real.sqrt 8573249 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8573249), Real.sqrt_nonneg (8573249 : ℝ)]
  have hx : Real.sqrt 8620438 ≤ (2936058241930 / 1000000000 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8620438), Real.sqrt_nonneg (8620438 : ℝ)]
  have hr : (5489121499 / 1000000000000 : ℝ) ≤ Real.log (8620438 / 8573249) ∧
      Real.log (8620438 / 8573249) ≤ 5489121500 / 1000000000000 :=
    log_rational_bounds (by norm_num) 4 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  have hn : (27261300535 / 1000000000000 : ℝ) ≤ Real.log (8620438 / 2 ^ 23) ∧
      Real.log (8620438 / 2 ^ 23) ≤ 27261300536 / 1000000000000 :=
    log_rational_bounds (by norm_num) 12 (by norm_num [Finset.sum_range_succ])
      (by norm_num [Finset.sum_range_succ])
  have hlog : Real.log 8620438 ≤ (15969646464 / 1000000000 : ℝ) :=
    (log_scaled_bounds 23 (by norm_num) hn (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 23 * (693147180 / 1000000000) + 27261300535 / 1000000000000)
      (by norm_num)).2
  have hb := endpoint_upper (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm hx hr hlog
  norm_num at hb
  constructor <;> linarith [hb.1, hb.2]

theorem onePercent_witness1_eligible :
    (14929 : ℕ) ^ 3 ≥ 324431 ^ 2 ∧ 8 * 14929 ≤ 324431 := by norm_num

theorem onePercent_witness2_eligible :
    (47189 : ℕ) ^ 3 ≥ 8573249 ^ 2 ∧ 8 * 47189 ≤ 8573249 := by norm_num

end RHGarden
