import RHGarden.SuzukiOnePercentFailureFirst
import RHGarden.SuzukiOnePercentData2

/- Copyright (c) 2026 Future Technologies Laboratory LLC. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

theorem onePercent_primeArrival2_lower :
    (44795673551 / 1000000000000 : ℝ) ≤
      ∑ q ∈ Finset.Ioc 8573249 8620438,
        ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (8620438 / q) := by
  have hb := primeSubset_logArrival_lower onePercentRows8573249 (by norm_num)
    (by norm_num) (by convert onePercent_log_m2 using 1 <;> norm_num)
    onePercentRows8573249_valid onePercentRows8573249_chain
  simpa only [onePercentRows8573249_sum, Nat.cast_ofNat] using hb

theorem onePercent_failure_8573249 :
    (17 / 100000 : ℝ) < suzukiAnchoredIntegral 8573249 8620438 -
      suzukiOnePercentTarget 8573249 8620438 := by
  have hid := anchoredIntegral_eq_logArrival_sub_main (m := 8573249) (x := 8620438)
    (by norm_num) (by norm_num)
  norm_num only [Nat.floor_ofNat] at hid
  have hb := onePercent_endpoint2_bounds
  have ha := onePercent_primeArrival2_lower
  unfold suzukiOnePercentTarget
  linarith [hb.1, hb.2]

end RHGarden
