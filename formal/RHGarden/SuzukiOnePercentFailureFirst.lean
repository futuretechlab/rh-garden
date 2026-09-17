import RHGarden.SuzukiOnePercentData1
import RHGarden.SuzukiOnePercentEndpoints
import RHGarden.SuzukiPrimeSubsetExtras

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite strict counterexamples to the proposed one-percent arithmetic target.
These are not counterexamples to Suzuki positivity, RH, or an eventual bound. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

theorem onePercent_primeArrival1_lower :
    (592287163908 / 1000000000000 : ℝ) ≤
      ∑ q ∈ Finset.Ioc 324431 339360,
        ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (339360 / q) := by
  have hb := primeSubset_logArrival_lower onePercentRows324431 (by norm_num)
    (by norm_num) (by convert onePercent_log_m1 using 1 <;> norm_num)
    onePercentRows324431_valid onePercentRows324431_chain
  simpa only [onePercentRows324431_sum, Nat.cast_ofNat] using hb

/-- Even the certified prime-only lower sum leaves a margin exceeding .0047. -/
theorem onePercent_primeOnly_margin1 :
    (47 / 10000 : ℝ) < 592287163908 / 1000000000000 -
      suzukiIntegratedMainTerm 324431 339360 - suzukiOnePercentTarget 324431 339360 := by
  have hb := onePercent_endpoint1_bounds
  unfold suzukiOnePercentTarget
  nlinarith [hb.1, hb.2]

theorem onePercent_failure1_even_without_proper_powers :
    (47 / 10000 : ℝ) <
      (∑ q ∈ (Finset.Ioc 324431 339360).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (339360 / q)) -
      suzukiIntegratedMainTerm 324431 339360 - suzukiOnePercentTarget 324431 339360 := by
  have hb := primeSubset_primeLogArrival_lower onePercentRows324431 (by norm_num)
    (by norm_num) (by convert onePercent_log_m1 using 1 <;> norm_num)
    onePercentRows324431_valid onePercentRows324431_chain
  simp only [onePercentRows324431_sum, Nat.cast_ofNat] at hb
  linarith [onePercent_primeOnly_margin1]

theorem onePercent_arrival1_with_squares_lower :
    (592927163908 / 1000000000000 : ℝ) ≤
      ∑ q ∈ Finset.Ioc 324431 339360,
        ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (339360 / q) := by
  have hb := primeSubset_logArrival_lower_with_extras onePercentRows324431 {326041, 332929}
    (by norm_num) (by norm_num) (by convert onePercent_log_m1 using 1 <;> norm_num)
    onePercentRows324431_valid onePercentRows324431_chain
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num)
  simp only [onePercentRows324431_sum, Nat.cast_ofNat] at hb
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton] at hb
  linarith [onePercent_square571_lower, onePercent_square577_lower]

theorem onePercent_failure_324431 :
    (53 / 10000 : ℝ) < suzukiAnchoredIntegral 324431 339360 -
      suzukiOnePercentTarget 324431 339360 := by
  have hid := anchoredIntegral_eq_logArrival_sub_main (m := 324431) (x := 339360)
    (by norm_num) (by norm_num)
  norm_num only [Nat.floor_ofNat] at hid
  have hb := onePercent_endpoint1_bounds
  have ha := onePercent_arrival1_with_squares_lower
  unfold suzukiOnePercentTarget
  linarith [hb.1, hb.2]

end RHGarden
