import RHGarden.SuzukiSmallArithmetic

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
A finite cover with fresh affine-state reserves. No total variation is
carried across recoveries, and no event or proper prime power is suppressed. -/
noncomputable section
open Set
open scoped BigOperators
namespace RHGarden
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem small_state_0 : suzukiMangoldtSlope 0 = 0 ∧ suzukiMangoldtIntercept 0 = 0 := by
  norm_num [suzukiMangoldtSlope, suzukiMangoldtIntercept]

theorem small_state_1 :
    ((0 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 1 ∧ suzukiMangoldtSlope 1 ≤ (0 : ℝ) / 1000000) ∧
    ((0 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 1 ∧ suzukiMangoldtIntercept 1 ≤ (0 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 0
  have hi := suzukiMangoldtIntercept_succ 0
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 1 = 0 := by
    exact small_zero_1
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_0
  constructor <;> constructor <;> linarith [hp.1, hp.2]

theorem small_state_2 :
    ((490128 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 2 ∧ suzukiMangoldtSlope 2 ≤ (490131 : ℝ) / 1000000) ∧
    ((339730 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 2 ∧ suzukiMangoldtIntercept 2 ≤ (339734 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 1
  have hi := suzukiMangoldtIntercept_succ 1
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_1
  have hw := finite_weight_2
  have hc := finite_intercept_2
  constructor <;> constructor <;> linarith

theorem small_state_3 :
    ((1124411 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 3 ∧ suzukiMangoldtSlope 3 ≤ (1124417 : ℝ) / 1000000) ∧
    ((1036561 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 3 ∧ suzukiMangoldtIntercept 3 ≤ (1036569 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 2
  have hi := suzukiMangoldtIntercept_succ 2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_2
  have hw := finite_weight_3
  have hc := finite_intercept_3
  constructor <;> constructor <;> linarith

theorem small_state_4 :
    ((1470983 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 4 ∧ suzukiMangoldtSlope 4 ≤ (1470992 : ℝ) / 1000000) ∧
    ((1517013 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 4 ∧ suzukiMangoldtIntercept 4 ≤ (1517025 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 3
  have hi := suzukiMangoldtIntercept_succ 3
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_3
  have hw := finite_weight_4
  have hc := finite_intercept_4
  constructor <;> constructor <;> linarith

theorem small_state_5 :
    ((2190744 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 5 ∧ suzukiMangoldtSlope 5 ≤ (2190756 : ℝ) / 1000000) ∧
    ((2675425 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 5 ∧ suzukiMangoldtIntercept 5 ≤ (2675441 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 4
  have hi := suzukiMangoldtIntercept_succ 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_4
  have hw := finite_weight_5
  have hc := finite_intercept_5
  constructor <;> constructor <;> linarith

theorem small_state_6 :
    ((2190744 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 6 ∧ suzukiMangoldtSlope 6 ≤ (2190756 : ℝ) / 1000000) ∧
    ((2675425 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 6 ∧ suzukiMangoldtIntercept 6 ≤ (2675441 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 5
  have hi := suzukiMangoldtIntercept_succ 5
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 6 = 0 := by
    exact small_zero_6
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_5
  constructor <;> constructor <;> linarith

theorem small_state_7 :
    ((2926227 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 7 ∧ suzukiMangoldtSlope 7 ≤ (2926242 : ℝ) / 1000000) ∧
    ((4106611 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 7 ∧ suzukiMangoldtIntercept 7 ≤ (4106631 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 6
  have hi := suzukiMangoldtIntercept_succ 6
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_6
  have hw := finite_weight_7
  have hc := finite_intercept_7
  constructor <;> constructor <;> linarith

theorem small_state_8 :
    ((3171290 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 8 ∧ suzukiMangoldtSlope 8 ≤ (3171308 : ℝ) / 1000000) ∧
    ((4616207 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 8 ∧ suzukiMangoldtIntercept 8 ≤ (4616231 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 7
  have hi := suzukiMangoldtIntercept_succ 7
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_7
  have hw := finite_weight_8
  have hc := finite_intercept_8
  constructor <;> constructor <;> linarith

theorem small_state_9 :
    ((3537493 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 9 ∧ suzukiMangoldtSlope 9 ≤ (3537514 : ℝ) / 1000000) ∧
    ((5420838 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 9 ∧ suzukiMangoldtIntercept 9 ≤ (5420866 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 8
  have hi := suzukiMangoldtIntercept_succ 8
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_8
  have hw := finite_weight_9
  have hc := finite_intercept_9
  constructor <;> constructor <;> linarith

theorem small_state_10 :
    ((3537493 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 10 ∧ suzukiMangoldtSlope 10 ≤ (3537514 : ℝ) / 1000000) ∧
    ((5420838 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 10 ∧ suzukiMangoldtIntercept 10 ≤ (5420866 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 9
  have hi := suzukiMangoldtIntercept_succ 9
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 10 = 0 := by
    exact small_zero_10
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_9
  constructor <;> constructor <;> linarith

theorem small_state_11 :
    ((4260484 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 11 ∧ suzukiMangoldtSlope 11 ≤ (4260508 : ℝ) / 1000000) ∧
    ((7154497 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 11 ∧ suzukiMangoldtIntercept 11 ≤ (7154529 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 10
  have hi := suzukiMangoldtIntercept_succ 10
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_10
  have hw := finite_weight_11
  have hc := finite_intercept_11
  constructor <;> constructor <;> linarith

theorem small_state_12 :
    ((4260484 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 12 ∧ suzukiMangoldtSlope 12 ≤ (4260508 : ℝ) / 1000000) ∧
    ((7154497 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 12 ∧ suzukiMangoldtIntercept 12 ≤ (7154529 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 11
  have hi := suzukiMangoldtIntercept_succ 11
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 12 = 0 := by
    exact small_zero_12
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_11
  constructor <;> constructor <;> linarith

theorem small_state_13 :
    ((4971871 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 13 ∧ suzukiMangoldtSlope 13 ≤ (4971898 : ℝ) / 1000000) ∧
    ((8979172 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 13 ∧ suzukiMangoldtIntercept 13 ≤ (8979208 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 12
  have hi := suzukiMangoldtIntercept_succ 12
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_12
  have hw := finite_weight_13
  have hc := finite_intercept_13
  constructor <;> constructor <;> linarith

theorem small_state_14 :
    ((4971871 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 14 ∧ suzukiMangoldtSlope 14 ≤ (4971898 : ℝ) / 1000000) ∧
    ((8979172 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 14 ∧ suzukiMangoldtIntercept 14 ≤ (8979208 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 13
  have hi := suzukiMangoldtIntercept_succ 13
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 14 = 0 := by
    exact small_zero_14
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_13
  constructor <;> constructor <;> linarith

theorem small_state_15 :
    ((4971871 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 15 ∧ suzukiMangoldtSlope 15 ≤ (4971898 : ℝ) / 1000000) ∧
    ((8979172 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 15 ∧ suzukiMangoldtIntercept 15 ≤ (8979208 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 14
  have hi := suzukiMangoldtIntercept_succ 14
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 15 = 0 := by
    exact small_zero_15
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_14
  constructor <;> constructor <;> linarith

theorem small_state_16 :
    ((5145156 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 16 ∧ suzukiMangoldtSlope 16 ≤ (5145186 : ℝ) / 1000000) ∧
    ((9459624 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 16 ∧ suzukiMangoldtIntercept 16 ≤ (9459664 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 15
  have hi := suzukiMangoldtIntercept_succ 15
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_15
  have hw := finite_weight_16
  have hc := finite_intercept_16
  constructor <;> constructor <;> linarith

theorem small_state_17 :
    ((5832310 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 17 ∧ suzukiMangoldtSlope 17 ≤ (5832343 : ℝ) / 1000000) ∧
    ((11406480 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 17 ∧ suzukiMangoldtIntercept 17 ≤ (11406524 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 16
  have hi := suzukiMangoldtIntercept_succ 16
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_16
  have hw := finite_weight_17
  have hc := finite_intercept_17
  constructor <;> constructor <;> linarith

theorem small_state_18 :
    ((5832310 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 18 ∧ suzukiMangoldtSlope 18 ≤ (5832343 : ℝ) / 1000000) ∧
    ((11406480 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 18 ∧ suzukiMangoldtIntercept 18 ≤ (11406524 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 17
  have hi := suzukiMangoldtIntercept_succ 17
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 18 = 0 := by
    exact small_zero_18
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_17
  constructor <;> constructor <;> linarith

theorem small_state_19 :
    ((6507809 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 19 ∧ suzukiMangoldtSlope 19 ≤ (6507845 : ℝ) / 1000000) ∧
    ((13395449 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 19 ∧ suzukiMangoldtIntercept 19 ≤ (13395497 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 18
  have hi := suzukiMangoldtIntercept_succ 18
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_18
  have hw := finite_weight_19
  have hc := finite_intercept_19
  constructor <;> constructor <;> linarith

theorem small_state_20 :
    ((6507809 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 20 ∧ suzukiMangoldtSlope 20 ≤ (6507845 : ℝ) / 1000000) ∧
    ((13395449 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 20 ∧ suzukiMangoldtIntercept 20 ≤ (13395497 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 19
  have hi := suzukiMangoldtIntercept_succ 19
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 20 = 0 := by
    exact small_zero_20
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_19
  constructor <;> constructor <;> linarith

theorem small_state_21 :
    ((6507809 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 21 ∧ suzukiMangoldtSlope 21 ≤ (6507845 : ℝ) / 1000000) ∧
    ((13395449 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 21 ∧ suzukiMangoldtIntercept 21 ≤ (13395497 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 20
  have hi := suzukiMangoldtIntercept_succ 20
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 21 = 0 := by
    exact small_zero_21
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_20
  constructor <;> constructor <;> linarith

theorem small_state_22 :
    ((6507809 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 22 ∧ suzukiMangoldtSlope 22 ≤ (6507845 : ℝ) / 1000000) ∧
    ((13395449 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 22 ∧ suzukiMangoldtIntercept 22 ≤ (13395497 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 21
  have hi := suzukiMangoldtIntercept_succ 21
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 22 = 0 := by
    exact small_zero_22
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_21
  constructor <;> constructor <;> linarith

theorem small_state_23 :
    ((7161603 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 23 ∧ suzukiMangoldtSlope 23 ≤ (7161642 : ℝ) / 1000000) ∧
    ((15445420 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 23 ∧ suzukiMangoldtIntercept 23 ≤ (15445472 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 22
  have hi := suzukiMangoldtIntercept_succ 22
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_22
  have hw := finite_weight_23
  have hc := finite_intercept_23
  constructor <;> constructor <;> linarith

theorem small_state_24 :
    ((7161603 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 24 ∧ suzukiMangoldtSlope 24 ≤ (7161642 : ℝ) / 1000000) ∧
    ((15445420 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 24 ∧ suzukiMangoldtIntercept 24 ≤ (15445472 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 23
  have hi := suzukiMangoldtIntercept_succ 23
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 24 = 0 := by
    exact small_zero_24
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_23
  constructor <;> constructor <;> linarith

theorem small_state_25 :
    ((7483489 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 25 ∧ suzukiMangoldtSlope 25 ≤ (7483531 : ℝ) / 1000000) ∧
    ((16481535 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 25 ∧ suzukiMangoldtIntercept 25 ≤ (16481591 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 24
  have hi := suzukiMangoldtIntercept_succ 24
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_24
  have hw := finite_weight_25
  have hc := finite_intercept_25
  constructor <;> constructor <;> linarith

theorem small_state_26 :
    ((7483489 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 26 ∧ suzukiMangoldtSlope 26 ≤ (7483531 : ℝ) / 1000000) ∧
    ((16481535 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 26 ∧ suzukiMangoldtIntercept 26 ≤ (16481591 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 25
  have hi := suzukiMangoldtIntercept_succ 25
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 26 = 0 := by
    exact small_zero_26
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_25
  constructor <;> constructor <;> linarith

theorem small_state_27 :
    ((7694916 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 27 ∧ suzukiMangoldtSlope 27 ≤ (7694961 : ℝ) / 1000000) ∧
    ((17178366 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 27 ∧ suzukiMangoldtIntercept 27 ≤ (17178426 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 26
  have hi := suzukiMangoldtIntercept_succ 26
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_26
  have hw := finite_weight_27
  have hc := finite_intercept_27
  constructor <;> constructor <;> linarith

theorem small_state_28 :
    ((7694916 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 28 ∧ suzukiMangoldtSlope 28 ≤ (7694961 : ℝ) / 1000000) ∧
    ((17178366 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 28 ∧ suzukiMangoldtIntercept 28 ≤ (17178426 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 27
  have hi := suzukiMangoldtIntercept_succ 27
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 28 = 0 := by
    exact small_zero_28
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_27
  constructor <;> constructor <;> linarith

theorem small_state_29 :
    ((8320206 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 29 ∧ suzukiMangoldtSlope 29 ≤ (8320254 : ℝ) / 1000000) ∧
    ((19283905 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 29 ∧ suzukiMangoldtIntercept 29 ≤ (19283969 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 28
  have hi := suzukiMangoldtIntercept_succ 28
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_28
  have hw := finite_weight_29
  have hc := finite_intercept_29
  constructor <;> constructor <;> linarith

theorem small_state_30 :
    ((8320206 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 30 ∧ suzukiMangoldtSlope 30 ≤ (8320254 : ℝ) / 1000000) ∧
    ((19283905 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 30 ∧ suzukiMangoldtIntercept 30 ≤ (19283969 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 29
  have hi := suzukiMangoldtIntercept_succ 29
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 30 = 0 := by
    exact small_zero_30
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_29
  constructor <;> constructor <;> linarith

theorem small_state_31 :
    ((8936967 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 31 ∧ suzukiMangoldtSlope 31 ≤ (8937018 : ℝ) / 1000000) ∧
    ((21401857 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 31 ∧ suzukiMangoldtIntercept 31 ≤ (21401925 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 30
  have hi := suzukiMangoldtIntercept_succ 30
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_30
  have hw := finite_weight_31
  have hc := finite_intercept_31
  constructor <;> constructor <;> linarith

theorem small_state_32 :
    ((9059498 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 32 ∧ suzukiMangoldtSlope 32 ≤ (9059552 : ℝ) / 1000000) ∧
    ((21826520 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 32 ∧ suzukiMangoldtIntercept 32 ≤ (21826592 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 31
  have hi := suzukiMangoldtIntercept_succ 31
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_31
  have hw := finite_weight_32
  have hc := finite_intercept_32
  constructor <;> constructor <;> linarith

theorem small_state_33 :
    ((9059498 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 33 ∧ suzukiMangoldtSlope 33 ≤ (9059552 : ℝ) / 1000000) ∧
    ((21826520 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 33 ∧ suzukiMangoldtIntercept 33 ≤ (21826592 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 32
  have hi := suzukiMangoldtIntercept_succ 32
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 33 = 0 := by
    exact small_zero_33
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_32
  constructor <;> constructor <;> linarith

theorem small_state_34 :
    ((9059498 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 34 ∧ suzukiMangoldtSlope 34 ≤ (9059552 : ℝ) / 1000000) ∧
    ((21826520 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 34 ∧ suzukiMangoldtIntercept 34 ≤ (21826592 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 33
  have hi := suzukiMangoldtIntercept_succ 33
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 34 = 0 := by
    exact small_zero_34
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_33
  constructor <;> constructor <;> linarith

theorem small_state_35 :
    ((9059498 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 35 ∧ suzukiMangoldtSlope 35 ≤ (9059552 : ℝ) / 1000000) ∧
    ((21826520 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 35 ∧ suzukiMangoldtIntercept 35 ≤ (21826592 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 34
  have hi := suzukiMangoldtIntercept_succ 34
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 35 = 0 := by
    exact small_zero_35
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_34
  constructor <;> constructor <;> linarith

theorem small_state_36 :
    ((9059498 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 36 ∧ suzukiMangoldtSlope 36 ≤ (9059552 : ℝ) / 1000000) ∧
    ((21826520 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 36 ∧ suzukiMangoldtIntercept 36 ≤ (21826592 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 35
  have hi := suzukiMangoldtIntercept_succ 35
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hz : ArithmeticFunction.vonMangoldt 36 = 0 := by
    exact small_zero_36
  rw [hz] at hs hi
  norm_num only [zero_div, zero_mul, add_zero] at hs hi
  have hp := small_state_35
  constructor <;> constructor <;> linarith

theorem small_state_37 :
    ((9653128 : ℝ) / 1000000 ≤ suzukiMangoldtSlope 37 ∧ suzukiMangoldtSlope 37 ≤ (9653185 : ℝ) / 1000000) ∧
    ((23970072 : ℝ) / 1000000 ≤ suzukiMangoldtIntercept 37 ∧ suzukiMangoldtIntercept 37 ≤ (23970148 : ℝ) / 1000000) := by
  have hs := suzukiMangoldtSlope_succ 36
  have hi := suzukiMangoldtIntercept_succ 36
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hs hi
  have hp := small_state_36
  have hw := finite_weight_37
  have hc := finite_intercept_37
  constructor <;> constructor <;> linarith

/-- A computed rational lower value at a root sample, with cancellation
retained before applying the logarithm enclosure. -/
theorem affine_sample_lower {u T I tl th il ih ll lh : ℝ}
    (hu : 1 < u) (hT : tl ≤ T ∧ T ≤ th) (hI : il ≤ I ∧ I ≤ ih)
    (hl : ll ≤ Real.log u ∧ Real.log u ≤ lh) (hth : 0 ≤ th) :
    4 * u - 8 + 42954 / 10000 -
      (4 / 25 : ℝ) * (u⁻¹)^5 / (1 - (u⁻¹)^4) -
      (53743 / 10000 + 2 * th) * lh + il ≤
    suzukiPsiArchimedean (2 * Real.log u) - T * (2 * Real.log u) + I := by
  have ha := (arch_root_rational_enclosure hu).1
  have hp := mul_le_mul_of_nonneg_right hT.2 (Real.log_nonneg hu.le)
  have hq := mul_le_mul_of_nonneg_left hl.2
    (show 0 ≤ 53743 / 10000 + 2 * th by linarith)
  nlinarith [hI.1]

theorem affine_sample_upper {u T I tl th il ih ll lh : ℝ}
    (hu : 1 < u) (hT : tl ≤ T ∧ T ≤ th) (hI : il ≤ I ∧ I ≤ ih)
    (hl : ll ≤ Real.log u ∧ Real.log u ≤ lh) (htl : 0 ≤ tl) :
    suzukiPsiArchimedean (2 * Real.log u) - T * (2 * Real.log u) + I ≤
    4 * u - 8 + 429934 / 100000 - (53700 / 10000 + 2 * tl) * ll + ih := by
  have ha := (arch_root_rational_enclosure hu).2
  have hp := mul_le_mul_of_nonneg_right hT.1 (Real.log_nonneg hu.le)
  have hq := mul_le_mul_of_nonneg_left hl.1
    (show 0 ≤ 53700 / 10000 + 2 * tl by linarith)
  nlinarith [hI.2]

theorem sample_log_5 :
    (89117802 : ℝ) / 100000000 ≤ Real.log ((2438 : ℝ) / 1000) ∧
    Real.log ((2438 : ℝ) / 1000) ≤ (89117805 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (198030850 : ℝ) / 1000000000) (b := (198030851 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_5 {T I t : ℝ}
    (hT : (2190744 : ℝ) / 1000000 ≤ T ∧ T ≤ (2190756 : ℝ) / 1000000)
    (hI : (2675425 : ℝ) / 1000000 ≤ I ∧ I ≤ (2675441 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (2438 : ℝ) / 1000)
    hT hI sample_log_5 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (2438 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((2438 : ℝ) / 1000) := by
    have hlog := sample_log_5.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((2438 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((2438 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_7 :
    (103175997 : ℝ) / 100000000 ≤ Real.log ((2806 : ℝ) / 1000) ∧
    Real.log ((2806 : ℝ) / 1000) ≤ (103176000 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (338612801 : ℝ) / 1000000000) (b := (338612802 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_7 {T I t : ℝ}
    (hT : (2926227 : ℝ) / 1000000 ≤ T ∧ T ≤ (2926242 : ℝ) / 1000000)
    (hI : (4106611 : ℝ) / 1000000 ≤ I ∧ I ≤ (4106631 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (2806 : ℝ) / 1000)
    hT hI sample_log_7 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (2806 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((2806 : ℝ) / 1000) := by
    have hlog := sample_log_7.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((2806 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((2806 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_8 :
    (107466105 : ℝ) / 100000000 ≤ Real.log ((2929 : ℝ) / 1000) ∧
    Real.log ((2929 : ℝ) / 1000) ≤ (107466108 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (381513887 : ℝ) / 1000000000) (b := (381513888 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_8 {T I t : ℝ}
    (hT : (3171290 : ℝ) / 1000000 ≤ T ∧ T ≤ (3171308 : ℝ) / 1000000)
    (hI : (4616207 : ℝ) / 1000000 ≤ I ∧ I ≤ (4616231 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (2929 : ℝ) / 1000)
    hT hI sample_log_8 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (2929 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((2929 : ℝ) / 1000) := by
    have hlog := sample_log_8.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((2929 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((2929 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_9 :
    (113526559 : ℝ) / 100000000 ≤ Real.log ((3112 : ℝ) / 1000) ∧
    Real.log ((3112 : ℝ) / 1000) ≤ (113526562 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (442118425 : ℝ) / 1000000000) (b := (442118426 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_9 {T I t : ℝ}
    (hT : (3537493 : ℝ) / 1000000 ≤ T ∧ T ≤ (3537514 : ℝ) / 1000000)
    (hI : (5420838 : ℝ) / 1000000 ≤ I ∧ I ≤ (5420866 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (3112 : ℝ) / 1000)
    hT hI sample_log_9 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (3112 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((3112 : ℝ) / 1000) := by
    have hlog := sample_log_9.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((3112 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((3112 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_11 :
    (124501876 : ℝ) / 100000000 ≤ Real.log ((3473 : ℝ) / 1000) ∧
    Real.log ((3473 : ℝ) / 1000) ≤ (124501879 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (551871593 : ℝ) / 1000000000) (b := (551871594 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_11 {T I t : ℝ}
    (hT : (4260484 : ℝ) / 1000000 ≤ T ∧ T ≤ (4260508 : ℝ) / 1000000)
    (hI : (7154497 : ℝ) / 1000000 ≤ I ∧ I ≤ (7154529 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (3473 : ℝ) / 1000)
    hT hI sample_log_11 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (3473 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((3473 : ℝ) / 1000) := by
    have hlog := sample_log_11.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((3473 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((3473 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_13 :
    (134260366 : ℝ) / 100000000 ≤ Real.log ((3829 : ℝ) / 1000) ∧
    Real.log ((3829 : ℝ) / 1000) ≤ (134260369 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (649456491 : ℝ) / 1000000000) (b := (649456492 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_13 {T I t : ℝ}
    (hT : (4971871 : ℝ) / 1000000 ≤ T ∧ T ≤ (4971898 : ℝ) / 1000000)
    (hI : (8979172 : ℝ) / 1000000 ≤ I ∧ I ≤ (8979208 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (3829 : ℝ) / 1000)
    hT hI sample_log_13 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (3829 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((3829 : ℝ) / 1000) := by
    have hlog := sample_log_13.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((3829 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((3829 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_16 :
    (136507071 : ℝ) / 100000000 ≤ Real.log ((3916 : ℝ) / 1000) ∧
    Real.log ((3916 : ℝ) / 1000) ≤ (136507074 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (671923544 : ℝ) / 1000000000) (b := (671923545 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_16 {T I t : ℝ}
    (hT : (5145156 : ℝ) / 1000000 ≤ T ∧ T ≤ (5145186 : ℝ) / 1000000)
    (hI : (9459624 : ℝ) / 1000000 ≤ I ∧ I ≤ (9459664 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (3916 : ℝ) / 1000)
    hT hI sample_log_16 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (3916 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((3916 : ℝ) / 1000) := by
    have hlog := sample_log_16.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((3916 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((3916 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_17 :
    (144903438 : ℝ) / 100000000 ≤ Real.log ((4259 : ℝ) / 1000) ∧
    Real.log ((4259 : ℝ) / 1000) ≤ (144903441 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (62740029 : ℝ) / 1000000000) (b := (62740030 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_17 {T I t : ℝ}
    (hT : (5832310 : ℝ) / 1000000 ≤ T ∧ T ≤ (5832343 : ℝ) / 1000000)
    (hI : (11406480 : ℝ) / 1000000 ≤ I ∧ I ≤ (11406524 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (4259 : ℝ) / 1000)
    hT hI sample_log_17 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (4259 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((4259 : ℝ) / 1000) := by
    have hlog := sample_log_17.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((4259 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((4259 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_19 :
    (152540390 : ℝ) / 100000000 ≤ Real.log ((4597 : ℝ) / 1000) ∧
    Real.log ((4597 : ℝ) / 1000) ≤ (152540393 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (139109555 : ℝ) / 1000000000) (b := (139109556 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_19 {T I t : ℝ}
    (hT : (6507809 : ℝ) / 1000000 ≤ T ∧ T ≤ (6507845 : ℝ) / 1000000)
    (hI : (13395449 : ℝ) / 1000000 ≤ I ∧ I ≤ (13395497 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (4597 : ℝ) / 1000)
    hT hI sample_log_19 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (4597 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((4597 : ℝ) / 1000) := by
    have hlog := sample_log_19.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((4597 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((4597 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_23 :
    (159412119 : ℝ) / 100000000 ≤ Real.log ((4924 : ℝ) / 1000) ∧
    Real.log ((4924 : ℝ) / 1000) ≤ (159412122 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (207826847 : ℝ) / 1000000000) (b := (207826848 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_23 {T I t : ℝ}
    (hT : (7161603 : ℝ) / 1000000 ≤ T ∧ T ≤ (7161642 : ℝ) / 1000000)
    (hI : (15445420 : ℝ) / 1000000 ≤ I ∧ I ≤ (15445472 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (4924 : ℝ) / 1000)
    hT hI sample_log_23 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (4924 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((4924 : ℝ) / 1000) := by
    have hlog := sample_log_23.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((4924 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((4924 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_25 :
    (162629501 : ℝ) / 100000000 ≤ Real.log ((5085 : ℝ) / 1000) ∧
    Real.log ((5085 : ℝ) / 1000) ≤ (162629504 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (240000668 : ℝ) / 1000000000) (b := (240000669 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_25 {T I t : ℝ}
    (hT : (7483489 : ℝ) / 1000000 ≤ T ∧ T ≤ (7483531 : ℝ) / 1000000)
    (hI : (16481535 : ℝ) / 1000000 ≤ I ∧ I ≤ (16481591 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (5085 : ℝ) / 1000)
    hT hI sample_log_25 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (5085 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((5085 : ℝ) / 1000) := by
    have hlog := sample_log_25.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((5085 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((5085 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_27 :
    (164692634 : ℝ) / 100000000 ≤ Real.log ((5191 : ℝ) / 1000) ∧
    Real.log ((5191 : ℝ) / 1000) ≤ (164692637 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (260631995 : ℝ) / 1000000000) (b := (260631996 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_27 {T I t : ℝ}
    (hT : (7694916 : ℝ) / 1000000 ≤ T ∧ T ≤ (7694961 : ℝ) / 1000000)
    (hI : (17178366 : ℝ) / 1000000 ≤ I ∧ I ≤ (17178426 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (5191 : ℝ) / 1000)
    hT hI sample_log_27 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (5191 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((5191 : ℝ) / 1000) := by
    have hlog := sample_log_27.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((5191 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((5191 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_29 :
    (170529338 : ℝ) / 100000000 ≤ Real.log ((5503 : ℝ) / 1000) ∧
    Real.log ((5503 : ℝ) / 1000) ≤ (170529341 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (318999036 : ℝ) / 1000000000) (b := (318999037 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_29 {T I t : ℝ}
    (hT : (8320206 : ℝ) / 1000000 ≤ T ∧ T ≤ (8320254 : ℝ) / 1000000)
    (hI : (19283905 : ℝ) / 1000000 ≤ I ∧ I ≤ (19283969 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (5503 : ℝ) / 1000)
    hT hI sample_log_29 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (5503 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((5503 : ℝ) / 1000) := by
    have hlog := sample_log_29.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((5503 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((5503 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_31 :
    (175992473 : ℝ) / 100000000 ≤ Real.log ((5812 : ℝ) / 1000) ∧
    Real.log ((5812 : ℝ) / 1000) ≤ (175992476 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (373630384 : ℝ) / 1000000000) (b := (373630385 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_31 {T I t : ℝ}
    (hT : (8936967 : ℝ) / 1000000 ≤ T ∧ T ≤ (8937018 : ℝ) / 1000000)
    (hI : (21401857 : ℝ) / 1000000 ≤ I ∧ I ≤ (21401925 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (5812 : ℝ) / 1000)
    hT hI sample_log_31 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (5812 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((5812 : ℝ) / 1000) := by
    have hlog := sample_log_31.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((5812 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((5812 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem sample_log_32 :
    (177036556 : ℝ) / 100000000 ≤ Real.log ((5873 : ℝ) / 1000) ∧
    Real.log ((5873 : ℝ) / 1000) ≤ (177036559 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (384071215 : ℝ) / 1000000000) (b := (384071216 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem small_affine_32 {T I t : ℝ}
    (hT : (9059498 : ℝ) / 1000000 ≤ T ∧ T ≤ (9059552 : ℝ) / 1000000)
    (hI : (21826520 : ℝ) / 1000000 ≤ I ∧ I ≤ (21826592 : ℝ) / 1000000)
    (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t - T * t + I := by
  have ha := affine_sample_lower (by norm_num : (1 : ℝ) < (5873 : ℝ) / 1000)
    hT hI sample_log_32 (by norm_num)
  have hs := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < (5873 : ℝ) / 1000)
  have hx : Real.log 2 ≤ 2 * Real.log ((5873 : ℝ) / 1000) := by
    have hlog := sample_log_32.1
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith
  have hd : |deriv suzukiPsiArchimedean (2 * Real.log ((5873 : ℝ) / 1000)) - T| ≤
      (1 / 100 : ℝ) := by
    change |suzukiRootArchSlope ((5873 : ℝ) / 1000) - T| ≤ _
    norm_num at hs
    rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  have hh := affine_state_lower_of_sample hx ht ha hd
  norm_num at hh
  linarith

theorem small_affine_state_positive (n : ℕ) (hn : 5 ≤ n) (hn' : n ≤ 36)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (1 / 100 : ℝ) ≤ suzukiPsiArchimedean t -
      suzukiMangoldtSlope n * t + suzukiMangoldtIntercept n := by
  interval_cases n
  · exact small_affine_5 small_state_5.1 small_state_5.2 ht
  · exact small_affine_5 small_state_6.1 small_state_6.2 ht
  · exact small_affine_7 small_state_7.1 small_state_7.2 ht
  · exact small_affine_8 small_state_8.1 small_state_8.2 ht
  · exact small_affine_9 small_state_9.1 small_state_9.2 ht
  · exact small_affine_9 small_state_10.1 small_state_10.2 ht
  · exact small_affine_11 small_state_11.1 small_state_11.2 ht
  · exact small_affine_11 small_state_12.1 small_state_12.2 ht
  · exact small_affine_13 small_state_13.1 small_state_13.2 ht
  · exact small_affine_13 small_state_14.1 small_state_14.2 ht
  · exact small_affine_13 small_state_15.1 small_state_15.2 ht
  · exact small_affine_16 small_state_16.1 small_state_16.2 ht
  · exact small_affine_17 small_state_17.1 small_state_17.2 ht
  · exact small_affine_17 small_state_18.1 small_state_18.2 ht
  · exact small_affine_19 small_state_19.1 small_state_19.2 ht
  · exact small_affine_19 small_state_20.1 small_state_20.2 ht
  · exact small_affine_19 small_state_21.1 small_state_21.2 ht
  · exact small_affine_19 small_state_22.1 small_state_22.2 ht
  · exact small_affine_23 small_state_23.1 small_state_23.2 ht
  · exact small_affine_23 small_state_24.1 small_state_24.2 ht
  · exact small_affine_25 small_state_25.1 small_state_25.2 ht
  · exact small_affine_25 small_state_26.1 small_state_26.2 ht
  · exact small_affine_27 small_state_27.1 small_state_27.2 ht
  · exact small_affine_27 small_state_28.1 small_state_28.2 ht
  · exact small_affine_29 small_state_29.1 small_state_29.2 ht
  · exact small_affine_29 small_state_30.1 small_state_30.2 ht
  · exact small_affine_31 small_state_31.1 small_state_31.2 ht
  · exact small_affine_32 small_state_32.1 small_state_32.2 ht
  · exact small_affine_32 small_state_33.1 small_state_33.2 ht
  · exact small_affine_32 small_state_34.1 small_state_34.2 ht
  · exact small_affine_32 small_state_35.1 small_state_35.2 ht
  · exact small_affine_32 small_state_36.1 small_state_36.2 ht

/-- This finite cover includes every integer cell, hence every prime power,
and does not presume that a negative excursion has recovered. -/
theorem suzukiPsi_nonnegative_zero_to_log_thirtySeven {t : ℝ}
    (ht : 0 ≤ t) (ht37 : t ≤ Real.log 37) : 0 ≤ suzukiPsi t := by
  by_cases ht5 : t ≤ Real.log 5
  · exact suzukiPsi_nonnegative_zero_to_log_five ht ht5
  have h5 : Real.log 5 ≤ t := (lt_of_not_ge ht5).le
  have h2 : Real.log 2 ≤ t :=
    (Real.log_le_log (by norm_num) (by norm_num : (2 : ℝ) ≤ 5)).trans h5
  by_cases h6 : t ≤ Real.log 6
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 5) (by norm_num) h5 (by norm_num; exact h6)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 5 (by norm_num) (by norm_num) h2)
  have h6 : Real.log 6 ≤ t := (lt_of_not_ge h6).le
  by_cases h7 : t ≤ Real.log 7
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 6) (by norm_num) h6 (by norm_num; exact h7)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 6 (by norm_num) (by norm_num) h2)
  have h7 : Real.log 7 ≤ t := (lt_of_not_ge h7).le
  by_cases h8 : t ≤ Real.log 8
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 7) (by norm_num) h7 (by norm_num; exact h8)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 7 (by norm_num) (by norm_num) h2)
  have h8 : Real.log 8 ≤ t := (lt_of_not_ge h8).le
  by_cases h9 : t ≤ Real.log 9
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 8) (by norm_num) h8 (by norm_num; exact h9)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 8 (by norm_num) (by norm_num) h2)
  have h9 : Real.log 9 ≤ t := (lt_of_not_ge h9).le
  by_cases h10 : t ≤ Real.log 10
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 9) (by norm_num) h9 (by norm_num; exact h10)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 9 (by norm_num) (by norm_num) h2)
  have h10 : Real.log 10 ≤ t := (lt_of_not_ge h10).le
  by_cases h11 : t ≤ Real.log 11
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 10) (by norm_num) h10 (by norm_num; exact h11)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 10 (by norm_num) (by norm_num) h2)
  have h11 : Real.log 11 ≤ t := (lt_of_not_ge h11).le
  by_cases h12 : t ≤ Real.log 12
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 11) (by norm_num) h11 (by norm_num; exact h12)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 11 (by norm_num) (by norm_num) h2)
  have h12 : Real.log 12 ≤ t := (lt_of_not_ge h12).le
  by_cases h13 : t ≤ Real.log 13
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 12) (by norm_num) h12 (by norm_num; exact h13)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 12 (by norm_num) (by norm_num) h2)
  have h13 : Real.log 13 ≤ t := (lt_of_not_ge h13).le
  by_cases h14 : t ≤ Real.log 14
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 13) (by norm_num) h13 (by norm_num; exact h14)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 13 (by norm_num) (by norm_num) h2)
  have h14 : Real.log 14 ≤ t := (lt_of_not_ge h14).le
  by_cases h15 : t ≤ Real.log 15
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 14) (by norm_num) h14 (by norm_num; exact h15)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 14 (by norm_num) (by norm_num) h2)
  have h15 : Real.log 15 ≤ t := (lt_of_not_ge h15).le
  by_cases h16 : t ≤ Real.log 16
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 15) (by norm_num) h15 (by norm_num; exact h16)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 15 (by norm_num) (by norm_num) h2)
  have h16 : Real.log 16 ≤ t := (lt_of_not_ge h16).le
  by_cases h17 : t ≤ Real.log 17
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 16) (by norm_num) h16 (by norm_num; exact h17)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 16 (by norm_num) (by norm_num) h2)
  have h17 : Real.log 17 ≤ t := (lt_of_not_ge h17).le
  by_cases h18 : t ≤ Real.log 18
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 17) (by norm_num) h17 (by norm_num; exact h18)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 17 (by norm_num) (by norm_num) h2)
  have h18 : Real.log 18 ≤ t := (lt_of_not_ge h18).le
  by_cases h19 : t ≤ Real.log 19
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 18) (by norm_num) h18 (by norm_num; exact h19)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 18 (by norm_num) (by norm_num) h2)
  have h19 : Real.log 19 ≤ t := (lt_of_not_ge h19).le
  by_cases h20 : t ≤ Real.log 20
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 19) (by norm_num) h19 (by norm_num; exact h20)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 19 (by norm_num) (by norm_num) h2)
  have h20 : Real.log 20 ≤ t := (lt_of_not_ge h20).le
  by_cases h21 : t ≤ Real.log 21
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 20) (by norm_num) h20 (by norm_num; exact h21)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 20 (by norm_num) (by norm_num) h2)
  have h21 : Real.log 21 ≤ t := (lt_of_not_ge h21).le
  by_cases h22 : t ≤ Real.log 22
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 21) (by norm_num) h21 (by norm_num; exact h22)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 21 (by norm_num) (by norm_num) h2)
  have h22 : Real.log 22 ≤ t := (lt_of_not_ge h22).le
  by_cases h23 : t ≤ Real.log 23
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 22) (by norm_num) h22 (by norm_num; exact h23)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 22 (by norm_num) (by norm_num) h2)
  have h23 : Real.log 23 ≤ t := (lt_of_not_ge h23).le
  by_cases h24 : t ≤ Real.log 24
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 23) (by norm_num) h23 (by norm_num; exact h24)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 23 (by norm_num) (by norm_num) h2)
  have h24 : Real.log 24 ≤ t := (lt_of_not_ge h24).le
  by_cases h25 : t ≤ Real.log 25
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 24) (by norm_num) h24 (by norm_num; exact h25)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 24 (by norm_num) (by norm_num) h2)
  have h25 : Real.log 25 ≤ t := (lt_of_not_ge h25).le
  by_cases h26 : t ≤ Real.log 26
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 25) (by norm_num) h25 (by norm_num; exact h26)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 25 (by norm_num) (by norm_num) h2)
  have h26 : Real.log 26 ≤ t := (lt_of_not_ge h26).le
  by_cases h27 : t ≤ Real.log 27
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 26) (by norm_num) h26 (by norm_num; exact h27)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 26 (by norm_num) (by norm_num) h2)
  have h27 : Real.log 27 ≤ t := (lt_of_not_ge h27).le
  by_cases h28 : t ≤ Real.log 28
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 27) (by norm_num) h27 (by norm_num; exact h28)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 27 (by norm_num) (by norm_num) h2)
  have h28 : Real.log 28 ≤ t := (lt_of_not_ge h28).le
  by_cases h29 : t ≤ Real.log 29
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 28) (by norm_num) h28 (by norm_num; exact h29)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 28 (by norm_num) (by norm_num) h2)
  have h29 : Real.log 29 ≤ t := (lt_of_not_ge h29).le
  by_cases h30 : t ≤ Real.log 30
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 29) (by norm_num) h29 (by norm_num; exact h30)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 29 (by norm_num) (by norm_num) h2)
  have h30 : Real.log 30 ≤ t := (lt_of_not_ge h30).le
  by_cases h31 : t ≤ Real.log 31
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 30) (by norm_num) h30 (by norm_num; exact h31)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 30 (by norm_num) (by norm_num) h2)
  have h31 : Real.log 31 ≤ t := (lt_of_not_ge h31).le
  by_cases h32 : t ≤ Real.log 32
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 31) (by norm_num) h31 (by norm_num; exact h32)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 31 (by norm_num) (by norm_num) h2)
  have h32 : Real.log 32 ≤ t := (lt_of_not_ge h32).le
  by_cases h33 : t ≤ Real.log 33
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 32) (by norm_num) h32 (by norm_num; exact h33)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 32 (by norm_num) (by norm_num) h2)
  have h33 : Real.log 33 ≤ t := (lt_of_not_ge h33).le
  by_cases h34 : t ≤ Real.log 34
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 33) (by norm_num) h33 (by norm_num; exact h34)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 33 (by norm_num) (by norm_num) h2)
  have h34 : Real.log 34 ≤ t := (lt_of_not_ge h34).le
  by_cases h35 : t ≤ Real.log 35
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 34) (by norm_num) h34 (by norm_num; exact h35)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 34 (by norm_num) (by norm_num) h2)
  have h35 : Real.log 35 ≤ t := (lt_of_not_ge h35).le
  by_cases h36 : t ≤ Real.log 36
  · rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 35) (by norm_num) h35 (by norm_num; exact h36)]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 35 (by norm_num) (by norm_num) h2)
  have h36 : Real.log 36 ≤ t := (lt_of_not_ge h36).le
  rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (n := 36) (by norm_num) h36 (by norm_num; exact ht37)]
  exact (by norm_num : (0 : ℝ) ≤ 1 / 100).trans
      (small_affine_state_positive 36 (by norm_num) (by norm_num) h2)

/-- Coverage is explicit at the cutoff, including an excursion that began
before it or never recovers. No completed-excursion assumption is substituted
for the universal tail field of the established interface. -/
def suzukiPrefixThirtySevenPlusTail
    (htail : ∀ t, Real.log 37 ≤ t → 0 ≤ suzukiPsi t) : SuzukiExactPrefixPlusTailCertificate where
  cutoff := Real.log 37
  cutoff_nonneg := Real.log_nonneg (by norm_num)
  prefix_safe := fun _ ht ht37 => suzukiPsi_nonnegative_zero_to_log_thirtySeven ht ht37
  tail_safe := htail

end RHGarden
