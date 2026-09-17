import RHGarden.SuzukiRationalBounds
import RHGarden.SuzukiPrimePowerSurcharge
import Mathlib.Tactic.NormNum.Prime

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite rational data below are checked by Lean, not imported numerical facts.
The generating decimals only select rational candidates; every enclosure has
a proof term using the logarithm series, square identities, and rational arithmetic. -/
noncomputable section
open Set
open scoped BigOperators
namespace RHGarden
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem log_scaled_bounds {x l h : ℝ} (k : ℕ) {a b : ℝ}
    (he : x = 2 ^ k * (x / 2 ^ k))
    (hy : a ≤ Real.log (x / 2 ^ k) ∧ Real.log (x / 2 ^ k) ≤ b)
    (hx : 0 < x) (hl : l ≤ k * (693147180 / 1000000000 : ℝ) + a)
    (hh : k * (693147181 / 1000000000 : ℝ) + b ≤ h) :
    l ≤ Real.log x ∧ Real.log x ≤ h := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have he' : Real.log x = (k : ℝ) * Real.log 2 + Real.log (x / 2 ^ k) := by
    calc
      Real.log x = Real.log (2 ^ k * (x / 2 ^ k)) := congrArg Real.log he
      _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rw [he']
  have hl' := mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg (α := ℝ) k)
  have hh' := mul_le_mul_of_nonneg_left h2'.le (Nat.cast_nonneg (α := ℝ) k)
  constructor <;> linarith [hy.1, hy.2]

private theorem quotient_enclosure {x y l h a b c d : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hc : 0 < c) (hl0 : 0 ≤ l) (hh0 : 0 ≤ h)
    (hl : l * d ≤ a) (hh : b ≤ h * c) :
    l ≤ x / y ∧ x / y ≤ h := by
  have hp : 0 < y := hc.trans_le hy.1
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact (mul_le_mul_of_nonneg_left hy.2 hl0).trans (hl.trans hx.1)
  · apply (div_le_iff₀ hp).mpr
    exact hx.2.trans (hh.trans (mul_le_mul_of_nonneg_left hy.1 hh0))

private theorem product_enclosure {x y l h a b c d : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hl : l ≤ a * c) (hh : b * d ≤ h) :
    l ≤ x * y ∧ x * y ≤ h := by
  constructor
  · exact hl.trans (mul_le_mul hx.1 hy.1 hc (ha.trans hx.1))
  · exact (mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans hx.1 |>.trans hx.2)).trans hh

theorem finite_log_2 : (69314717 : ℝ) / 100000000 ≤ Real.log (2) ∧ Real.log (2) ≤ (69314720 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (0 : ℝ) / 1000000000) (b := (1 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_3 : (109861227 : ℝ) / 100000000 ≤ Real.log (3) ∧ Real.log (3) ≤ (109861230 : ℝ) / 100000000 := by
  apply log_scaled_bounds 1 (a := (405465108 : ℝ) / 1000000000) (b := (405465109 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_4 : (138629435 : ℝ) / 100000000 ≤ Real.log (4) ∧ Real.log (4) ≤ (138629438 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (0 : ℝ) / 1000000000) (b := (1 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_5 : (160943790 : ℝ) / 100000000 ≤ Real.log (5) ∧ Real.log (5) ≤ (160943793 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (223143551 : ℝ) / 1000000000) (b := (223143552 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_7 : (194591013 : ℝ) / 100000000 ≤ Real.log (7) ∧ Real.log (7) ≤ (194591016 : ℝ) / 100000000 := by
  apply log_scaled_bounds 2 (a := (559615787 : ℝ) / 1000000000) (b := (559615788 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_8 : (207944153 : ℝ) / 100000000 ≤ Real.log (8) ∧ Real.log (8) ≤ (207944156 : ℝ) / 100000000 := by
  apply log_scaled_bounds 3 (a := (0 : ℝ) / 1000000000) (b := (1 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_9 : (219722456 : ℝ) / 100000000 ≤ Real.log (9) ∧ Real.log (9) ≤ (219722459 : ℝ) / 100000000 := by
  apply log_scaled_bounds 3 (a := (117783035 : ℝ) / 1000000000) (b := (117783036 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_11 : (239789526 : ℝ) / 100000000 ≤ Real.log (11) ∧ Real.log (11) ≤ (239789529 : ℝ) / 100000000 := by
  apply log_scaled_bounds 3 (a := (318453731 : ℝ) / 1000000000) (b := (318453732 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_13 : (256494934 : ℝ) / 100000000 ≤ Real.log (13) ∧ Real.log (13) ≤ (256494937 : ℝ) / 100000000 := by
  apply log_scaled_bounds 3 (a := (485507815 : ℝ) / 1000000000) (b := (485507816 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_16 : (277258871 : ℝ) / 100000000 ≤ Real.log (16) ∧ Real.log (16) ≤ (277258874 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (0 : ℝ) / 1000000000) (b := (1 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_17 : (283321333 : ℝ) / 100000000 ≤ Real.log (17) ∧ Real.log (17) ≤ (283321336 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (60624621 : ℝ) / 1000000000) (b := (60624622 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_19 : (294443896 : ℝ) / 100000000 ≤ Real.log (19) ∧ Real.log (19) ≤ (294443899 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (171850256 : ℝ) / 1000000000) (b := (171850257 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_23 : (313549420 : ℝ) / 100000000 ≤ Real.log (23) ∧ Real.log (23) ≤ (313549423 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (362905493 : ℝ) / 1000000000) (b := (362905494 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_25 : (321887581 : ℝ) / 100000000 ≤ Real.log (25) ∧ Real.log (25) ≤ (321887584 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (446287102 : ℝ) / 1000000000) (b := (446287103 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_27 : (329583685 : ℝ) / 100000000 ≤ Real.log (27) ∧ Real.log (27) ≤ (329583688 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (523248143 : ℝ) / 1000000000) (b := (523248144 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_29 : (336729581 : ℝ) / 100000000 ≤ Real.log (29) ∧ Real.log (29) ≤ (336729584 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (594707107 : ℝ) / 1000000000) (b := (594707108 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_31 : (343398719 : ℝ) / 100000000 ≤ Real.log (31) ∧ Real.log (31) ≤ (343398722 : ℝ) / 100000000 := by
  apply log_scaled_bounds 4 (a := (661398482 : ℝ) / 1000000000) (b := (661398483 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_32 : (346573589 : ℝ) / 100000000 ≤ Real.log (32) ∧ Real.log (32) ≤ (346573592 : ℝ) / 100000000 := by
  apply log_scaled_bounds 5 (a := (0 : ℝ) / 1000000000) (b := (1 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_log_37 : (361091790 : ℝ) / 100000000 ≤ Real.log (37) ∧ Real.log (37) ≤ (361091793 : ℝ) / 100000000 := by
  apply log_scaled_bounds 5 (a := (145182009 : ℝ) / 1000000000) (b := (145182010 : ℝ) / 1000000000)
  · norm_num
  · apply log_rational_bounds (by norm_num) 12 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem finite_sqrt_2 : (141421356 : ℝ) / 100000000 ≤ Real.sqrt (2 : ℝ) ∧
    Real.sqrt (2 : ℝ) ≤ (141421357 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_2 :
    (4901289 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 ∧
    ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 ≤ (4901292 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    rw [show 2 = 2 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_2 finite_sqrt_2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_2 :
    (339730 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 2 * Real.log 2 / Real.sqrt 2 ∧
    ArithmeticFunction.vonMangoldt 2 * Real.log 2 / Real.sqrt 2 ≤ (339734 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 2 * Real.log 2 / Real.sqrt 2 =
    (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) * Real.log 2 by ring]
  exact product_enclosure finite_weight_2 finite_log_2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_3 : (173205080 : ℝ) / 100000000 ≤ Real.sqrt (3 : ℝ) ∧
    Real.sqrt (3 : ℝ) ≤ (173205081 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_3 :
    (6342840 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 ∧
    ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 ≤ (6342843 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    rw [show 3 = 3 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_3 finite_sqrt_3 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_3 :
    (696831 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 3 * Real.log 3 / Real.sqrt 3 ∧
    ArithmeticFunction.vonMangoldt 3 * Real.log 3 / Real.sqrt 3 ≤ (696835 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 3 * Real.log 3 / Real.sqrt 3 =
    (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3) * Real.log 3 by ring]
  exact product_enclosure finite_weight_3 finite_log_3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_4 : (200000000 : ℝ) / 100000000 ≤ Real.sqrt (4 : ℝ) ∧
    Real.sqrt (4 : ℝ) ≤ (200000001 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
  have hp := Real.sqrt_nonneg (4 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_4 :
    (3465734 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 4 / Real.sqrt 4 ∧
    ArithmeticFunction.vonMangoldt 4 / Real.sqrt 4 ≤ (3465737 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show 4 = 2 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_2 finite_sqrt_4 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_4 :
    (480452 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 4 * Real.log 4 / Real.sqrt 4 ∧
    ArithmeticFunction.vonMangoldt 4 * Real.log 4 / Real.sqrt 4 ≤ (480456 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 4 * Real.log 4 / Real.sqrt 4 =
    (ArithmeticFunction.vonMangoldt 4 / Real.sqrt 4) * Real.log 4 by ring]
  exact product_enclosure finite_weight_4 finite_log_4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_5 : (223606797 : ℝ) / 100000000 ≤ Real.sqrt (5 : ℝ) ∧
    Real.sqrt (5 : ℝ) ≤ (223606798 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_5 :
    (7197624 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 5 / Real.sqrt 5 ∧
    ArithmeticFunction.vonMangoldt 5 / Real.sqrt 5 ≤ (7197627 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    rw [show 5 = 5 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_5 finite_sqrt_5 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_5 :
    (1158412 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 5 * Real.log 5 / Real.sqrt 5 ∧
    ArithmeticFunction.vonMangoldt 5 * Real.log 5 / Real.sqrt 5 ≤ (1158416 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 5 * Real.log 5 / Real.sqrt 5 =
    (ArithmeticFunction.vonMangoldt 5 / Real.sqrt 5) * Real.log 5 by ring]
  exact product_enclosure finite_weight_5 finite_log_5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_7 : (264575131 : ℝ) / 100000000 ≤ Real.sqrt (7 : ℝ) ∧
    Real.sqrt (7 : ℝ) ≤ (264575132 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  have hp := Real.sqrt_nonneg (7 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_7 :
    (7354848 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 7 / Real.sqrt 7 ∧
    ArithmeticFunction.vonMangoldt 7 / Real.sqrt 7 ≤ (7354851 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    rw [show 7 = 7 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_7 finite_sqrt_7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_7 :
    (1431186 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 7 * Real.log 7 / Real.sqrt 7 ∧
    ArithmeticFunction.vonMangoldt 7 * Real.log 7 / Real.sqrt 7 ≤ (1431190 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 7 * Real.log 7 / Real.sqrt 7 =
    (ArithmeticFunction.vonMangoldt 7 / Real.sqrt 7) * Real.log 7 by ring]
  exact product_enclosure finite_weight_7 finite_log_7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_8 : (282842712 : ℝ) / 100000000 ≤ Real.sqrt (8 : ℝ) ∧
    Real.sqrt (8 : ℝ) ≤ (282842713 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  have hp := Real.sqrt_nonneg (8 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_8 :
    (2450644 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 8 / Real.sqrt 8 ∧
    ArithmeticFunction.vonMangoldt 8 / Real.sqrt 8 ≤ (2450647 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show 8 = 2 ^ 3 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_2 finite_sqrt_8 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_8 :
    (509596 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 8 * Real.log 8 / Real.sqrt 8 ∧
    ArithmeticFunction.vonMangoldt 8 * Real.log 8 / Real.sqrt 8 ≤ (509600 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 8 * Real.log 8 / Real.sqrt 8 =
    (ArithmeticFunction.vonMangoldt 8 / Real.sqrt 8) * Real.log 8 by ring]
  exact product_enclosure finite_weight_8 finite_log_8 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_9 : (300000000 : ℝ) / 100000000 ≤ Real.sqrt (9 : ℝ) ∧
    Real.sqrt (9 : ℝ) ≤ (300000001 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)
  have hp := Real.sqrt_nonneg (9 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_9 :
    (3662039 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 9 / Real.sqrt 9 ∧
    ArithmeticFunction.vonMangoldt 9 / Real.sqrt 9 ≤ (3662042 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show 9 = 3 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_3 finite_sqrt_9 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_9 :
    (804631 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 9 * Real.log 9 / Real.sqrt 9 ∧
    ArithmeticFunction.vonMangoldt 9 * Real.log 9 / Real.sqrt 9 ≤ (804635 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 9 * Real.log 9 / Real.sqrt 9 =
    (ArithmeticFunction.vonMangoldt 9 / Real.sqrt 9) * Real.log 9 by ring]
  exact product_enclosure finite_weight_9 finite_log_9 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_11 : (331662479 : ℝ) / 100000000 ≤ Real.sqrt (11 : ℝ) ∧
    Real.sqrt (11 : ℝ) ≤ (331662480 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
  have hp := Real.sqrt_nonneg (11 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_11 :
    (7229925 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 11 / Real.sqrt 11 ∧
    ArithmeticFunction.vonMangoldt 11 / Real.sqrt 11 ≤ (7229928 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
    rw [show 11 = 11 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_11 finite_sqrt_11 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_11 :
    (1733659 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 11 * Real.log 11 / Real.sqrt 11 ∧
    ArithmeticFunction.vonMangoldt 11 * Real.log 11 / Real.sqrt 11 ≤ (1733663 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 11 * Real.log 11 / Real.sqrt 11 =
    (ArithmeticFunction.vonMangoldt 11 / Real.sqrt 11) * Real.log 11 by ring]
  exact product_enclosure finite_weight_11 finite_log_11 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_13 : (360555127 : ℝ) / 100000000 ≤ Real.sqrt (13 : ℝ) ∧
    Real.sqrt (13 : ℝ) ≤ (360555128 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hp := Real.sqrt_nonneg (13 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_13 :
    (7113888 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 13 / Real.sqrt 13 ∧
    ArithmeticFunction.vonMangoldt 13 / Real.sqrt 13 ≤ (7113891 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
    rw [show 13 = 13 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_13 finite_sqrt_13 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_13 :
    (1824675 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 13 * Real.log 13 / Real.sqrt 13 ∧
    ArithmeticFunction.vonMangoldt 13 * Real.log 13 / Real.sqrt 13 ≤ (1824679 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 13 * Real.log 13 / Real.sqrt 13 =
    (ArithmeticFunction.vonMangoldt 13 / Real.sqrt 13) * Real.log 13 by ring]
  exact product_enclosure finite_weight_13 finite_log_13 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_16 : (400000000 : ℝ) / 100000000 ≤ Real.sqrt (16 : ℝ) ∧
    Real.sqrt (16 : ℝ) ≤ (400000001 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 16 by norm_num)
  have hp := Real.sqrt_nonneg (16 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_16 :
    (1732866 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 16 / Real.sqrt 16 ∧
    ArithmeticFunction.vonMangoldt 16 / Real.sqrt 16 ≤ (1732869 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    rw [show 16 = 2 ^ 4 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_2 finite_sqrt_16 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_16 :
    (480452 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 16 * Real.log 16 / Real.sqrt 16 ∧
    ArithmeticFunction.vonMangoldt 16 * Real.log 16 / Real.sqrt 16 ≤ (480456 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 16 * Real.log 16 / Real.sqrt 16 =
    (ArithmeticFunction.vonMangoldt 16 / Real.sqrt 16) * Real.log 16 by ring]
  exact product_enclosure finite_weight_16 finite_log_16 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_17 : (412310562 : ℝ) / 100000000 ≤ Real.sqrt (17 : ℝ) ∧
    Real.sqrt (17 : ℝ) ≤ (412310563 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have hp := Real.sqrt_nonneg (17 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_17 :
    (6871550 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 17 / Real.sqrt 17 ∧
    ArithmeticFunction.vonMangoldt 17 / Real.sqrt 17 ≤ (6871553 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
    rw [show 17 = 17 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_17 finite_sqrt_17 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_17 :
    (1946856 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 17 * Real.log 17 / Real.sqrt 17 ∧
    ArithmeticFunction.vonMangoldt 17 * Real.log 17 / Real.sqrt 17 ≤ (1946860 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 17 * Real.log 17 / Real.sqrt 17 =
    (ArithmeticFunction.vonMangoldt 17 / Real.sqrt 17) * Real.log 17 by ring]
  exact product_enclosure finite_weight_17 finite_log_17 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_19 : (435889894 : ℝ) / 100000000 ≤ Real.sqrt (19 : ℝ) ∧
    Real.sqrt (19 : ℝ) ≤ (435889895 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num)
  have hp := Real.sqrt_nonneg (19 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_19 :
    (6755005 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 19 / Real.sqrt 19 ∧
    ArithmeticFunction.vonMangoldt 19 / Real.sqrt 19 ≤ (6755008 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
    rw [show 19 = 19 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_19 finite_sqrt_19 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_19 :
    (1988969 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 19 * Real.log 19 / Real.sqrt 19 ∧
    ArithmeticFunction.vonMangoldt 19 * Real.log 19 / Real.sqrt 19 ≤ (1988973 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 19 * Real.log 19 / Real.sqrt 19 =
    (ArithmeticFunction.vonMangoldt 19 / Real.sqrt 19) * Real.log 19 by ring]
  exact product_enclosure finite_weight_19 finite_log_19 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_23 : (479583152 : ℝ) / 100000000 ≤ Real.sqrt (23 : ℝ) ∧
    Real.sqrt (23 : ℝ) ≤ (479583153 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
  have hp := Real.sqrt_nonneg (23 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_23 :
    (6537956 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 23 / Real.sqrt 23 ∧
    ArithmeticFunction.vonMangoldt 23 / Real.sqrt 23 ≤ (6537959 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
    rw [show 23 = 23 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_23 finite_sqrt_23 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_23 :
    (2049971 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 23 * Real.log 23 / Real.sqrt 23 ∧
    ArithmeticFunction.vonMangoldt 23 * Real.log 23 / Real.sqrt 23 ≤ (2049975 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 23 * Real.log 23 / Real.sqrt 23 =
    (ArithmeticFunction.vonMangoldt 23 / Real.sqrt 23) * Real.log 23 by ring]
  exact product_enclosure finite_weight_23 finite_log_23 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_25 : (500000000 : ℝ) / 100000000 ≤ Real.sqrt (25 : ℝ) ∧
    Real.sqrt (25 : ℝ) ≤ (500000001 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)
  have hp := Real.sqrt_nonneg (25 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_25 :
    (3218874 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 25 / Real.sqrt 25 ∧
    ArithmeticFunction.vonMangoldt 25 / Real.sqrt 25 ≤ (3218877 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
    rw [show 25 = 5 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_5 finite_sqrt_25 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_25 :
    (1036115 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 25 * Real.log 25 / Real.sqrt 25 ∧
    ArithmeticFunction.vonMangoldt 25 * Real.log 25 / Real.sqrt 25 ≤ (1036119 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 25 * Real.log 25 / Real.sqrt 25 =
    (ArithmeticFunction.vonMangoldt 25 / Real.sqrt 25) * Real.log 25 by ring]
  exact product_enclosure finite_weight_25 finite_log_25 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_27 : (519615242 : ℝ) / 100000000 ≤ Real.sqrt (27 : ℝ) ∧
    Real.sqrt (27 : ℝ) ≤ (519615243 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 27 by norm_num)
  have hp := Real.sqrt_nonneg (27 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_27 :
    (2114279 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 27 / Real.sqrt 27 ∧
    ArithmeticFunction.vonMangoldt 27 / Real.sqrt 27 ≤ (2114282 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
    rw [show 27 = 3 ^ 3 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_3 finite_sqrt_27 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_27 :
    (696831 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 27 * Real.log 27 / Real.sqrt 27 ∧
    ArithmeticFunction.vonMangoldt 27 * Real.log 27 / Real.sqrt 27 ≤ (696835 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 27 * Real.log 27 / Real.sqrt 27 =
    (ArithmeticFunction.vonMangoldt 27 / Real.sqrt 27) * Real.log 27 by ring]
  exact product_enclosure finite_weight_27 finite_log_27 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_29 : (538516480 : ℝ) / 100000000 ≤ Real.sqrt (29 : ℝ) ∧
    Real.sqrt (29 : ℝ) ≤ (538516481 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hp := Real.sqrt_nonneg (29 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_29 :
    (6252910 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 29 / Real.sqrt 29 ∧
    ArithmeticFunction.vonMangoldt 29 / Real.sqrt 29 ≤ (6252913 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
    rw [show 29 = 29 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_29 finite_sqrt_29 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_29 :
    (2105539 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 29 * Real.log 29 / Real.sqrt 29 ∧
    ArithmeticFunction.vonMangoldt 29 * Real.log 29 / Real.sqrt 29 ≤ (2105543 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 29 * Real.log 29 / Real.sqrt 29 =
    (ArithmeticFunction.vonMangoldt 29 / Real.sqrt 29) * Real.log 29 by ring]
  exact product_enclosure finite_weight_29 finite_log_29 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_31 : (556776436 : ℝ) / 100000000 ≤ Real.sqrt (31 : ℝ) ∧
    Real.sqrt (31 : ℝ) ≤ (556776437 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 31 by norm_num)
  have hp := Real.sqrt_nonneg (31 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_31 :
    (6167622 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 31 / Real.sqrt 31 ∧
    ArithmeticFunction.vonMangoldt 31 / Real.sqrt 31 ≤ (6167625 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
    rw [show 31 = 31 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_31 finite_sqrt_31 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_31 :
    (2117952 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 31 * Real.log 31 / Real.sqrt 31 ∧
    ArithmeticFunction.vonMangoldt 31 * Real.log 31 / Real.sqrt 31 ≤ (2117956 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 31 * Real.log 31 / Real.sqrt 31 =
    (ArithmeticFunction.vonMangoldt 31 / Real.sqrt 31) * Real.log 31 by ring]
  exact product_enclosure finite_weight_31 finite_log_31 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_32 : (565685424 : ℝ) / 100000000 ≤ Real.sqrt (32 : ℝ) ∧
    Real.sqrt (32 : ℝ) ≤ (565685425 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 32 by norm_num)
  have hp := Real.sqrt_nonneg (32 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_32 :
    (1225321 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 32 / Real.sqrt 32 ∧
    ArithmeticFunction.vonMangoldt 32 / Real.sqrt 32 ≤ (1225324 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
    rw [show 32 = 2 ^ 5 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_2 finite_sqrt_32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_32 :
    (424663 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 32 * Real.log 32 / Real.sqrt 32 ∧
    ArithmeticFunction.vonMangoldt 32 * Real.log 32 / Real.sqrt 32 ≤ (424667 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 32 * Real.log 32 / Real.sqrt 32 =
    (ArithmeticFunction.vonMangoldt 32 / Real.sqrt 32) * Real.log 32 by ring]
  exact product_enclosure finite_weight_32 finite_log_32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem finite_sqrt_37 : (608276253 : ℝ) / 100000000 ≤ Real.sqrt (37 : ℝ) ∧
    Real.sqrt (37 : ℝ) ≤ (608276254 : ℝ) / 100000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 37 by norm_num)
  have hp := Real.sqrt_nonneg (37 : ℝ)
  constructor <;> nlinarith

theorem finite_weight_37 :
    (5936311 : ℝ) / 10000000 ≤ ArithmeticFunction.vonMangoldt 37 / Real.sqrt 37 ∧
    ArithmeticFunction.vonMangoldt 37 / Real.sqrt 37 ≤ (5936314 : ℝ) / 10000000 := by
  have he : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
    rw [show 37 = 37 ^ 1 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    norm_num
  rw [he]
  exact quotient_enclosure finite_log_37 finite_sqrt_37 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem finite_intercept_37 :
    (2143552 : ℝ) / 1000000 ≤ ArithmeticFunction.vonMangoldt 37 * Real.log 37 / Real.sqrt 37 ∧
    ArithmeticFunction.vonMangoldt 37 * Real.log 37 / Real.sqrt 37 ≤ (2143556 : ℝ) / 1000000 := by
  rw [show ArithmeticFunction.vonMangoldt 37 * Real.log 37 / Real.sqrt 37 =
    (ArithmeticFunction.vonMangoldt 37 / Real.sqrt 37) * Real.log 37 by ring]
  exact product_enclosure finite_weight_37 finite_log_37 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem vonMangoldt_zero_of_two_prime_divisors {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) (hne : p ≠ q) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg]
  intro h
  obtain ⟨r, _, hr⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  exact hne ((hr p ⟨hp, hpn⟩).trans (hr q ⟨hq, hqn⟩).symm)

theorem small_zero_1 : ArithmeticFunction.vonMangoldt 1 = 0 := by
  simp

theorem small_zero_6 : ArithmeticFunction.vonMangoldt 6 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_10 : ArithmeticFunction.vonMangoldt 10 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_12 : ArithmeticFunction.vonMangoldt 12 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_14 : ArithmeticFunction.vonMangoldt 14 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_15 : ArithmeticFunction.vonMangoldt 15 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_18 : ArithmeticFunction.vonMangoldt 18 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_20 : ArithmeticFunction.vonMangoldt 20 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_21 : ArithmeticFunction.vonMangoldt 21 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 3) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_22 : ArithmeticFunction.vonMangoldt 22 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_24 : ArithmeticFunction.vonMangoldt 24 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_26 : ArithmeticFunction.vonMangoldt 26 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 13)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_28 : ArithmeticFunction.vonMangoldt 28 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_30 : ArithmeticFunction.vonMangoldt 30 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_33 : ArithmeticFunction.vonMangoldt 33 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 3) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_34 : ArithmeticFunction.vonMangoldt 34 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 17)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_35 : ArithmeticFunction.vonMangoldt 35 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem small_zero_36 : ArithmeticFunction.vonMangoldt 36 = 0 := by
  exact vonMangoldt_zero_of_two_prime_divisors (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)


end RHGarden
