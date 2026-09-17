import RHGarden.SuzukiFiniteSieve
import RHGarden.SuzukiAnchoredIntegral

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Instantiated sample-independent bounds for the signed integrated arithmetic functional.
Correctness of these bounds does not assert compatibility with the Suzuki reserve. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

theorem logSqrtWeight_nonneg {m q : ℕ} {x : ℝ} (hm : 1 ≤ m)
    (hq : q ∈ Finset.Ioc m ⌊x⌋₊) : 0 ≤ suzukiLogSqrtWeight x q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := (Finset.mem_Ioc.mp hq).1; omega)
  have hqx : (q : ℝ) ≤ x := (Nat.le_floor_iff (by
    have := (Finset.mem_Ioc.mp hq).2
    have : 0 < ⌊x⌋₊ := by have := (Finset.mem_Ioc.mp hq).1; omega
    exact (by linarith [Nat.floor_pos.mp this]))).mp (Finset.mem_Ioc.mp hq).2
  exact div_nonneg (Real.log_nonneg ((one_le_div hq0).mpr hqx)) (Real.sqrt_nonneg _)

def suzukiSieveIntegralUpper (D : Finset ℕ) (a : ℕ → ℚ) (m : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc m ⌊x⌋₊,
    Real.log n * suzukiLogSqrtWeight x n * suzukiSieveWeight D a n) +
    suzukiAllBasePowerBound m ⌊x⌋₊ (fun n => suzukiLogSqrtWeight x n) -
    suzukiIntegratedMainTerm m x

/-- The finite weighted divisor-square bound, including all-base proper-power overcount.
No future prime/Chebyshev sample, recovery coordinate, or fitted error is a hypothesis. -/
theorem anchoredIntegral_le_sieve {D : Finset ℕ} {a : ℕ → ℚ} {z m : ℕ} {x : ℝ}
    (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z)
    (h1 : 1 ∈ D) (ha : a 1 = 1) (hzm : z ≤ m) :
    suzukiAnchoredIntegral m x ≤ suzukiSieveIntegralUpper D a m x := by
  rw [anchoredIntegral_eq_logArrival_sub_main hm hmx]
  unfold suzukiSieveIntegralUpper
  apply sub_le_sub_right
  have h := weightedMangoldt_le_sieve_add_allBasePowers hD h1 ha hzm
    (fun n => suzukiLogSqrtWeight x n) (fun n hn => logSqrtWeight_nonneg hm hn)
  convert h using 1
  apply Finset.sum_congr rfl
  intro q hq
  unfold suzukiLogSqrtWeight
  ring

def suzukiParityIntegralUpper (m : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc m ⌊x⌋₊, suzukiParityMangoldtUpper n * suzukiLogSqrtWeight x n) -
    suzukiIntegratedMainTerm m x

def suzukiAllIntegerIntegralUpper (m : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc m ⌊x⌋₊, Real.log n * suzukiLogSqrtWeight x n) -
    suzukiIntegratedMainTerm m x

theorem anchoredIntegral_le_parity {m : ℕ} {x : ℝ} (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) :
    suzukiAnchoredIntegral m x ≤ suzukiParityIntegralUpper m x := by
  rw [anchoredIntegral_eq_logArrival_sub_main hm hmx]
  unfold suzukiParityIntegralUpper
  apply sub_le_sub_right
  have h := weightedMangoldt_le_parity (fun n => suzukiLogSqrtWeight x n)
    (fun n hn => logSqrtWeight_nonneg hm hn)
  convert h using 1
  apply Finset.sum_congr rfl
  intro q hq
  unfold suzukiLogSqrtWeight
  ring

theorem parityIntegralUpper_le_baseline {m : ℕ} {x : ℝ} (hm : 1 ≤ m) :
    suzukiParityIntegralUpper m x ≤ suzukiAllIntegerIntegralUpper m x := by
  apply sub_le_sub_right
  apply parity_le_all_integer (fun n hn => by have := (Finset.mem_Ioc.mp hn).1; omega)
    (fun n => suzukiLogSqrtWeight x n) (fun n hn => logSqrtWeight_nonneg hm hn)

/-- Strict improvement whenever a positive-weight even integer greater than two occurs. -/
theorem parityIntegralUpper_lt_baseline {m q : ℕ} {x : ℝ} (hm : 1 ≤ m)
    (hq : q ∈ Finset.Ioc m ⌊x⌋₊) (hq2 : 2 < q) (heven : 2 ∣ q) (hqx : (q : ℝ) < x) :
    suzukiParityIntegralUpper m x < suzukiAllIntegerIntegralUpper m x := by
  apply sub_lt_sub_right
  apply Finset.sum_lt_sum
  · intro n hn
    apply mul_le_mul_of_nonneg_right _ (logSqrtWeight_nonneg hm hn)
    unfold suzukiParityMangoldtUpper
    split_ifs
    · exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by have := (Finset.mem_Ioc.mp hn).1; omega))
    · rfl
  · refine ⟨q, hq, ?_⟩
    rw [suzukiParityMangoldtUpper, if_pos heven]
    apply mul_lt_mul_of_pos_right (Real.log_lt_log (by norm_num) (by exact_mod_cast hq2))
    apply div_pos (Real.log_pos ((one_lt_div (by exact_mod_cast (show 0 < q by omega))).mpr hqx))
    exact Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))

/-- Actual proof term for a fixed effective bound, not a field in a certificate. -/
theorem anchoredIntegral_ten_fifteen_le_parity :
    suzukiAnchoredIntegral 10 15 ≤ suzukiParityIntegralUpper 10 15 :=
  anchoredIntegral_le_parity (by norm_num) (by norm_num)

theorem parity_ten_fifteen_strictly_improves_baseline :
    suzukiParityIntegralUpper 10 15 < suzukiAllIntegerIntegralUpper 10 15 := by
  apply parityIntegralUpper_lt_baseline (q := 12) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- A second, sharper concrete rational divisor-square instance. Proper powers are
handled by the proved all-base bound, not by inspecting the local prime table. -/
theorem anchoredIntegral_ten_fifteen_le_sieve :
    suzukiAnchoredIntegral 10 15 ≤
      suzukiSieveIntegralUpper {1, 2} suzukiParitySieveCoeff 10 15 := by
  apply anchoredIntegral_le_sieve (z := 2) (by norm_num) (by norm_num)
    (by intro d hd; simp at hd; rcases hd with rfl | rfl <;> norm_num)
    (by simp) (by simp [suzukiParitySieveCoeff]) (by norm_num)

theorem allBasePowerBound_ten_fifteen (w : ℕ → ℝ) : suzukiAllBasePowerBound 10 15 w = 0 := by
  norm_num [suzukiAllBasePowerBound, show Nat.log 2 15 = 3 by decide,
    show Finset.Icc 2 3 = {2, 3} by decide,
    show Finset.Icc 2 15 = {2,3,4,5,6,7,8,9,10,11,12,13,14,15} by decide]

theorem sieveIntegralUpper_ten_fifteen_eq :
    suzukiSieveIntegralUpper {1, 2} suzukiParitySieveCoeff 10 15 =
      Real.log 11 / Real.sqrt 11 * Real.log (15 / 11 : ℝ) +
      Real.log 13 / Real.sqrt 13 * Real.log (15 / 13 : ℝ) - suzukiIntegratedMainTerm 10 15 := by
  rw [suzukiSieveIntegralUpper]
  norm_num only [Nat.floor_ofNat]
  rw [allBasePowerBound_ten_fifteen]
  norm_num [show Finset.Ioc 10 15 = {11,12,13,14,15} by decide,
    suzukiParitySieveWeight, suzukiLogSqrtWeight]
  ring

theorem sieve_ten_fifteen_strictly_improves_baseline :
    suzukiSieveIntegralUpper {1, 2} suzukiParitySieveCoeff 10 15 <
      suzukiAllIntegerIntegralUpper 10 15 := by
  apply lt_of_le_of_lt _ parity_ten_fifteen_strictly_improves_baseline
  unfold suzukiSieveIntegralUpper suzukiParityIntegralUpper
  norm_num only [Nat.floor_ofNat]
  rw [allBasePowerBound_ten_fifteen, add_zero]
  apply sub_le_sub_right
  apply Finset.sum_le_sum
  intro n hn
  rw [suzukiParitySieveWeight, suzukiParityMangoldtUpper]
  split_ifs
  · rw [mul_zero]
    exact mul_nonneg (Real.log_nonneg (by norm_num))
      (logSqrtWeight_nonneg (by norm_num : 1 ≤ 10) (by simpa using hn))
  · rw [mul_one]

end RHGarden
