import RHGarden.SuzukiPrimePowerSurcharge
import Mathlib.NumberTheory.AbelSummation

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Arbitrary-real-endpoint anchored arithmetic loss, without an excursion hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace RHGarden

def suzukiAnchoredError (m : ℕ) (y : ℝ) : ℝ :=
  suzukiChebyshevPsi y - suzukiChebyshevPsi m - (y - m)

def suzukiIntegratedKernel (x y : ℝ) : ℝ :=
  (1 + (1 / 2 : ℝ) * Real.log (x / y)) / (y * Real.sqrt y)

def suzukiLogSqrtWeight (x y : ℝ) : ℝ := Real.log (x / y) / Real.sqrt y

def suzukiAnchoredIntegral (m : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (m : ℝ)..x, suzukiAnchoredError m y * suzukiIntegratedKernel x y

def suzukiIntegratedMainTerm (m : ℕ) (x : ℝ) : ℝ :=
  4 * (Real.sqrt x - Real.sqrt m) - 2 * Real.sqrt m * Real.log (x / m)

def suzukiIntegratedArchDefect (m : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (m : ℝ)..x, suzukiRootArchDefect (Real.sqrt m) (Real.sqrt y) / y

/-- A unit interval may contain a full logarithmic jump: a uniformly small
pure-slope allowance cannot hold at every anchor. -/
theorem anchoredError_prime_predecessor {p : ℕ} (hp : p.Prime) :
    suzukiAnchoredError (p - 1) p = Real.log p - 1 := by
  have hs := Finset.sum_Ioc_succ_top (Nat.zero_le (p - 1)) ArithmeticFunction.vonMangoldt
  rw [Nat.sub_add_cancel hp.one_le, ArithmeticFunction.vonMangoldt_apply_prime hp] at hs
  unfold suzukiAnchoredError suzukiChebyshevPsi
  rw [Nat.floor_natCast, Nat.floor_natCast, hs, Nat.cast_sub hp.one_le]
  norm_num

theorem integratedKernel_eq_rpow {x y : ℝ} (hy : 0 < y) :
    suzukiIntegratedKernel x y = (1 + (1 / 2 : ℝ) * Real.log (x / y)) / y ^ (3 / 2 : ℝ) := by
  have he : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hy]; norm_num
      _ = _ := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [suzukiIntegratedKernel, he]

theorem hasDerivAt_logSqrtWeight {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (suzukiLogSqrtWeight x) (-suzukiIntegratedKernel x y) y := by
  have hs := Real.hasDerivAt_sqrt hy.ne'
  have hl := (Real.hasDerivAt_log hy.ne').const_sub (Real.log x)
  have h := hl.div hs (Real.sqrt_pos.mpr hy).ne'
  have he : suzukiLogSqrtWeight x =ᶠ[nhds y]
      (fun v => (Real.log x - Real.log v) / Real.sqrt v) := by
    filter_upwards [eventually_gt_nhds hy] with v hv
    simp [suzukiLogSqrtWeight, Real.log_div hx.ne' hv.ne']
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [suzukiIntegratedKernel, Real.log_div hx.ne' hy.ne']
  field_simp
  rw [Real.sq_sqrt hy.le]
  ring

theorem continuousOn_integratedKernel {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    ContinuousOn (suzukiIntegratedKernel x) (Icc m x) := by
  intro y hy
  have hy0 : 0 < y := hm.trans_le hy.1
  have hx0 : 0 < x := hm.trans_le hmx
  unfold suzukiIntegratedKernel
  exact ((continuousAt_const.add (continuousAt_const.mul
    ((continuousAt_const.div continuousAt_id hy0.ne').log (div_ne_zero hx0.ne' hy0.ne')))).div
      (continuousAt_id.mul (Real.continuous_sqrt.continuousAt))
      (mul_ne_zero hy0.ne' (Real.sqrt_pos.mpr hy0).ne')).continuousWithinAt

theorem integratedKernel_nonneg {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    0 ≤ suzukiIntegratedKernel x y := by
  apply div_nonneg _ (mul_nonneg hy.le (Real.sqrt_nonneg _))
  have hl : 0 ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy).mpr hyx)
  positivity

theorem integral_integratedKernel {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    (∫ y in m..x, suzukiIntegratedKernel x y) = Real.log (x / m) / Real.sqrt m := by
  have hd (y : ℝ) (hy : y ∈ Icc m x) :=
    (hasDerivAt_logSqrtWeight (hm.trans_le hmx) (hm.trans_le hy.1)).neg
  have hi : IntervalIntegrable (suzukiIntegratedKernel x) volume m x :=
    (continuousOn_integratedKernel hm hmx).intervalIntegrable_of_Icc hmx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => by rw [uIcc_of_le hmx] at hy; simpa using hd y hy) hi
  simpa [suzukiLogSqrtWeight, (hm.trans_le hmx).ne'] using h

theorem integral_linear_integratedKernel {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    (∫ y in m..x, (y - m) * suzukiIntegratedKernel x y) =
      4 * (Real.sqrt x - Real.sqrt m) - 2 * Real.sqrt m * Real.log (x / m) := by
  let F := fun y : ℝ => (y + m) * suzukiLogSqrtWeight x y + 4 * Real.sqrt y
  have hd (y : ℝ) (hy : y ∈ Icc m x) : HasDerivAt F ((y - m) * suzukiIntegratedKernel x y) y := by
    have hy0 : 0 < y := hm.trans_le hy.1
    have h := (((hasDerivAt_id y).add_const m).mul
      (hasDerivAt_logSqrtWeight (hm.trans_le hmx) hy0)).add
        ((Real.hasDerivAt_sqrt hy0.ne').const_mul 4)
    apply h.congr_deriv
    unfold suzukiLogSqrtWeight suzukiIntegratedKernel
    field_simp
    simp only [id_eq]
    ring
  have hi : IntervalIntegrable (fun y => (y - m) * suzukiIntegratedKernel x y) volume m x :=
    ((continuous_id.sub continuous_const).continuousOn.mul
      (continuousOn_integratedKernel hm hmx)).intervalIntegrable_of_Icc hmx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y (by rwa [uIcc_of_le hmx] at hy)) hi]
  dsimp [F, suzukiLogSqrtWeight]
  simp only [div_self (hm.trans_le hmx).ne', Real.log_one, zero_div, mul_zero, zero_add]
  field_simp
  ring_nf
  simp [Real.sq_sqrt hm.le]

theorem integratedMainTerm_nonneg {m : ℕ} {x : ℝ} (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) :
    0 ≤ suzukiIntegratedMainTerm m x := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [suzukiIntegratedMainTerm, ← integral_linear_integratedKernel hm0 hmx]
  exact intervalIntegral.integral_nonneg hmx (fun y hy => mul_nonneg (sub_nonneg.mpr hy.1)
    (integratedKernel_nonneg (hm0.trans_le hy.1) hy.2))

theorem intervalIntegrable_anchoredIntegral {m : ℕ} {x : ℝ} (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) :
    IntervalIntegrable (fun y => suzukiAnchoredError m y * suzukiIntegratedKernel x y) volume m x := by
  have hi : IntervalIntegrable (suzukiAnchoredError m) volume m x :=
    (suzukiChebyshevPsi_mono.intervalIntegrable.sub intervalIntegrable_const).sub
      ((continuous_id.sub continuous_const).intervalIntegrable _ _)
  exact hi.mul_continuousOn (by
    rw [uIcc_of_le hmx]
    exact continuousOn_integratedKernel (by exact_mod_cast hm) hmx)

/-- The signed anchored integral is a finite correctly weighted log-arrival sum minus C. -/
theorem anchoredIntegral_eq_logArrival_sub_main {m : ℕ} {x : ℝ}
    (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) :
    suzukiAnchoredIntegral m x =
      (∑ q ∈ Finset.Ioc m ⌊x⌋₊, ArithmeticFunction.vonMangoldt q /
        Real.sqrt q * Real.log (x / q)) - suzukiIntegratedMainTerm m x := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 := hm0.trans_le hmx
  have hk : IntervalIntegrable (suzukiIntegratedKernel x) volume m x :=
    (continuousOn_integratedKernel hm0 hmx).intervalIntegrable_of_Icc hmx
  have hp : IntervalIntegrable (fun y => suzukiChebyshevPsi y * suzukiIntegratedKernel x y) volume m x :=
    suzukiChebyshevPsi_mono.intervalIntegrable.mul_continuousOn (by
      rw [uIcc_of_le hmx]; exact continuousOn_integratedKernel hm0 hmx)
  have hc := hk.const_mul (suzukiChebyshevPsi m)
  have hl : IntervalIntegrable (fun y => (y - m) * suzukiIntegratedKernel x y) volume m x :=
    ((continuous_id.sub continuous_const).continuousOn.mul
      (continuousOn_integratedKernel hm0 hmx)).intervalIntegrable_of_Icc hmx
  have ha := sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt
    hm0.le hmx (fun y hy => (hasDerivAt_logSqrtWeight hx0 (hm0.trans_le hy.1)).differentiableAt)
    (f := suzukiLogSqrtWeight x) (by
      apply ((continuousOn_integratedKernel hm0 hmx).neg.integrableOn_Icc).congr_fun
      · intro y hy; exact (hasDerivAt_logSqrtWeight hx0 (hm0.trans_le hy.1)).deriv.symm
      · exact measurableSet_Icc)
  rw [Nat.floor_natCast, ← intervalIntegral.integral_of_le hmx] at ha
  have hs (y : ℝ) : (∑ q ∈ Finset.Icc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt q) = suzukiChebyshevPsi y := by
    rw [suzukiChebyshevPsi, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
    simp
  simp_rw [hs] at ha
  have hsm := hs (m : ℝ)
  rw [Nat.floor_natCast] at hsm
  rw [hsm] at ha
  have he : (∫ y in (m : ℝ)..x, deriv (suzukiLogSqrtWeight x) y * suzukiChebyshevPsi y) =
      -(∫ y in (m : ℝ)..x, suzukiChebyshevPsi y * suzukiIntegratedKernel x y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hmx] at hy
    dsimp only
    rw [(hasDerivAt_logSqrtWeight hx0 (hm0.trans_le hy.1)).deriv]
    ring
  rw [he] at ha
  have hi : suzukiAnchoredIntegral m x =
      (∫ y in (m : ℝ)..x, suzukiChebyshevPsi y * suzukiIntegratedKernel x y) -
        suzukiChebyshevPsi m * (Real.log (x / m) / Real.sqrt m) - suzukiIntegratedMainTerm m x := by
    unfold suzukiAnchoredIntegral
    have heq : (fun y => suzukiAnchoredError m y * suzukiIntegratedKernel x y) =
        (fun y => (suzukiChebyshevPsi y * suzukiIntegratedKernel x y -
          suzukiChebyshevPsi m * suzukiIntegratedKernel x y) - (y - m) * suzukiIntegratedKernel x y) := by
      funext y; unfold suzukiAnchoredError; ring
    rw [heq, intervalIntegral.integral_sub (hp.sub hc) hl, intervalIntegral.integral_sub hp hc,
      intervalIntegral.integral_const_mul, integral_integratedKernel hm0 hmx,
      integral_linear_integratedKernel hm0 hmx]
    rfl
  rw [hi]
  have hs' : (∑ q ∈ Finset.Ioc m ⌊x⌋₊, suzukiLogSqrtWeight x q * ArithmeticFunction.vonMangoldt q) =
      ∑ q ∈ Finset.Ioc m ⌊x⌋₊, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (x / q) := by
    apply Finset.sum_congr rfl; intro q hq; unfold suzukiLogSqrtWeight; ring
  rw [hs'] at ha
  simp [suzukiLogSqrtWeight, hx0.ne'] at ha
  linarith

theorem anchoredIntegral_le_accuracy_budget {m : ℕ} {x eta beta : ℝ}
    (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) (_heta : 0 ≤ eta) (_hbeta : 0 ≤ beta)
    (herror : ∀ y ∈ Icc (m : ℝ) x, suzukiAnchoredError m y ≤ eta * (y - m) + beta) :
    suzukiAnchoredIntegral m x ≤ eta * suzukiIntegratedMainTerm m x +
      beta / Real.sqrt m * Real.log (x / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : IntervalIntegrable (suzukiIntegratedKernel x) volume m x :=
    (continuousOn_integratedKernel hm0 hmx).intervalIntegrable_of_Icc hmx
  have hl : IntervalIntegrable (fun y => (y - m) * suzukiIntegratedKernel x y) volume m x :=
    ((continuous_id.sub continuous_const).continuousOn.mul
      (continuousOn_integratedKernel hm0 hmx)).intervalIntegrable_of_Icc hmx
  calc
    _ ≤ ∫ y in (m : ℝ)..x, eta * ((y - m) * suzukiIntegratedKernel x y) + beta * suzukiIntegratedKernel x y := by
      apply intervalIntegral.integral_mono_on hmx (intervalIntegrable_anchoredIntegral hm hmx)
        ((hl.const_mul eta).add (hk.const_mul beta))
      intro y hy
      have h := mul_le_mul_of_nonneg_right (herror y hy)
        (integratedKernel_nonneg (hm0.trans_le hy.1) hy.2)
      nlinarith
    _ = _ := by
      rw [intervalIntegral.integral_add (hl.const_mul eta) (hk.const_mul beta),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_linear_integratedKernel hm0 hmx, integral_integratedKernel hm0 hmx]
      unfold suzukiIntegratedMainTerm
      ring

theorem suzukiPsiRoot_sqrt_eq_arch_sub_logSum {x : ℝ} (hx : 1 ≤ x) :
    suzukiPsiRoot (Real.sqrt x) = suzukiPsiArchimedean (Real.log x) -
      ∑ q ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (x / q) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have he : 2 * Real.log (Real.sqrt x) = Real.log x := by rw [Real.log_sqrt hx0.le]; ring
  rw [suzukiPsiRoot, he, suzukiPsi_eq_primeSide, suzukiPsiPrimeSide,
    abs_of_nonneg (Real.log_nonneg hx), suzukiPsiPrimeSideNonneg,
    suzukiPsiPrimeContribution, Real.exp_log hx0]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [Real.log_div hx0.ne' (by exact_mod_cast (Finset.mem_Ioc.mp hq).1.ne')]

theorem suzukiPsiRoot_sqrt_increment {m : ℕ} {x : ℝ}
    (hm : 1 ≤ m) (hmx : (m : ℝ) ≤ x) :
    suzukiPsiRoot (Real.sqrt x) = suzukiPsiRoot (Real.sqrt m) +
      suzukiPsiArchimedean (Real.log x) - suzukiPsiArchimedean (Real.log m) -
      suzukiMangoldtSlope m * Real.log (x / m) -
        ∑ q ∈ Finset.Ioc m ⌊x⌋₊, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (x / q) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hx0 := hm0.trans_le hmx
  have hmn : m ≤ ⌊x⌋₊ := Nat.le_floor hmx
  have he : (∑ q ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (x / q)) =
      (∑ q ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (m / q)) +
      suzukiMangoldtSlope m * Real.log (x / m) +
      ∑ q ∈ Finset.Ioc m ⌊x⌋₊, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log (x / q) := by
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmn]
    congr 1
    have hsets : Finset.Icc 1 m = Finset.Ioc 0 m := by ext q; simp; omega
    rw [suzukiMangoldtSlope, hsets, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hq).1.ne'
    rw [Real.log_div hx0.ne' hq0, Real.log_div hm0.ne' hq0, Real.log_div hx0.ne' hm0.ne']
    ring
  rw [suzukiPsiRoot_sqrt_eq_arch_sub_logSum (hm1.trans hmx),
    suzukiPsiRoot_sqrt_eq_arch_sub_logSum hm1, Nat.floor_natCast, he]
  ring

theorem hasDerivAt_arch_log {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun v => suzukiPsiArchimedean (Real.log v))
      (suzukiRootArchSlope (Real.sqrt y) / y) y := by
  have he : 2 * Real.log (Real.sqrt y) = Real.log y := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h := hasDerivAt_suzukiPsiArchimedean_of_pos (Real.log_pos hy)
  have hd : HasDerivAt suzukiPsiArchimedean (suzukiRootArchSlope (Real.sqrt y)) (Real.log y) := by
    rw [suzukiRootArchSlope, he, h.deriv]
    exact h
  simpa [Function.comp_def, div_eq_mul_inv] using
    hd.comp y (Real.hasDerivAt_log (by linarith))

theorem integratedArchDefect_eq {m : ℕ} {x : ℝ} (hm : 2 ≤ m) (hmx : (m : ℝ) ≤ x) :
    suzukiIntegratedArchDefect m x = suzukiIntegratedMainTerm m x -
      suzukiPsiArchimedean (Real.log x) + suzukiPsiArchimedean (Real.log m) +
      suzukiRootArchSlope (Real.sqrt m) * Real.log (x / m) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hx0 := hm0.trans_le hmx
  have hr : Real.sqrt 2 ≤ Real.sqrt m := Real.sqrt_le_sqrt hm2
  let F := fun y : ℝ => 4 * Real.sqrt y -
    suzukiPsiArchimedean (Real.log y) +
    (suzukiRootArchSlope (Real.sqrt m) - 2 * Real.sqrt m) * Real.log y
  have hd (y : ℝ) (hy : y ∈ Icc (m : ℝ) x) :
      HasDerivAt F (suzukiRootArchDefect (Real.sqrt m) (Real.sqrt y) / y) y := by
    have hy0 := hm0.trans_le hy.1
    have he := rootService_eq_linear_sub_archDefect hr (Real.sqrt_le_sqrt hy.1)
    unfold suzukiRootService at he
    have hh := (((Real.hasDerivAt_sqrt hy0.ne').const_mul 4).sub
      (hasDerivAt_arch_log (by linarith [hy.1]))).add
        ((Real.hasDerivAt_log hy0.ne').const_mul
          (suzukiRootArchSlope (Real.sqrt m) - 2 * Real.sqrt m))
    apply hh.congr_deriv
    have hyS := Real.sq_sqrt hy0.le
    have hdef : suzukiRootArchDefect (Real.sqrt m) (Real.sqrt y) =
        2 * (Real.sqrt y - Real.sqrt m) - suzukiRootArchSlope (Real.sqrt y) +
          suzukiRootArchSlope (Real.sqrt m) := by linarith
    rw [hdef]
    field_simp
    nlinarith
  have hc : ContinuousOn (fun y => suzukiRootArchDefect (Real.sqrt m) (Real.sqrt y) / y)
      (Icc (m : ℝ) x) := by
    have he : Set.EqOn (fun y => suzukiRootArchDefect (Real.sqrt m) (Real.sqrt y) / y)
        (fun y => (2 * (Real.sqrt y - Real.sqrt m) - suzukiRootArchSlope (Real.sqrt y) +
          suzukiRootArchSlope (Real.sqrt m)) / y) (Icc (m : ℝ) x) := by
      intro y hy
      have h := rootService_eq_linear_sub_archDefect hr (Real.sqrt_le_sqrt hy.1)
      unfold suzukiRootService at h
      dsimp only
      congr 1; linarith
    apply ContinuousOn.congr _ he
    intro y hy
    have hs := (hasDerivAt_suzukiRootArchSlope (hr.trans (Real.sqrt_le_sqrt hy.1))).continuousAt
    exact (((continuousAt_const.mul (Real.continuous_sqrt.continuousAt.sub continuousAt_const)).sub
      (hs.comp Real.continuous_sqrt.continuousAt)).add continuousAt_const).div
        continuousAt_id (hm0.trans_le hy.1).ne' |>.continuousWithinAt
  rw [suzukiIntegratedArchDefect, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y (by rwa [uIcc_of_le hmx] at hy)) (hc.intervalIntegrable_of_Icc hmx)]
  dsimp [F, suzukiIntegratedMainTerm]
  rw [Real.log_div hx0.ne' hm0.ne']
  ring

/-- Arbitrary finite interval, exact signed initial state; no recovery or excursion premise. -/
theorem suzukiPsiRoot_eq_signed_anchoredIntegral {m : ℕ} {x : ℝ}
    (hm : 2 ≤ m) (hmx : (m : ℝ) ≤ x) :
    suzukiPsiRoot (Real.sqrt x) = suzukiPsiRoot (Real.sqrt m) +
      suzukiRootSlopeDiscrepancy (Real.sqrt m) * Real.log (x / m) -
      suzukiIntegratedArchDefect m x - suzukiAnchoredIntegral m x := by
  rw [anchoredIntegral_eq_logArrival_sub_main (by omega) hmx,
    integratedArchDefect_eq hm hmx, suzukiRootSlopeDiscrepancy, suzukiRootMangoldtSlope,
    Real.sq_sqrt (Nat.cast_nonneg m), Nat.floor_natCast,
    suzukiPsiRoot_sqrt_increment (by omega) hmx]
  ring

end RHGarden
