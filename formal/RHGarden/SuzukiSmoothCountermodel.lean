import RHGarden.SuzukiRootDynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

NON-ARITHMETIC MODEL. None of b, q, Q, d, W is the actual Chebyshev
function, von Mangoldt sequence, Suzuki discrepancy, or Suzuki reserve.
The model threshold below is NOT a threshold for primes.
-/
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace RHGarden.SmoothCountermodel

def b (x : ℝ) : ℝ := 1 - 1 / (x * (x ^ 2 - 1))
def q (x : ℝ) : ℝ := b x + (1 / 4) * x ^ (-(1 / 4 : ℝ))
def Q (x : ℝ) : ℝ := ∫ y in (2 : ℝ)..x, q y
def d (m d0 x : ℝ) : ℝ := d0 + m ^ (1 / 4 : ℝ) - x ^ (1 / 4 : ℝ)
def W (m R0 d0 x : ℝ) : ℝ :=
  R0 + (d0 + m ^ (1 / 4 : ℝ)) * Real.log (x / m) -
    4 * (x ^ (1 / 4 : ℝ) - m ^ (1 / 4 : ℝ))

theorem b_eq_curvature {x : ℝ} (hx : 0 ≤ x) :
    b x = suzukiCurvatureFactor (Real.sqrt x) := by
  unfold b suzukiCurvatureFactor
  rw [show Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 by ring,
    Real.sq_sqrt hx]

theorem q_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ q x := by
  have hb := five_sixths_le_suzukiCurvatureFactor (Real.sqrt_le_sqrt hx)
  rw [← b_eq_curvature (by linarith : 0 ≤ x)] at hb
  have hr : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  dsimp [q]
  linarith

theorem fourthRoot_fourthPower {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 4) ^ (1 / 4 : ℝ) = x := by
  rw [← Real.rpow_natCast_mul hx]
  norm_num

theorem q_le_201_200 {x : ℝ} (hx : (50 : ℝ) ^ 4 ≤ x) : q x ≤ 201 / 200 := by
  have hx0 : 0 < x := by nlinarith
  have hx2 : 2 ≤ x := by nlinarith
  have hb : b x ≤ 1 := by
    dsimp [b]
    have hs : 0 < x ^ 2 - 1 := by nlinarith
    have : 0 ≤ 1 / (x * (x ^ 2 - 1)) := by positivity
    linarith
  have hroot : 50 ≤ x ^ (1 / 4 : ℝ) := by
    calc
      (50 : ℝ) = ((50 : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
        (fourthRoot_fourthPower (by norm_num)).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hpow : x ^ (-(1 / 4 : ℝ)) ≤ 1 / 50 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hroot
  dsimp [q]
  linarith

theorem continuousOn_q : ContinuousOn q (Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hs : 0 < x ^ 2 - 1 := by nlinarith
  have hden : x * (x ^ 2 - 1) ≠ 0 := by positivity
  exact ((continuousAt_const.sub (continuousAt_const.div
    (continuousAt_id.mul ((continuousAt_id.pow 2).sub continuousAt_const)) hden)).add
    (continuousAt_const.mul (Real.continuousAt_rpow_const x (-(1 / 4 : ℝ))
      (Or.inl hx0.ne')))).continuousWithinAt

/-- This bound holds for every length, but only for the non-arithmetic model. -/
theorem Q_increment_le {a h : ℝ} (ha : (50 : ℝ) ^ 4 ≤ a) (hh : 0 ≤ h) :
    Q (a + h) - Q a ≤ (201 / 200) * h := by
  have ha2 : (2 : ℝ) ≤ a := by nlinarith
  have hab : a ≤ a + h := by linarith
  have hi (u v : ℝ) (hu : 2 ≤ u) (huv : u ≤ v) : IntervalIntegrable q volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact continuousOn_q.mono (fun y hy => hu.trans hy.1)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi 2 a le_rfl ha2) (hi a (a + h) ha2 hab)
  have hbound : (∫ y in a..a + h, q y) ≤ ∫ y in a..a + h, (201 / 200 : ℝ) :=
    intervalIntegral.integral_mono_on hab (hi a (a + h) ha2 hab) intervalIntegrable_const
      (fun y hy => q_le_201_200 (ha.trans hy.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hbound
  dsimp [Q]
  linarith

theorem hasDerivAt_d {m d0 x : ℝ} (hx : 0 < x) :
    HasDerivAt (d m d0) (-(1 / 4 : ℝ) * x ^ (-(3 / 4 : ℝ))) x := by
  have hr := (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl hx.ne')).const_sub
    (d0 + m ^ (1 / 4 : ℝ))
  change HasDerivAt (fun x : ℝ => d0 + m ^ (1 / 4 : ℝ) - x ^ (1 / 4 : ℝ)) _ x
  exact hr.congr_deriv (by norm_num)

theorem d_matches_arrivals {m d0 x : ℝ} (hx : 0 < x) :
    deriv (d m d0) x = (b x - q x) / Real.sqrt x := by
  rw [(hasDerivAt_d hx).deriv]
  rw [q, sub_add_cancel_left, Real.sqrt_eq_rpow]
  rw [neg_div, mul_div_assoc, ← Real.rpow_sub hx]
  norm_num

theorem hasDerivAt_W {m R0 d0 x : ℝ} (hm : 0 < m) (hx : 0 < x) :
    HasDerivAt (W m R0 d0) (d m d0 x / x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl hx.ne')
  have hl := ((hasDerivAt_id x).div_const m).log (div_ne_zero hx.ne' hm.ne')
  have hd := ((hl.const_mul (d0 + m ^ (1 / 4 : ℝ))).const_add R0).sub
    ((hp.sub_const (m ^ (1 / 4 : ℝ))).const_mul 4)
  change HasDerivAt (fun x : ℝ => R0 + (d0 + m ^ (1 / 4 : ℝ)) * Real.log (x / m) -
    4 * (x ^ (1 / 4 : ℝ) - m ^ (1 / 4 : ℝ))) _ x
  apply hd.congr_deriv
  unfold d
  simp only [id_eq]
  rw [Real.rpow_sub hx, Real.rpow_one]
  field_simp [hx.ne', hm.ne']

@[simp] theorem d_initial (m d0 : ℝ) : d m d0 m = d0 := by simp [d]

theorem W_initial {m : ℝ} (hm : 0 < m) (R0 d0 : ℝ) : W m R0 d0 m = R0 := by
  simp [W, hm.ne']

theorem log_one_add_le_cubic {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  let H : ℝ → ℝ := fun v => v - v ^ 2 / 2 + v ^ 3 / 3 - Real.log (1 + v)
  have hd (v : ℝ) (hv : 0 ≤ v) :
      HasDerivAt H (v ^ 3 / (1 + v)) v := by
    have hp : 0 < 1 + v := by linarith
    have hder := (((hasDerivAt_id v).sub (((hasDerivAt_id v).pow 2).div_const 2)).add
      (((hasDerivAt_id v).pow 3).div_const 3)).sub
      (((hasDerivAt_id v).const_add 1).log hp.ne')
    change HasDerivAt (fun v : ℝ => v - v ^ 2 / 2 + v ^ 3 / 3 - Real.log (1 + v)) _ v
    apply hder.congr_deriv
    simp only [id_eq]
    field_simp [hp.ne']
    ring
  have hm : MonotoneOn H (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    (fun v hv => by
      have hv0 : 0 ≤ v := interior_subset hv
      rw [(hd v hv0).deriv]
      positivity)
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) hu hu
  dsimp [H] at hh
  norm_num at hh
  linarith

theorem W_finite_failure :
    W (100 ^ 4) (1 / 100) 0 (101 ^ 4) ≤ -(37 / 3750 : ℝ) := by
  have hlog := log_one_add_le_cubic (by norm_num : (0 : ℝ) ≤ 1 / 100)
  norm_num at hlog
  have he : Real.log ((101 : ℝ) ^ 4 / 100 ^ 4) = 4 * Real.log (101 / 100 : ℝ) := by
    rw [← div_pow, Real.log_pow]
    norm_num
  unfold W
  rw [fourthRoot_fourthPower (by norm_num), fourthRoot_fourthPower (by norm_num), he]
  norm_num
  linarith

theorem finite_width_regime :
    let m : ℕ := 100 ^ 4
    let h : ℕ := 101 ^ 4 - m
    m ^ 2 ≤ h ^ 3 ∧ 8 * h ≤ m ∧ m ^ 3 ≤ h ^ 5 ∧ h ^ 100 ≤ m ^ 99 := by
  norm_num

end RHGarden.SmoothCountermodel
