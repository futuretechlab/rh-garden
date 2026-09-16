import RHGarden.SuzukiEventPartition
import RHGarden.SuzukiEventArithmetic
import RHGarden.SuzukiInitialInterval

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.

A concrete certificate on `[sqrt 3,sqrt 5]`, including the prime-square
arrival at 4. Rational bounds are proved from the pinned analytic series.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology Interval
namespace RHGarden

set_option maxHeartbeats 1000000

theorem nineteen_tenths_le_rootArchSlope_deriv {u : ℝ} (hu : Real.sqrt 3 ≤ u) :
    (19 / 10 : ℝ) ≤ deriv suzukiRootArchSlope u := by
  have hu2 : Real.sqrt 2 ≤ u := (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3)).trans hu
  rw [(hasDerivAt_suzukiRootArchSlope hu2).deriv, suzukiCurvatureFactor]
  have hsq : (3 : ℝ) ≤ u ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hfour : (9 : ℝ) ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2 - 3)]
  have hden : (20 : ℝ) ≤ u ^ 2 * (u ^ 4 - 1) := by nlinarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20) hden
  linarith

theorem nineteen_tenths_service_lower {r s : ℝ} (hr : Real.sqrt 3 ≤ r) (hrs : r ≤ s) :
    (19 / 10 : ℝ) * (s - r) ≤ suzukiRootService r s := by
  rcases hrs.eq_or_lt with rfl | hlt
  · simp [suzukiRootService]
  · have hr2 := (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3)).trans hr
    have hc : ContinuousOn suzukiRootArchSlope (Icc r s) := by
      intro u hu
      exact (hasDerivAt_suzukiRootArchSlope (hr2.trans hu.1)).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ suzukiRootArchSlope (Ioo r s) := by
      intro u hu
      exact (hasDerivAt_suzukiRootArchSlope (hr2.trans hu.1.le)).differentiableAt.differentiableWithinAt
    obtain ⟨v, hv, he⟩ := exists_deriv_eq_slope suzukiRootArchSlope hlt hc hd
    have hmul := (eq_div_iff (sub_pos.mpr hlt).ne').mp he
    have hlow := nineteen_tenths_le_rootArchSlope_deriv (hr.trans hv.1.le)
    unfold suzukiRootService
    nlinarith

/-- A per-cell triangle bound for the exact weighted cost. This is an
upper bound, not an exact backlog formula or a whole-period rectangle. -/
theorem exactServiceCellCost_le_quadratic
    {r s K c : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) (hK : 0 ≤ K) (hc : 0 < c)
    (hservice : ∀ u ∈ Icc r s, c * (u - r) ≤ suzukiRootService r u) :
    suzukiExactServiceCellCost r s K ≤ K ^ 2 / (c * r) := by
  let h := suzukiServiceCutoff r s K
  have hcut := suzukiServiceCutoff_spec (K := K) hr hrs
  have hmem : h ∈ Icc r s := hcut.1
  have hr0 : 0 < r := (Real.sqrt_pos.2 (by norm_num)).trans_le hr
  have hcost : suzukiExactServiceCellCost r s K =
      ∫ u in r..h, 2 / u * (K - suzukiRootService r u) := by
    exact (integral_serviceDecay_untruncated hr hmem.1).symm
  by_cases hzero : K = 0
  · have hh : h = r := by
      rcases hcut.2 with hl | hm | hi
      · exact hl.2
      · exact (by linarith [hm.1] : False).elim
      · exact (by linarith [hi.1] : False).elim
    rw [hcost, hh]
    simp [hzero]
  have hpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
  have hSh : suzukiRootService r h ≤ K := by
    rcases hcut.2 with hl | hm | hi
    · linarith [hl.1]
    · simpa only [h, hm.2.2] using hm.2.1
    · exact hi.2.2.le
  have hcont : ContinuousOn (fun u => 2 / u * (K - suzukiRootService r u)) (Icc r h) := by
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (ne_of_gt (hr0.trans_le hu.1))).mul
      (continuousAt_const.sub ((hasDerivAt_suzukiRootArchSlope (hr.trans hu.1)).continuousAt.sub
        continuousAt_const))).continuousWithinAt
  have hupper : Continuous (fun u : ℝ => (2 / r) * (K - c * (u - r))) := by fun_prop
  have hbound : (∫ u in r..h, 2 / u * (K - suzukiRootService r u)) ≤
      ∫ u in r..h, (2 / r) * (K - c * (u - r)) := by
    apply intervalIntegral.integral_mono_on hmem.1
      (hcont.intervalIntegrable_of_Icc hmem.1) (hupper.intervalIntegrable _ _)
    intro u hu
    have hSu : suzukiRootService r u ≤ K :=
      (suzukiRootService_mono_right hr hu.1 hmem.1 hu.2).trans hSh
    have hweight : 2 / u ≤ 2 / r := div_le_div_of_nonneg_left (by norm_num) hr0 hu.1
    have hdecay : K - suzukiRootService r u ≤ K - c * (u - r) :=
      sub_le_sub_left (hservice u ⟨hu.1, hu.2.trans hmem.2⟩) K
    exact (mul_le_mul_of_nonneg_right hweight (sub_nonneg.mpr hSu)).trans
      (mul_le_mul_of_nonneg_left hdecay (div_nonneg (by norm_num) hr0.le))
  have heval : (∫ u in r..h, (2 / r) * (K - c * (u - r))) =
      (2 / r) * (K * (h - r) - c / 2 * (h - r) ^ 2) := by
    have hi1 : IntervalIntegrable (fun u : ℝ => c * (u - r)) volume r h := by
      exact (by fun_prop : Continuous (fun u : ℝ => c * (u - r))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => u) volume r h := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hi1,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hi2 intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [hcost]
  apply hbound.trans
  rw [heval]
  apply (le_div_iff₀ (mul_pos hc hr0)).mpr
  field_simp
  nlinarith [sq_nonneg (K - c * (h - r))]

theorem sqrt_three_mem_rational :
    (173205 : ℝ) / 100000 < Real.sqrt 3 ∧ Real.sqrt 3 < (173206 : ℝ) / 100000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hz := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem exp_half_log_three : Real.exp (Real.log 3 / 2) = Real.sqrt 3 := by
  rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.exp_log (Real.sqrt_pos.2 (by norm_num))]

theorem exp_neg_half_log_three_mem :
    (57735 : ℝ) / 100000 < Real.exp (-Real.log 3 / 2) ∧
      Real.exp (-Real.log 3 / 2) < (57736 : ℝ) / 100000 := by
  rw [show -Real.log 3 / 2 = -(Real.log 3 / 2) by ring,
    Real.exp_neg, exp_half_log_three]
  have hpos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs := sqrt_three_mem_rational
  have hi : (Real.sqrt (3 : ℝ))⁻¹ = Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hi]
  constructor <;> linarith [hs.1, hs.2]

private theorem quarter_value_at_log_three_lower :
    (7866 : ℝ) / 1000 < ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2) *
      (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * Real.log 3)) := by
  let f : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1 / 4) ^ 2) *
    (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * Real.log 3))
  have ht : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * Real.log 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    dsimp [f]
    positivity
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    simpa [sq_abs] using
      (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le hf0 _ hbase
    intro n
    dsimp [f]
    apply mul_le_of_le_one_right (by positivity)
    have he := Real.exp_nonneg (-2 * ((n : ℝ) + 1 / 4) * Real.log 3)
    linarith
  have hpartial := hf.sum_le_tsum (Finset.range 20) (fun n _ => hf0 n)
  have hterm : ∀ n ∈ Finset.range 20,
      (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - ((57736 : ℝ) / 100000) ^ (4 * n + 1)) ≤ f n := by
    intro n _
    have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * Real.log 3) =
        Real.exp (-Real.log 3 / 2) ^ (4 * n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    dsimp [f]
    rw [he]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left
      (pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_half_log_three_mem.2.le _) 1)
        (by positivity)
  have hs := Finset.sum_le_sum hterm
  have hrat : (7866 : ℝ) / 1000 < ∑ n ∈ Finset.range 20,
      (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - ((57736 : ℝ) / 100000) ^ (4 * n + 1)) := by norm_num
  exact hrat.trans_le (hs.trans hpartial)

private theorem quarter_derivative_first_two_lower {t : ℝ} (ht : 0 < t) :
    8 * Real.exp (-t / 2) + (8 / 5 : ℝ) * Real.exp (-t / 2) ^ 5 ≤
      ∑' n : ℕ, (2 / ((n : ℝ) + 1 / 4)) * Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) := by
  let f : ℕ → ℝ := fun n => (2 / ((n : ℝ) + 1 / 4)) *
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)
  have hsum : Summable f := by
    have hg : Summable (fun n : ℕ => 8 * Real.exp (-t / 2) * Real.exp ((n : ℝ) * (-2 * t))) :=
      (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _
    apply Summable.of_nonneg_of_le (fun n => by dsimp [f]; positivity) _ hg
    · intro n
      have hc : 2 / ((n : ℝ) + 1 / 4) ≤ 8 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1 / 4)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      dsimp [f]
      calc
        _ ≤ 8 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
        _ = _ := by
          have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) =
              Real.exp (-t / 2) * Real.exp ((n : ℝ) * (-2 * t)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [he]
          ring
  have hp := hsum.sum_le_tsum (Finset.range 2) (fun n _ => by dsimp [f]; positivity)
  have he : Real.exp (-t / 2) ^ 5 = Real.exp (-5 / 2 * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hp
  have hleft : 8 * Real.exp (-t / 2) + (8 / 5 : ℝ) * Real.exp (-t / 2) ^ 5 = f 0 + f 1 := by
    dsimp [f]
    rw [he]
    norm_num
    congr 1 <;> congr 1 <;> congr 1 <;> ring
  rw [hleft]
  exact hp

theorem mangoldtSlope_two_exact : suzukiMangoldtSlope 2 = Real.log 2 / Real.sqrt 2 := by
  norm_num [suzukiMangoldtSlope, Finset.sum_Icc_succ_top,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

theorem log_two_div_sqrt_two_lt : Real.log 2 / Real.sqrt 2 < (491 : ℝ) / 1000 := by
  rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  have hs := sqrt_two_mem_Ioo_rational.1
  have hl := Real.log_two_lt_d9
  norm_num at hl
  nlinarith

/-- The starting reserve is proved from twenty nonnegative series terms. -/
theorem psiRoot_sqrt_three_reserve : (43 : ℝ) / 1000 ≤ suzukiPsiRoot (Real.sqrt 3) := by
  have hroot : 2 * Real.log (Real.sqrt 3) = Real.log 3 := by
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hpsi := suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
    (n := 2) (t := Real.log 3) (by norm_num)
    (Real.log_le_log (by norm_num) (by norm_num)) (by norm_num)
  have hintercept : suzukiMangoldtIntercept 2 = Real.log 2 * Real.log 2 / Real.sqrt 2 := by
    norm_num [suzukiMangoldtIntercept, Finset.sum_Icc_succ_top,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [suzukiPsiRoot, hroot, hpsi, mangoldtSlope_two_exact, hintercept,
    suzukiPsiArchimedean_eq_quarter_tsum (Real.log_nonneg (by norm_num)), exp_half_log_three]
  have hD := digammaLogPi_mem_Ioo_rational.1
  have hS := quarter_value_at_log_three_lower
  have hw := exp_neg_half_log_three_mem.1
  have hs := sqrt_three_mem_rational.1
  have hl3lo := Real.log_three_gt_d9
  have hl3hi := Real.log_three_lt_d9
  have hl2 := Real.log_two_gt_d9
  norm_num at hl3lo hl3hi hl2 hD hS hw hs
  have hramp : Real.log 2 / Real.sqrt 2 * (Real.log 3 - Real.log 2) < (1991 : ℝ) / 10000 := by
    have hpos : 0 < Real.log 3 - Real.log 2 :=
      sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
    have hmul := mul_lt_mul_of_pos_right log_two_div_sqrt_two_lt hpos
    nlinarith
  have hconst : (-(5391 : ℝ) / 1000) * (Real.log 3 / 2) <
      (Real.log 3 / 2) * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) := by
    nlinarith [mul_pos (by linarith : 0 < Real.log 3 / 2)
      (sub_pos.mpr hD)]
  have heq : Real.log 2 * Real.log 2 / Real.sqrt 2 -
      Real.log 2 / Real.sqrt 2 * Real.log 3 =
      -(Real.log 2 / Real.sqrt 2 * (Real.log 3 - Real.log 2)) := by ring
  norm_num at ⊢
  nlinarith

/-- A rational upper bound for the signed post-3 state, not a reflected
state update. -/
theorem neg_discrepancy_sqrt_three_le :
    -suzukiRootSlopeDiscrepancy (Real.sqrt 3) ≤ (1 / 3 : ℝ) := by
  have hlog : 2 * Real.log (Real.sqrt 3) = Real.log 3 := by
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hslope3 : suzukiMangoldtSlope 3 = Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3 := by
    rw [show 3 = 2 + 1 by norm_num, suzukiMangoldtSlope_succ, mangoldtSlope_two_exact]
    norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  have hl3 : Real.log 3 / Real.sqrt 3 < (635 : ℝ) / 1000 := by
    rw [div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    have hs := sqrt_three_mem_rational.1
    have hl := Real.log_three_lt_d9
    norm_num at hs hl
    nlinarith
  have hderiv := (hasDerivAt_suzukiPsiArchimedean_of_pos
    (Real.log_pos (by norm_num : (1 : ℝ) < 3))).deriv
  rw [suzukiPsiPrimeFreeDerivative_eq_quarter_tsum (Real.log_pos (by norm_num))] at hderiv
  have hD := digammaLogPi_mem_Ioo_rational.1
  have hS := quarter_derivative_first_two_lower (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  have hw := exp_neg_half_log_three_mem
  have hs := sqrt_three_mem_rational.1
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 57735 / 100000) hw.1.le 5
  unfold suzukiRootSlopeDiscrepancy suzukiRootArchSlope suzukiRootMangoldtSlope
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Nat.floor_ofNat, hslope3, hlog,
    hderiv, exp_half_log_three]
  norm_num at hp hD hw hs
  linarith [log_two_div_sqrt_two_lt]

theorem suzuki_eventFree_three_four : IsSuzukiEventFreeCell 3 4 := by
  exact ⟨by norm_num, fun k hk hkr => by omega⟩

theorem suzuki_eventFree_four_five : IsSuzukiEventFreeCell 4 5 := by
  exact ⟨by norm_num, fun k hk hkr => by omega⟩

theorem suzuki_six_not_event : ¬ IsMangoldtEvent 6 := by
  rw [isMangoldtEvent_iff_primePower, isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, _, hp⟩
  have h2 := hp 2 ⟨Nat.prime_two, by norm_num⟩
  have h3 := hp 3 ⟨Nat.prime_three, by norm_num⟩
  omega

/-- Endpoint regression with an actual zero-arrival terminal. -/
theorem signedRootState_terminal_six :
    suzukiSignedRootState 3 (Real.sqrt 6) =
      suzukiSignedRootState 3 (Real.sqrt 5) - suzukiRootService (Real.sqrt 5) (Real.sqrt 6) := by
  exact signedRootState_nonEvent_terminal (m := 3) (q := 5) (r := 6) (by norm_num) (by norm_num)
    ⟨by norm_num, fun k hk hkr => by omega⟩ suzuki_six_not_event

theorem vonMangoldt_four_exact : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
  rw [show 4 = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
  exact ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two

theorem suzuki_sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg (4 : ℝ)]

/-- The prime-square impulse is present in the exact signed recurrence. -/
theorem neg_discrepancy_sqrt_four_le :
    -suzukiRootSlopeDiscrepancy (Real.sqrt 4) ≤ (9 / 50 : ℝ) := by
  have hb := rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess
    (m := 3) (n := 4) (by norm_num) (by norm_num)
  rw [suzukiArrivalServiceExcess,
    weightedMangoldtInterval_eventFree_right suzuki_eventFree_three_four,
    vonMangoldt_four_exact] at hb
  have hs := nineteen_tenths_service_lower (r := Real.sqrt 3) (s := Real.sqrt 4)
    le_rfl (Real.sqrt_le_sqrt (by norm_num))
  have hq := neg_discrepancy_sqrt_three_le
  have hroot := sqrt_three_mem_rational.2
  have hlog := Real.log_two_lt_d9
  norm_num [suzuki_sqrt_four] at hb hs hq hroot hlog ⊢
  linarith

theorem exactCost_three_four_le :
    suzukiExactServiceCellCost (Real.sqrt 3) (Real.sqrt 4)
      (-suzukiRootSlopeDiscrepancy (Real.sqrt 3)) ≤ (34 / 1000 : ℝ) := by
  have hr : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have h34 : Real.sqrt (3 : ℝ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  apply (exactServiceCellCost_mono_state hr h34 neg_discrepancy_sqrt_three_le).trans
  have hcost := exactServiceCellCost_le_quadratic (K := (1 / 3 : ℝ))
    (c := (19 / 10 : ℝ)) hr h34 (by norm_num) (by norm_num)
    (fun u hu => nineteen_tenths_service_lower le_rfl hu.1)
  apply hcost.trans
  rw [div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))]
  have hs := sqrt_three_mem_rational.1
  nlinarith

theorem exactCost_four_five_conservative_le :
    suzukiExactServiceCellCost (Real.sqrt 4) (Real.sqrt 5) (9 / 50) ≤ (9 / 1000 : ℝ) := by
  have hr : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  have h45 : Real.sqrt (4 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  have hcost := exactServiceCellCost_le_quadratic (K := (9 / 50 : ℝ))
    (c := (19 / 10 : ℝ)) hr h45 (by norm_num) (by norm_num)
    (fun u hu => nineteen_tenths_service_lower (Real.sqrt_le_sqrt (by norm_num)) hu.1)
  apply hcost.trans
  norm_num [suzuki_sqrt_four]

def suzukiEventChain_three_five : SuzukiEventChain 3 5 :=
  .cons suzuki_eventFree_three_four (.cons suzuki_eventFree_four_five (.nil 5))

/-- A proved conservative two-cell certificate. In particular its event
bound at 4 is a rational enlargement of the actual signed state; no floating
event table or pre-existing positivity theorem on cell 3 or 4 is used. -/
def suzukiFinitePartitionCertificate_three_five : SuzukiFinitePartitionCertificate where
  anchor := 3
  terminal := 5
  anchor_ge_two := by norm_num
  chain := suzukiEventChain_three_five
  eventUpper := fun q => if q = 3 then 0 else
    suzukiRootSlopeDiscrepancy (Real.sqrt 3) + 9 / 50
  cellCostUpper := fun q _ => if q = 3 then 34 / 1000 else 9 / 1000
  reserve := 43 / 1000
  event_bounds := by
    simp only [suzukiEventChain_three_five, SuzukiEventChain.eventBounds]
    norm_num
    constructor
    · simp [suzukiArrivalServiceExcess, suzukiWeightedMangoldtInterval, suzukiRootService]
    · have hb := rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess
        (m := 3) (n := 4) (by norm_num) (by norm_num)
      have hq := neg_discrepancy_sqrt_four_le
      norm_num at hb hq
      linarith
  cost_bounds := by
    simp only [suzukiEventChain_three_five, SuzukiEventChain.costBounds]
    norm_num
    constructor
    · convert exactCost_three_four_le using 1 <;> norm_num
    · simpa using exactCost_four_five_conservative_le
  reserve_bound := psiRoot_sqrt_three_reserve
  total_safe := by norm_num [suzukiEventChain_three_five, SuzukiEventChain.sumCosts]

theorem suzukiPsiRoot_nonnegative_three_five {u : ℝ}
    (hu : u ∈ Icc (Real.sqrt 3) (Real.sqrt 5)) : 0 ≤ suzukiPsiRoot u := by
  exact suzukiFinitePartitionCertificate_three_five.nonnegative hu

/-- The newly proved finite interval joins the already closed initial
interval. This is finite coverage and supplies no universal tail. -/
theorem suzukiPsi_nonnegative_zero_to_log_five {t : ℝ}
    (ht : 0 ≤ t) (ht5 : t ≤ Real.log 5) : 0 ≤ suzukiPsi t := by
  by_cases ht3 : t ≤ Real.log 3
  · rcases ht.eq_or_lt with rfl | htpos
    · simp
    · exact (suzukiPsi_pos_zero_to_log_three htpos ht3).le
  · have h3 : Real.sqrt 3 ≤ Real.exp (t / 2) := by
      rw [← exp_half_log_three]
      apply Real.exp_le_exp.mpr
      linarith
    have h5 : Real.exp (t / 2) ≤ Real.sqrt 5 := by
      rw [← Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)),
        Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      apply Real.exp_le_exp.mpr
      linarith
    have h := suzukiPsiRoot_nonnegative_three_five ⟨h3, h5⟩
    have hid : 2 * (t / 2) = t := by ring
    simpa [suzukiPsiRoot, Real.log_exp, hid] using h

/-- The prefix field is now a theorem; the independent infinite tail
obligation is left explicit and uninhabited here. -/
def suzukiPrefixFivePlusTail
    (htail : ∀ t, Real.log 5 ≤ t → 0 ≤ suzukiPsi t) : SuzukiExactPrefixPlusTailCertificate where
  cutoff := Real.log 5
  cutoff_nonneg := Real.log_nonneg (by norm_num)
  prefix_safe := fun _ ht ht5 => suzukiPsi_nonnegative_zero_to_log_five ht ht5
  tail_safe := htail

end RHGarden
