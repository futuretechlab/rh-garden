import RHGarden.SuzukiEventArithmetic

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Exact prime-power substitution surcharge. All endpoints below are real
root coordinates, not last-event or next-event labels. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace RHGarden

def suzukiPrimePowerOvercharge (q : ℕ) : ℝ := by
  classical
  exact if IsMangoldtEvent q then
    (Real.log q - ArithmeticFunction.vonMangoldt q) / Real.sqrt q else 0

theorem suzukiPrimePowerOvercharge_nonneg (q : ℕ) :
    0 ≤ suzukiPrimePowerOvercharge q := by
  unfold suzukiPrimePowerOvercharge
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log)
      (Real.sqrt_nonneg _)
  · rfl

theorem suzukiPrimePowerOvercharge_prime_pow {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    suzukiPrimePowerOvercharge (p ^ k) =
      ((k : ℝ) - 1) * Real.log p / Real.sqrt (p ^ k : ℕ) := by
  have hv : ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have he : IsMangoldtEvent (p ^ k) := by
    unfold IsMangoldtEvent
    rw [hv]
    exact hpos.ne'
  rw [suzukiPrimePowerOvercharge, if_pos he, hv, Nat.cast_pow, Real.log_pow]
  ring

theorem suzukiPrimePowerOvercharge_prime {p : ℕ} (hp : p.Prime) :
    suzukiPrimePowerOvercharge p = 0 := by
  simpa using suzukiPrimePowerOvercharge_prime_pow hp (le_refl 1)

theorem suzukiPrimePowerOvercharge_nonEvent {q : ℕ} (hq : ¬ IsMangoldtEvent q) :
    suzukiPrimePowerOvercharge q = 0 := by simp [suzukiPrimePowerOvercharge, hq]

theorem suzukiPrimePowerOvercharge_pos_iff (q : ℕ) :
    0 < suzukiPrimePowerOvercharge q ↔
      ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = q := by
  constructor
  · intro h
    have he : IsMangoldtEvent q := by
      by_contra hn
      rw [suzukiPrimePowerOvercharge_nonEvent hn] at h
      exact (lt_irrefl 0 h)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp
      (isMangoldtEvent_iff_primePower.mp he)
    refine ⟨p, k, hp, ?_, rfl⟩
    by_contra hn
    have : k = 1 := by omega
    subst k
    simpa [suzukiPrimePowerOvercharge_prime hp] using h
  · rintro ⟨p, k, hp, hk, rfl⟩
    rw [suzukiPrimePowerOvercharge_prime_pow hp (by omega)]
    apply div_pos (mul_pos _ (Real.log_pos (by exact_mod_cast hp.one_lt)))
      (Real.sqrt_pos.2 (by exact_mod_cast pow_pos hp.pos k))
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

/-- Generic finite right-continuous error process, excluding the anchor. -/
def suzukiEventError (m : ℕ) (eta : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc m ⌊u ^ 2⌋₊, eta q

def suzukiEventErrorCharge (m : ℕ) (eta : ℕ → ℝ) (b : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc m ⌊b ^ 2⌋₊, eta q * Real.log (b ^ 2 / q)

def suzukiPrimePowerDelta (m : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc m ⌊x⌋₊, suzukiPrimePowerOvercharge q

def suzukiPrimePowerSurcharge (m : ℕ) (b : ℝ) : ℝ :=
  suzukiEventErrorCharge m suzukiPrimePowerOvercharge b

theorem eventLogWeight_eq_weight_add_overcharge (q : ℕ) :
    SuzukiEventChain.eventLogWeight q =
      ArithmeticFunction.vonMangoldt q / Real.sqrt q + suzukiPrimePowerOvercharge q := by
  classical
  by_cases hq : IsMangoldtEvent q
  · simp only [SuzukiEventChain.eventLogWeight, suzukiPrimePowerOvercharge, if_pos hq]
    ring
  · have hz : ArithmeticFunction.vonMangoldt q = 0 := by
      simpa [IsMangoldtEvent] using hq
    simp [SuzukiEventChain.eventLogWeight, suzukiPrimePowerOvercharge, hq, hz]

def suzukiEventLogSignedProfile (m : ℕ) (u : ℝ) : ℝ :=
  -suzukiRootSlopeDiscrepancy (Real.sqrt m) +
    (∑ q ∈ Finset.Ioc m ⌊u ^ 2⌋₊, SuzukiEventChain.eventLogWeight q) -
    suzukiRootService (Real.sqrt m) u

theorem eventLogSignedProfile_eq_neg_discrepancy_add_delta
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hu : Real.sqrt m ≤ u) :
    suzukiEventLogSignedProfile m u =
      -suzukiRootSlopeDiscrepancy u + suzukiPrimePowerDelta m (u ^ 2) := by
  have hs := suzukiSignedRootState_eq_neg_discrepancy hm hu
  simp only [suzukiEventLogSignedProfile, eventLogWeight_eq_weight_add_overcharge,
    Finset.sum_add_distrib, suzukiPrimePowerDelta]
  unfold suzukiSignedRootState suzukiSignedArrivalServiceExcess suzukiWeightedMangoldtInterval at hs
  linarith

theorem primePowerCorrectedProfile_eq_neg_discrepancy
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hu : Real.sqrt m ≤ u) :
    suzukiEventLogSignedProfile m u - suzukiPrimePowerDelta m (u ^ 2) =
      -suzukiRootSlopeDiscrepancy u := by
  rw [eventLogSignedProfile_eq_neg_discrepancy_add_delta hm hu]
  ring

def suzukiWeightedStep (r c u : ℝ) : ℝ := if r ≤ u then 2 / u * c else 0

theorem intervalIntegrable_suzukiWeightedStep {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (r c : ℝ) : IntervalIntegrable (suzukiWeightedStep r c) volume a b := by
  have hc : ContinuousOn (fun u : ℝ => 2 / u * c) (Icc a b) := by
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (ne_of_gt (ha.trans_le hu.1))).mul
      continuousAt_const).continuousWithinAt
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hc.integrableOn_Icc.indicator measurableSet_Ici

theorem integral_suzukiWeightedStep {a r b c : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) :
    (∫ u in a..b, suzukiWeightedStep r c u) = 2 * c * Real.log (b / r) := by
  have hi1 := intervalIntegrable_suzukiWeightedStep ha har r c
  have hi2 := intervalIntegrable_suzukiWeightedStep (ha.trans_le har) hrb r c
  have hz : (∫ u in a..r, suzukiWeightedStep r c u) = 0 := by
    rw [← intervalIntegral.integral_zero (a := a) (b := r)]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le har] at hu
    simp [suzukiWeightedStep, not_le.mpr hu.2]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hz, zero_add]
  have he : (∫ u in r..b, suzukiWeightedStep r c u) =
      ∫ u in r..b, (2 * c) * u⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hrb] at hu
    simp only [suzukiWeightedStep, if_pos hu.1]
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_inv_of_pos (ha.trans_le har)
    (ha.trans_le (har.trans hrb))]

theorem weightedEventError_eq_sum_steps {m : ℕ} {u b : ℝ} (eta : ℕ → ℝ)
    (hu : 0 ≤ u) (hub : u ≤ b) :
    2 / u * suzukiEventError m eta u =
      ∑ q ∈ Finset.Ioc m ⌊b ^ 2⌋₊, suzukiWeightedStep (Real.sqrt q) (eta q) u := by
  classical
  have hfloor : ⌊u ^ 2⌋₊ ≤ ⌊b ^ 2⌋₊ := Nat.floor_mono (by nlinarith)
  have hroot (q : ℕ) : Real.sqrt q ≤ u ↔ q ≤ ⌊u ^ 2⌋₊ := by
    rw [Real.sqrt_le_iff, Nat.le_floor_iff (sq_nonneg u)]
    simp [hu]
  simp only [suzukiEventError, Finset.mul_sum]
  calc
    _ = ∑ q ∈ Finset.Ioc m ⌊u ^ 2⌋₊, suzukiWeightedStep (Real.sqrt q) (eta q) u := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [suzukiWeightedStep, (hroot q).mpr (Finset.mem_Ioc.mp hq).2]
    _ = _ := by
      apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl hfloor)
      intro q hq hnq
      have hn : ¬ q ≤ ⌊u ^ 2⌋₊ := by
        intro h
        exact hnq (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hq).1, h⟩)
      simp [suzukiWeightedStep, (hroot q).not.mpr hn]

theorem intervalIntegrable_weightedEventError {m : ℕ} {b : ℝ}
    (hm : 1 ≤ m) (hb : Real.sqrt m ≤ b) (eta : ℕ → ℝ) :
    IntervalIntegrable (fun u => 2 / u * suzukiEventError m eta u)
      volume (Real.sqrt m) b := by
  have ha : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hi := IntervalIntegrable.sum (s := Finset.Ioc m ⌊b ^ 2⌋₊)
    (fun q _ => intervalIntegrable_suzukiWeightedStep ha hb (Real.sqrt q) (eta q))
  apply hi.congr
  intro u hu
  rw [uIoc_of_le hb] at hu
  simpa only [Finset.sum_apply] using
    (weightedEventError_eq_sum_steps (m := m) eta (ha.le.trans hu.1.le) hu.2).symm

theorem integral_weightedEventError {m : ℕ} {b : ℝ}
    (hm : 1 ≤ m) (hb : Real.sqrt m ≤ b) (eta : ℕ → ℝ) :
    (∫ u in Real.sqrt m..b, 2 / u * suzukiEventError m eta u) =
      suzukiEventErrorCharge m eta b := by
  have ha : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hb0 := ha.trans_le hb
  have he : (∫ u in Real.sqrt m..b, 2 / u * suzukiEventError m eta u) =
      ∫ u in Real.sqrt m..b,
        ∑ q ∈ Finset.Ioc m ⌊b ^ 2⌋₊, suzukiWeightedStep (Real.sqrt q) (eta q) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hb] at hu
    exact weightedEventError_eq_sum_steps eta (ha.le.trans hu.1) hu.2
  rw [he, intervalIntegral.integral_finsetSum (s := Finset.Ioc m ⌊b ^ 2⌋₊)
    (f := fun (q : ℕ) u => suzukiWeightedStep (Real.sqrt q) (eta q) u)
    (fun q _ => intervalIntegrable_suzukiWeightedStep ha hb (Real.sqrt q) (eta q))]
  apply Finset.sum_congr rfl
  intro q hq
  have hmq := (Finset.mem_Ioc.mp hq).1.le
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (hm.trans hmq)
  have hqr : Real.sqrt q ≤ b := Real.sqrt_le_iff.mpr
    ⟨hb0.le, (Nat.le_floor_iff (sq_nonneg b)).mp (Finset.mem_Ioc.mp hq).2⟩
  rw [integral_suzukiWeightedStep ha (Real.sqrt_le_sqrt (by exact_mod_cast hmq)) hqr,
    Real.log_div hb0.ne' (Real.sqrt_pos.2 hqpos).ne',
    Real.log_sqrt hqpos.le, Real.log_div (pow_pos hb0 2).ne' hqpos.ne', Real.log_pow]
  ring

theorem intervalIntegrable_weightedSignedDiscrepancy {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hb : Real.sqrt m ≤ b) :
    IntervalIntegrable (fun u => 2 / u * (-suzukiRootSlopeDiscrepancy u))
      volume (Real.sqrt m) b := by
  have ha : Real.sqrt 2 ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  have hc : ContinuousOn (fun u => 2 / u *
      (-suzukiRootSlopeDiscrepancy (Real.sqrt m) - suzukiRootService (Real.sqrt m) u))
      (Icc (Real.sqrt m) b) := by
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (hp.trans_le hu.1).ne').continuousWithinAt.mul
      (continuousWithinAt_const.sub ((continuousOn_suzukiRootService ha hb) u hu)))
  have hi := (hc.intervalIntegrable_of_Icc hb).add
    (intervalIntegrable_weightedEventError (by omega : 1 ≤ m) hb
      (fun q => ArithmeticFunction.vonMangoldt q / Real.sqrt q))
  apply hi.congr
  intro u hu
  rw [uIoc_of_le hb] at hu
  have he := suzukiSignedRootState_eq_neg_discrepancy (by omega : 1 ≤ m) hu.1.le
  unfold suzukiSignedRootState suzukiSignedArrivalServiceExcess suzukiWeightedMangoldtInterval at he
  dsimp only
  unfold suzukiEventError
  rw [← he]
  ring

theorem intervalIntegrable_positivePart {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun u => max (f u) 0) volume a b := by
  have he : (fun u => max (f u) 0) = (fun u => (f u + |f u|) / 2) := by
    funext u
    by_cases hu : 0 ≤ f u
    · rw [abs_of_nonneg hu, max_eq_left hu]; ring
    · rw [abs_of_neg (lt_of_not_ge hu), max_eq_right (le_of_not_ge hu)]; ring
  rw [he]
  exact (hf.add hf.abs).div_const 2

def suzukiPerturbedWeightedCost (m : ℕ) (eta0 : ℝ) (eta : ℕ → ℝ) (b : ℝ) : ℝ :=
  ∫ u in Real.sqrt m..b, 2 / u *
    max (-suzukiRootSlopeDiscrepancy u + eta0 + suzukiEventError m eta u) 0

def suzukiTrueWeightedCost (m : ℕ) (b : ℝ) : ℝ :=
  ∫ u in Real.sqrt m..b, 2 / u * suzukiRootSlopeBacklog u

def suzukiEventLogWeightedCost (m : ℕ) (b : ℝ) : ℝ :=
  ∫ u in Real.sqrt m..b, 2 / u * max (suzukiEventLogSignedProfile m u) 0

theorem intervalIntegrable_perturbedDensity {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hb : Real.sqrt m ≤ b) (eta0 : ℝ) (eta : ℕ → ℝ) :
    IntervalIntegrable (fun u => 2 / u *
      max (-suzukiRootSlopeDiscrepancy u + eta0 + suzukiEventError m eta u) 0)
      volume (Real.sqrt m) b := by
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  have hc : IntervalIntegrable (fun u : ℝ => 2 / u * eta0) volume (Real.sqrt m) b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (hp.trans_le hu.1).ne').mul
      continuousAt_const).continuousWithinAt
  have hi := intervalIntegrable_positivePart
    (((intervalIntegrable_weightedSignedDiscrepancy hm hb).add hc).add
      (intervalIntegrable_weightedEventError (by omega) hb eta))
  apply hi.congr
  intro u hu
  rw [uIoc_of_le hb] at hu
  dsimp only
  rw [← mul_add, ← mul_add, mul_max_of_nonneg _ _
    (div_nonneg (by norm_num) (hp.le.trans hu.1.le)), mul_zero]

theorem integral_weightedInitialError {m : ℕ} {b : ℝ}
    (hm : 1 ≤ m) (hb : Real.sqrt m ≤ b) (eta0 : ℝ) :
    (∫ u in Real.sqrt m..b, 2 / u * eta0) = eta0 * Real.log (b ^ 2 / m) := by
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  have hb0 := hp.trans_le hb
  have he : (fun u : ℝ => 2 / u * eta0) = (fun u => (2 * eta0) * u⁻¹) := by
    funext u; ring
  rw [he, intervalIntegral.integral_const_mul, integral_inv_of_pos hp hb0,
    Real.log_div hb0.ne' hp.ne', Real.log_sqrt (Nat.cast_nonneg m),
    Real.log_div (pow_pos hb0 2).ne' (by exact_mod_cast (by omega : m ≠ 0)), Real.log_pow]
  ring

theorem eventError_nonneg (m : ℕ) {eta : ℕ → ℝ} (heta : ∀ q, 0 ≤ eta q) (u : ℝ) :
    0 ≤ suzukiEventError m eta u := Finset.sum_nonneg (fun q _ => heta q)

theorem weightedCost_perturbation_bound {m : ℕ} {b eta0 : ℝ} {eta : ℕ → ℝ}
    (hm : 2 ≤ m) (hb : Real.sqrt m ≤ b) (h0 : 0 ≤ eta0) (heta : ∀ q, 0 ≤ eta q) :
    0 ≤ suzukiPerturbedWeightedCost m eta0 eta b - suzukiTrueWeightedCost m b ∧
    suzukiPerturbedWeightedCost m eta0 eta b - suzukiTrueWeightedCost m b ≤
      eta0 * Real.log (b ^ 2 / m) + suzukiEventErrorCharge m eta b := by
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  have ht := intervalIntegrable_perturbedDensity hm hb 0 (fun _ => 0)
  simp only [suzukiEventError, Finset.sum_const_zero, add_zero] at ht
  have he := intervalIntegrable_perturbedDensity hm hb eta0 eta
  have hi := intervalIntegrable_weightedEventError (by omega : 1 ≤ m) hb eta
  have hc : IntervalIntegrable (fun u : ℝ => 2 / u * eta0) volume (Real.sqrt m) b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (hp.trans_le hu.1).ne').mul
      continuousAt_const).continuousWithinAt
  have hdiff := he.sub ht
  have hid : suzukiPerturbedWeightedCost m eta0 eta b - suzukiTrueWeightedCost m b =
      ∫ u in Real.sqrt m..b, (2 / u *
        max (-suzukiRootSlopeDiscrepancy u + eta0 + suzukiEventError m eta u) 0 -
        2 / u * max (-suzukiRootSlopeDiscrepancy u) 0) := by
    rw [intervalIntegral.integral_sub he ht]
    rfl
  rw [hid]
  constructor
  · apply intervalIntegral.integral_nonneg hb
    intro u hu
    have hw : 0 ≤ 2 / u := div_nonneg (by norm_num) (hp.le.trans hu.1)
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (max_le_max_right 0 (by linarith [eventError_nonneg m heta u])) hw)
  · have hle := intervalIntegral.integral_mono_on hb hdiff (hc.add hi)
      (fun u hu => show _ ≤ 2 / u * eta0 + 2 / u * suzukiEventError m eta u from by
        have hη := eventError_nonneg m heta u
        have hmax : max (-suzukiRootSlopeDiscrepancy u + eta0 + suzukiEventError m eta u) 0 ≤
            max (-suzukiRootSlopeDiscrepancy u) 0 + eta0 + suzukiEventError m eta u := by
          apply max_le
          · linarith [le_max_left (-suzukiRootSlopeDiscrepancy u) 0]
          · linarith [le_max_right (-suzukiRootSlopeDiscrepancy u) 0]
        have hw := mul_le_mul_of_nonneg_left hmax
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hp.le.trans hu.1))
        nlinarith)
    rw [intervalIntegral.integral_add hc hi, integral_weightedInitialError (by omega) hb,
      integral_weightedEventError (by omega) hb] at hle
    exact hle

theorem weightedCost_perturbation_eq_of_negative {m : ℕ} {b eta0 : ℝ} {eta : ℕ → ℝ}
    (hm : 2 ≤ m) (hb : Real.sqrt m ≤ b) (h0 : 0 ≤ eta0) (heta : ∀ q, 0 ≤ eta q)
    (hneg : ∀ u ∈ Icc (Real.sqrt m) b, suzukiRootSlopeDiscrepancy u ≤ 0) :
    suzukiPerturbedWeightedCost m eta0 eta b - suzukiTrueWeightedCost m b =
      eta0 * Real.log (b ^ 2 / m) + suzukiEventErrorCharge m eta b := by
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
  have ht := intervalIntegrable_perturbedDensity hm hb 0 (fun _ => 0)
  simp only [suzukiEventError, Finset.sum_const_zero, add_zero] at ht
  have he := intervalIntegrable_perturbedDensity hm hb eta0 eta
  have hi := intervalIntegrable_weightedEventError (by omega : 1 ≤ m) hb eta
  have hc : IntervalIntegrable (fun u : ℝ => 2 / u * eta0) volume (Real.sqrt m) b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb
    intro u hu
    exact ((continuousAt_const.div continuousAt_id (hp.trans_le hu.1).ne').mul
      continuousAt_const).continuousWithinAt
  unfold suzukiPerturbedWeightedCost suzukiTrueWeightedCost suzukiRootSlopeBacklog
  rw [← intervalIntegral.integral_sub he ht]
  have hpoint : (∫ u in Real.sqrt m..b,
      (2 / u * max (-suzukiRootSlopeDiscrepancy u + eta0 + suzukiEventError m eta u) 0 -
      2 / u * max (-suzukiRootSlopeDiscrepancy u) 0)) =
      ∫ u in Real.sqrt m..b, (2 / u * eta0 + 2 / u * suzukiEventError m eta u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hb] at hu
    have hn := hneg u hu
    have hη := eventError_nonneg m heta u
    dsimp only
    rw [max_eq_left (by linarith : 0 ≤ -suzukiRootSlopeDiscrepancy u + eta0 +
      suzukiEventError m eta u), max_eq_left (by linarith : 0 ≤ -suzukiRootSlopeDiscrepancy u)]
    ring
  rw [hpoint, intervalIntegral.integral_add hc hi,
    integral_weightedInitialError (by omega) hb, integral_weightedEventError (by omega) hb]

theorem eventLogWeightedCost_eq_perturbed {m : ℕ} {b : ℝ}
    (hm : 1 ≤ m) (hb : Real.sqrt m ≤ b) :
    suzukiEventLogWeightedCost m b =
      suzukiPerturbedWeightedCost m 0 suzukiPrimePowerOvercharge b := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hb] at hu
  dsimp only
  rw [eventLogSignedProfile_eq_neg_discrepancy_add_delta hm hu.1]
  simp only [add_zero, suzukiPrimePowerDelta, suzukiEventError]

theorem eventLogWeightedCost_sub_true_bounds {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hb : Real.sqrt m ≤ b) :
    0 ≤ suzukiEventLogWeightedCost m b - suzukiTrueWeightedCost m b ∧
    suzukiEventLogWeightedCost m b - suzukiTrueWeightedCost m b ≤
      suzukiPrimePowerSurcharge m b := by
  rw [eventLogWeightedCost_eq_perturbed (by omega) hb]
  simpa [suzukiPrimePowerSurcharge] using weightedCost_perturbation_bound hm hb
    (le_refl 0) suzukiPrimePowerOvercharge_nonneg

theorem eventLogWeightedCost_sub_true_eq_surcharge {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt m) b) :
    suzukiEventLogWeightedCost m b - suzukiTrueWeightedCost m b =
      suzukiPrimePowerSurcharge m b := by
  rw [eventLogWeightedCost_eq_perturbed (by omega) hexc.1]
  simpa [suzukiPrimePowerSurcharge] using weightedCost_perturbation_eq_of_negative hm hexc.1
    (le_refl 0) suzukiPrimePowerOvercharge_nonneg hexc.2

theorem SuzukiEventChain.negative_loss_eq_backlog_integral {q r : ℕ}
    (chain : SuzukiEventChain q r) (hq : 2 ≤ q) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r)
    (hneg : ∀ v ∈ Icc (Real.sqrt q) u, suzukiRootSlopeDiscrepancy v ≤ 0) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u =
      ∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeBacklog v := by
  have localLoss {q p : ℕ} (h : IsSuzukiEventFreeCell q p) (hq : 2 ≤ q) {u : ℝ}
      (hqu : Real.sqrt q ≤ u) (hup : u ≤ Real.sqrt p)
      (hneg : ∀ v ∈ Icc (Real.sqrt q) u, suzukiRootSlopeDiscrepancy v ≤ 0) :
      suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u =
        ∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeBacklog v := by
    obtain ⟨j, k, hjk, hjq, hpk⟩ := h.contained_in_block hq
    exact suzukiPsiRoot_loss_eq_integral_backlog hjk
      (Real.sqrt_le_sqrt (by exact_mod_cast hjq)) hqu
      (hup.trans (Real.sqrt_le_sqrt (by exact_mod_cast hpk))) hneg
  induction chain generalizing u with
  | nil q =>
      have hu : u = Real.sqrt q := le_antisymm hur hqu
      subst u
      simp
  | @cons q p r h tail ih =>
      have hqp := Real.sqrt_le_sqrt (show (q : ℝ) ≤ p by exact_mod_cast h.1.le)
      by_cases hup : u ≤ Real.sqrt p
      · exact localLoss h hq hqu hup hneg
      · have hpu := le_of_not_ge hup
        have hi := (tail.backlog_integrable (hq.trans h.1.le)).mono_set (by
          rw [uIcc_of_le hpu, uIcc_of_le (Real.sqrt_le_sqrt (by exact_mod_cast tail.ordered))]
          exact Icc_subset_Icc le_rfl hur)
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_weighted_backlog_eventFree hq h) hi,
          ← localLoss h hq hqp le_rfl (fun v hv => hneg v ⟨hv.1, hv.2.trans hpu⟩),
          ← ih (hq.trans h.1.le) hpu hur (fun v hv => hneg v ⟨hqp.trans hv.1, hv.2⟩)]
        ring

theorem trueWeightedCost_eq_loss_of_negative {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt m) b) :
    suzukiTrueWeightedCost m b = suzukiPsiRoot (Real.sqrt m) - suzukiPsiRoot b := by
  have hb0 : 0 ≤ b := (Real.sqrt_nonneg m).trans hexc.1
  have hmb : (m : ℝ) ≤ b ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m), Real.sqrt_nonneg m, hexc.1]
  have hmn : m ≤ ⌈b ^ 2⌉₊ := by exact_mod_cast hmb.trans (Nat.le_ceil _)
  have hbr : b ≤ Real.sqrt (⌈b ^ 2⌉₊ : ℝ) := by
    nlinarith [Nat.le_ceil (b ^ 2), Real.sq_sqrt (Nat.cast_nonneg ⌈b ^ 2⌉₊),
      Real.sqrt_nonneg (⌈b ^ 2⌉₊ : ℝ)]
  exact ((SuzukiEventChain.canonical m ⌈b ^ 2⌉₊ hmn).negative_loss_eq_backlog_integral
    hm hexc.1 hbr hexc.2).symm

theorem eventLogWeightedCost_eq_loss_add_surcharge {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt m) b) :
    suzukiEventLogWeightedCost m b =
      suzukiPsiRoot (Real.sqrt m) - suzukiPsiRoot b + suzukiPrimePowerSurcharge m b := by
  linarith [eventLogWeightedCost_sub_true_eq_surcharge hm hexc,
    trueWeightedCost_eq_loss_of_negative hm hexc]

/-- The event-log criterion is exactly endpoint positivity strengthened by
the artificial prime-power surcharge, not an independent positivity theorem. -/
theorem eventLog_cost_safe_iff_surcharge_le_endpoint {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt m) b) :
    suzukiEventLogWeightedCost m b ≤ suzukiPsiRoot (Real.sqrt m) ↔
      suzukiPrimePowerSurcharge m b ≤ suzukiPsiRoot b := by
  rw [eventLogWeightedCost_eq_loss_add_surcharge hm hexc]
  constructor <;> intro h <;> linarith

theorem corrected_cost_safe_iff_endpoint_nonnegative {m : ℕ} {b : ℝ}
    (hm : 2 ≤ m) (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt m) b) :
    suzukiTrueWeightedCost m b ≤ suzukiPsiRoot (Real.sqrt m) ↔ 0 ≤ suzukiPsiRoot b := by
  rw [trueWeightedCost_eq_loss_of_negative hm hexc]
  constructor <;> intro h <;> linarith

end RHGarden
