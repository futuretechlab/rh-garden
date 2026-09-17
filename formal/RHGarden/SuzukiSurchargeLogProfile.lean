import RHGarden.SuzukiPrimePowerSurcharge

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite logarithmic-coordinate identities for the artificial event-log surcharge.
The identities use arbitrary event weights, not a numerical approximation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace RHGarden

theorem log_event_threshold {m q r : ℝ} (hm : 0 < m) (hq : 0 < q) :
    Real.log (q / m) ≤ r ↔ q ≤ m * Real.exp r := by
  rw [Real.log_le_iff_le_exp (div_pos hq hm), div_le_iff₀ hm]
  rw [mul_comm]

/-- A right-continuous constant step; its value at the jump does not affect its integral. -/
def suzukiLogStep (t c r : ℝ) : ℝ := if t ≤ r then c else 0

theorem intervalIntegrable_suzukiLogStep (a b t c : ℝ) :
    IntervalIntegrable (suzukiLogStep t c) volume a b := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (continuous_const.integrableOn_Icc).indicator measurableSet_Ici
  · apply IntervalIntegrable.symm
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (continuous_const.integrableOn_Icc).indicator measurableSet_Ici

theorem integral_suzukiLogStep {t s c : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (∫ r in 0..s, suzukiLogStep t c r) = c * max (s - t) 0 := by
  by_cases hts : t ≤ s
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_suzukiLogStep 0 t t c)
      (intervalIntegrable_suzukiLogStep t s t c)]
    have hleft : (∫ r in 0..t, suzukiLogStep t c r) = 0 := by
      conv_rhs => rw [← intervalIntegral.integral_zero (a := 0) (b := t) (μ := volume)]
      apply intervalIntegral.integral_congr_uIoo
      intro r hr
      rw [uIoo_of_le ht] at hr
      simp [suzukiLogStep, not_le.mpr hr.2]
    have hright : (∫ r in t..s, suzukiLogStep t c r) = (s - t) * c := by
      calc
        _ = ∫ r in t..s, c := by
          apply intervalIntegral.integral_congr
          intro r hr
          rw [uIcc_of_le hts] at hr
          simp [suzukiLogStep, hr.1]
        _ = _ := by simp
    rw [hleft, hright, zero_add, max_eq_left (sub_nonneg.mpr hts), mul_comm]
  · rw [max_eq_right (by linarith : s - t ≤ 0), mul_zero]
    conv_rhs => rw [← intervalIntegral.integral_zero (a := 0) (b := s) (μ := volume)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs] at hr
    simp [suzukiLogStep, not_le.mpr (lt_of_le_of_lt hr.2 (lt_of_not_ge hts))]

theorem logEventProfile_eq_sum_steps {m : ℕ} {s S : ℝ}
    (hm : 1 ≤ m) (hsS : s ≤ S) (eta : ℕ → ℝ) :
    (∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊, eta q) =
      ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp S⌋₊,
        suzukiLogStep (Real.log ((q : ℝ) / m)) (eta q) s := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub : Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊ ⊆
      Finset.Ioc m ⌊(m : ℝ) * Real.exp S⌋₊ := by
    exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_le_floor
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsS) hm0.le))
  symm
  calc
    _ = ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊,
        suzukiLogStep (Real.log ((q : ℝ) / m)) (eta q) s := by
      symm
      apply Finset.sum_subset hsub
      intro q hq hnot
      have hqm := (Finset.mem_Ioc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hnotq : ¬ (q : ℝ) ≤ (m : ℝ) * Real.exp s := by
        intro h
        exact hnot (Finset.mem_Ioc.mpr ⟨hqm, (Nat.le_floor_iff (by positivity)).mpr h⟩)
      simp [suzukiLogStep, log_event_threshold hm0 hq0, hnotq]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq0 : (0 : ℝ) < q := by have := (Finset.mem_Ioc.mp hq).1; exact_mod_cast (show 0 < q by omega)
      have hqu := (Nat.le_floor_iff (by positivity : 0 ≤ (m : ℝ) * Real.exp s)).mp
        (Finset.mem_Ioc.mp hq).2
      simp [suzukiLogStep, log_event_threshold hm0 hq0, hqu]

theorem intervalIntegrable_logEventProfile (m : ℕ) (hm : 1 ≤ m)
    (eta : ℕ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun r => ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp r⌋₊,
      eta q) volume 0 s := by
  have hi := IntervalIntegrable.sum (s := Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊)
    (fun q _ => intervalIntegrable_suzukiLogStep 0 s
      (Real.log ((q : ℝ) / m)) (eta q))
  apply hi.congr
  intro r hr
  rw [uIoc_of_le hs] at hr
  simpa only [Finset.sum_apply] using (logEventProfile_eq_sum_steps hm hr.2 eta).symm

/-- A finite fixed-window ramp formula, including a zero-valued ramp at the terminal event. -/
theorem eventErrorCharge_log_ramp {m : ℕ} {s S : ℝ}
    (hm : 1 ≤ m) (_hs : 0 ≤ s) (hsS : s ≤ S) (eta : ℕ → ℝ) :
    suzukiEventErrorCharge m eta (Real.sqrt ((m : ℝ) * Real.exp s)) =
      ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp S⌋₊,
        eta q * max (s - Real.log ((q : ℝ) / m)) 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold suzukiEventErrorCharge
  rw [Real.sq_sqrt (by positivity)]
  have hsub : Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊ ⊆
      Finset.Ioc m ⌊(m : ℝ) * Real.exp S⌋₊ :=
    Finset.Ioc_subset_Ioc le_rfl (Nat.floor_le_floor
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsS) hm0.le))
  calc
    _ = ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊,
        eta q * max (s - Real.log ((q : ℝ) / m)) 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq0 : (0 : ℝ) < q := by have := (Finset.mem_Ioc.mp hq).1; exact_mod_cast (show 0 < q by omega)
      have hqu := (Nat.le_floor_iff (by positivity : 0 ≤ (m : ℝ) * Real.exp s)).mp
        (Finset.mem_Ioc.mp hq).2
      rw [max_eq_left (sub_nonneg.mpr ((log_event_threshold hm0 hq0).mpr hqu)),
        Real.log_div (by positivity) hq0.ne', Real.log_mul hm0.ne' (Real.exp_ne_zero _),
        Real.log_exp, Real.log_div hq0.ne' hm0.ne']
      ring
    _ = _ := by
      apply Finset.sum_subset hsub
      intro q hq hnot
      have hqm := (Finset.mem_Ioc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hnotq : ¬ (q : ℝ) ≤ (m : ℝ) * Real.exp s := by
        intro h
        exact hnot (Finset.mem_Ioc.mpr ⟨hqm, (Nat.le_floor_iff (by positivity)).mpr h⟩)
      rw [max_eq_right (by
        have := not_le.mp (mt (log_event_threshold hm0 hq0).mp hnotq)
        linarith), mul_zero]

theorem integral_logEventProfile {m : ℕ} {s : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) (eta : ℕ → ℝ) :
    (∫ r in 0..s, ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp r⌋₊, eta q) =
      suzukiEventErrorCharge m eta (Real.sqrt ((m : ℝ) * Real.exp s)) := by
  rw [eventErrorCharge_log_ramp hm hs le_rfl]
  have he : (∫ r in 0..s, ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp r⌋₊, eta q) =
      ∫ r in 0..s, ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊,
        suzukiLogStep (Real.log ((q : ℝ) / m)) (eta q) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs] at hr
    exact logEventProfile_eq_sum_steps hm hr.2 eta
  rw [he, intervalIntegral.integral_finsetSum (s := Finset.Ioc m ⌊(m : ℝ) * Real.exp s⌋₊)
    (f := fun (q : ℕ) r => suzukiLogStep (Real.log ((q : ℝ) / m)) (eta q) r) (fun q _ =>
    intervalIntegrable_suzukiLogStep 0 s (Real.log ((q : ℝ) / m)) (eta q))]
  apply Finset.sum_congr rfl
  intro q hq
  apply integral_suzukiLogStep _ hs
  apply Real.log_nonneg
  apply (one_le_div (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
  exact_mod_cast (Finset.mem_Ioc.mp hq).1.le

theorem primePowerSurcharge_log_ramp {m : ℕ} {s S : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) (hsS : s ≤ S) :
    suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) =
      ∑ q ∈ Finset.Ioc m ⌊(m : ℝ) * Real.exp S⌋₊,
        suzukiPrimePowerOvercharge q * max (s - Real.log ((q : ℝ) / m)) 0 :=
  eventErrorCharge_log_ramp hm hs hsS _

theorem primePowerSurcharge_eq_integral_logDelta {m : ℕ} {s : ℝ}
    (hm : 1 ≤ m) (hs : 0 ≤ s) :
    suzukiPrimePowerSurcharge m (Real.sqrt ((m : ℝ) * Real.exp s)) =
      ∫ r in 0..s, suzukiPrimePowerDelta m ((m : ℝ) * Real.exp r) :=
  (integral_logEventProfile hm hs _).symm

end RHGarden
