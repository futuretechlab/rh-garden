import RHGarden.SuzukiFinitePrefix37

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
A counterexample to the uncorrected event-log budget, not to positivity.
All decimal-looking constants below are rational enclosures proved in Lean. -/
noncomputable section
open Set
open scoped BigOperators
namespace RHGarden
set_option maxHeartbeats 3000000

theorem event_thirtyOne : IsMangoldtEvent 31 := by
  rw [isMangoldtEvent_iff_primePower]
  exact (show Nat.Prime 31 by norm_num).isPrimePow

theorem event_thirtyTwo : IsMangoldtEvent 32 := by
  rw [isMangoldtEvent_iff_primePower, isPrimePow_nat_iff]
  exact ⟨2, 5, by norm_num, by norm_num, by norm_num⟩

theorem block_thirtyOne_thirtyTwo : IsMangoldtBlock 31 32 := by
  exact ⟨by norm_num, event_thirtyOne, event_thirtyTwo, fun k hk hk' => by omega⟩

theorem block_thirtyTwo_thirtySeven : IsMangoldtBlock 32 37 := by
  refine ⟨by norm_num, event_thirtyTwo, ?_, ?_⟩
  · rw [isMangoldtEvent_iff_primePower]
    exact (show Nat.Prime 37 by norm_num).isPrimePow
  · intro k hk hk'
    interval_cases k
    · exact small_zero_33
    · exact small_zero_34
    · exact small_zero_35
    · exact small_zero_36

theorem recovery31_slope_bracket :
    suzukiRootArchSlope (5871 / 1000) < suzukiMangoldtSlope 32 ∧
    suzukiMangoldtSlope 32 < suzukiRootArchSlope (5875 / 1000) := by
  have hl := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < 5871 / 1000)
  have hh := rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < 5875 / 1000)
  have ht := small_state_32.1
  norm_num at hl hh
  constructor <;> linarith [ht.1, ht.2]

/-- The unique real recovery in the event-free cell after 32. The interval
is an exact rational enclosure, not a rounded numerical root witness. -/
theorem exists_unique_recovery31 :
    ∃! b : ℝ, b ∈ Icc (5871 / 1000) (5875 / 1000) ∧
      suzukiRootArchSlope b = suzukiMangoldtSlope 32 := by
  have hroot : Real.sqrt 2 ≤ (5871 / 1000 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc : ContinuousOn suzukiRootArchSlope (Icc (5871 / 1000) (5875 / 1000)) := by
    intro u hu
    exact (hasDerivAt_suzukiRootArchSlope (hroot.trans hu.1)).continuousAt.continuousWithinAt
  obtain ⟨b, hb, he⟩ := intermediate_value_Icc (by norm_num :
      (5871 / 1000 : ℝ) ≤ 5875 / 1000) hc
    ⟨recovery31_slope_bracket.1.le, recovery31_slope_bracket.2.le⟩
  refine ⟨b, ⟨hb, he⟩, ?_⟩
  intro y hy
  exact strictMonoOn_suzukiRootArchSlope.injOn
    (hroot.trans hy.1.1) (hroot.trans hb.1) (hy.2.trans he.symm)

theorem recovery31_root_bounds {b : ℝ} (hb : b ∈ Icc (5871 / 1000) (5875 / 1000)) :
    Real.sqrt 32 < b ∧ b < Real.sqrt 37 ∧ ⌊b ^ 2⌋₊ = 34 := by
  have h32 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32)
  have h37 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 37)
  have hp32 := Real.sqrt_nonneg (32 : ℝ)
  have hp37 := Real.sqrt_nonneg (37 : ℝ)
  refine ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2], ?_⟩
  apply (Nat.floor_eq_iff (sq_nonneg b)).mpr
  constructor <;> norm_num <;> nlinarith [hb.1, hb.2]

theorem recovery31_negative_excursion {b : ℝ}
    (hb : b ∈ Icc (5871 / 1000) (5875 / 1000))
    (he : suzukiRootArchSlope b = suzukiMangoldtSlope 32) :
    IsSuzukiRootNegativeExcursion (Real.sqrt 31) b ∧
      suzukiRootSlopeDiscrepancy b = 0 := by
  have hr := recovery31_root_bounds hb
  have h3132 : Real.sqrt 31 ≤ Real.sqrt (32 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
  have h231 : Real.sqrt 2 ≤ Real.sqrt (31 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
  have h257 : Real.sqrt 2 ≤ (57 / 10 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h3257 : Real.sqrt (32 : ℝ) ≤ 57 / 10 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32), Real.sqrt_nonneg 32]
  have hs57 : suzukiRootArchSlope (57 / 10) < suzukiMangoldtSlope 31 := by
    have hs := (rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < 57 / 10)).2
    norm_num at hs
    linarith [small_state_31.1.1]
  constructor
  · refine ⟨h3132.trans hr.1.le, ?_⟩
    intro u hu
    by_cases hu32 : u < Real.sqrt 32
    · rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyOne_thirtyTwo hu.1 hu32]
      have hs := strictMonoOn_suzukiRootArchSlope.monotoneOn
        (h231.trans hu.1) h257 (hu32.le.trans h3257)
      linarith
    · have h32u : Real.sqrt 32 ≤ u := le_of_not_gt hu32
      rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyTwo_thirtySeven h32u
        (hu.2.trans_lt hr.2.1)]
      have hs := strictMonoOn_suzukiRootArchSlope.monotoneOn
        (h231.trans hu.1) (h231.trans (h3132.trans hr.1.le)) hu.2
      rw [he] at hs
      linarith
  · rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyTwo_thirtySeven hr.1.le hr.2.1,
      he, sub_self]

theorem root_log_mem {q r : ℕ} {u : ℝ} (hq : 1 ≤ q)
    (huq : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    Real.log q ≤ 2 * Real.log u ∧ 2 * Real.log u ≤ Real.log r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hu0 : 0 < u := (Real.sqrt_pos.mpr hq0).trans_le huq
  have hq2 : (q : ℝ) ≤ u ^ 2 := by
    nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg (q : ℝ)]
  have hr2 : u ^ 2 ≤ (r : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg (r : ℝ)]
  constructor
  · simpa [Real.log_pow] using Real.log_le_log hq0 hq2
  · simpa [Real.log_pow] using Real.log_le_log (pow_pos hu0 2) hr2

theorem recovery31_reserve_bounds {b : ℝ}
    (hb : b ∈ Icc (5871 / 1000) (5875 / 1000))
    (he : suzukiRootArchSlope b = suzukiMangoldtSlope 32) :
    (1 / 100 : ℝ) ≤ suzukiPsiRoot b ∧ suzukiPsiRoot b < 35 / 1000 := by
  have hr := recovery31_root_bounds hb
  have ht := root_log_mem (by norm_num : 1 ≤ (32 : ℕ)) hr.1.le hr.2.1.le
  have ht2 : Real.log 2 ≤ 2 * Real.log b :=
    (Real.log_le_log (by norm_num) (by norm_num : (2 : ℝ) ≤ 32)).trans ht.1
  have hx2 : Real.log 2 ≤ 2 * Real.log (5873 / 1000 : ℝ) := by
    have h2 := Real.log_two_lt_d9
    norm_num at h2
    linarith [sample_log_32.1]
  unfold suzukiPsiRoot
  rw [suzukiPsi_eq_mangoldtBlock block_thirtyTwo_thirtySeven ht.1 ht.2]
  constructor
  · exact small_affine_32 small_state_32.1 small_state_32.2 ht2
  · have hs := suzukiArchimedean_strong_tangent_lower ht2 hx2
    change deriv suzukiPsiArchimedean (2 * Real.log b) = _ at he
    rw [he] at hs
    have ha := affine_sample_upper (by norm_num : (1 : ℝ) < 5873 / 1000)
      small_state_32.1 small_state_32.2 sample_log_32 (by norm_num)
    norm_num at ha
    nlinarith [sq_nonneg (2 * Real.log (5873 / 1000 : ℝ) - 2 * Real.log b)]

theorem recovery31_surcharge_lower {b : ℝ}
    (hb : b ∈ Icc (5871 / 1000) (5875 / 1000)) :
    (36 / 1000 : ℝ) < suzukiPrimePowerSurcharge 31 b := by
  have hr := recovery31_root_bounds hb
  have he32 : suzukiPrimePowerOvercharge 32 = 4 * Real.log 2 / Real.sqrt 32 := by
    convert suzukiPrimePowerOvercharge_prime_pow Nat.prime_two (show 1 ≤ 5 by norm_num) using 1 <;> norm_num
  have hz33 : suzukiPrimePowerOvercharge 33 = 0 :=
    suzukiPrimePowerOvercharge_nonEvent (by simpa [IsMangoldtEvent] using small_zero_33)
  have hz34 : suzukiPrimePowerOvercharge 34 = 0 :=
    suzukiPrimePowerOvercharge_nonEvent (by simpa [IsMangoldtEvent] using small_zero_34)
  rw [suzukiPrimePowerSurcharge, suzukiEventErrorCharge, hr.2.2]
  norm_num [Finset.sum_Ioc_succ_top, he32, hz33, hz34]
  have hg : (49 / 100 : ℝ) ≤ 4 * Real.log 2 / Real.sqrt 32 := by
    have hl := finite_log_2.1
    have hh := finite_sqrt_32.2
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    nlinarith
  have hl0 := log_rational_bounds (x := ((5871 / 1000 : ℝ) ^ 2 / 32))
    (l := 74 / 1000) (h := 8 / 100) (by norm_num) 3 (by norm_num) (by norm_num)
  have hl : (74 / 1000 : ℝ) ≤ Real.log (b ^ 2 / 32) := by
    apply hl0.1.trans
    apply Real.log_le_log (by norm_num)
    nlinarith [hb.1, hb.2]
  have hp := mul_le_mul hg hl (by norm_num : (0 : ℝ) ≤ 74 / 1000)
    (by linarith : 0 ≤ 4 * Real.log 2 / Real.sqrt 32)
  nlinarith

/-- The integrated exact-service event-log budget fails, while the true
Mangoldt-weight excursion has strictly positive terminal reserve. -/
theorem suzuki_eventLog_obstruction_thirtyOne :
    ∃ b : ℝ, b ∈ Icc (5871 / 1000) (5875 / 1000) ∧
      IsSuzukiRootNegativeExcursion (Real.sqrt 31) b ∧
      suzukiRootSlopeDiscrepancy b = 0 ∧
      (1 / 100 : ℝ) ≤ suzukiPsiRoot b ∧
      suzukiPsiRoot b < 35 / 1000 ∧
      (36 / 1000 : ℝ) < suzukiPrimePowerSurcharge 31 b ∧
      suzukiPsiRoot (Real.sqrt 31) < suzukiEventLogWeightedCost 31 b ∧
      suzukiTrueWeightedCost 31 b < suzukiPsiRoot (Real.sqrt 31) := by
  obtain ⟨b, ⟨hb, he⟩, _⟩ := exists_unique_recovery31
  obtain ⟨hexc, hz⟩ := recovery31_negative_excursion hb he
  obtain ⟨hv0, hv1⟩ := recovery31_reserve_bounds hb he
  have hj := recovery31_surcharge_lower hb
  refine ⟨b, hb, hexc, hz, hv0, hv1, hj, ?_, ?_⟩
  · rw [eventLogWeightedCost_eq_loss_add_surcharge (by norm_num) hexc]
    norm_num only [Nat.cast_ofNat]
    linarith
  · rw [trueWeightedCost_eq_loss_of_negative (by norm_num) hexc]
    norm_num only [Nat.cast_ofNat]
    linarith

theorem recovery31_first_recovery {b : ℝ}
    (hb : b ∈ Icc (5871 / 1000) (5875 / 1000))
    (he : suzukiRootArchSlope b = suzukiMangoldtSlope 32)
    {u : ℝ} (hu : u ∈ Ico (Real.sqrt 31) b) :
    suzukiRootSlopeDiscrepancy u < 0 := by
  have hr := recovery31_root_bounds hb
  have h231 : Real.sqrt 2 ≤ Real.sqrt (31 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
  by_cases hu32 : u < Real.sqrt 32
  · rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyOne_thirtyTwo hu.1 hu32]
    have hs := (rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < 57 / 10)).2
    have hu57 : u < (57 / 10 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32), Real.sqrt_nonneg 32]
    have h257 : Real.sqrt 2 ≤ (57 / 10 : ℝ) := (h231.trans hu.1).trans hu57.le
    have hmono := strictMonoOn_suzukiRootArchSlope (h231.trans hu.1) h257 hu57
    norm_num at hs
    linarith [small_state_31.1.1]
  · rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyTwo_thirtySeven
      (le_of_not_gt hu32) (hu.2.trans hr.2.1)]
    have hmono := strictMonoOn_suzukiRootArchSlope (h231.trans hu.1)
      ((h231.trans hu.1).trans hu.2.le) hu.2
    rw [he] at hmono
    linarith

theorem recovery31_true_excursion_safe {b : ℝ}
    (hb : b ∈ Icc (5871 / 1000) (5875 / 1000))
    {u : ℝ} (hu : u ∈ Icc (Real.sqrt 31) b) : 0 ≤ suzukiPsiRoot u := by
  have hr := recovery31_root_bounds hb
  have ht := root_log_mem (by norm_num : 1 ≤ (31 : ℕ)) hu.1 (hu.2.trans hr.2.1.le)
  exact suzukiPsi_nonnegative_zero_to_log_thirtySeven
    ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 31)).trans ht.1) ht.2

/-- The event at 31 actually starts the negative excursion: its pre-jump
state is positive and its right-continuous post-jump state is negative. -/
theorem event31_crosses_from_positive_to_negative :
    0 < suzukiRootArchSlope (Real.sqrt 31) - suzukiMangoldtSlope 30 ∧
    suzukiRootSlopeDiscrepancy (Real.sqrt 31) < 0 := by
  have hsq := finite_sqrt_31
  have hu : (1 : ℝ) < Real.sqrt 31 := by linarith [hsq.1]
  have hlo := (rootSlope_rational_enclosure hu).1
  have hhi := (rootSlope_rational_enclosure (by norm_num : (1 : ℝ) < 28 / 5)).2
  have h231 : Real.sqrt 2 ≤ Real.sqrt (31 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
  have h3156 : Real.sqrt (31 : ℝ) ≤ 28 / 5 := by linarith [hsq.2]
  have hmono := strictMonoOn_suzukiRootArchSlope.monotoneOn
    h231 (h231.trans h3156) h3156
  norm_num at hhi
  constructor
  · linarith [hsq.1, small_state_30.1.2]
  · change suzukiRootArchSlope (Real.sqrt 31) -
      suzukiMangoldtSlope ⌊(Real.sqrt (31 : ℝ)) ^ 2⌋₊ < 0
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31)]
    norm_num
    linarith [small_state_31.1.1]

/-- Uniqueness holds on the entire event-free recovery cell, not just on
the smaller rational isolating interval. -/
theorem exists_unique_recovery31_in_block :
    ∃! b : ℝ, b ∈ Ioo (Real.sqrt 32) (Real.sqrt 37) ∧
      suzukiRootSlopeDiscrepancy b = 0 := by
  obtain ⟨b, ⟨hb, he⟩, _⟩ := exists_unique_recovery31
  have hr := recovery31_root_bounds hb
  have hz := (recovery31_negative_excursion hb he).2
  refine ⟨b, ⟨⟨hr.1, hr.2.1⟩, hz⟩, ?_⟩
  intro u hu
  have h2 : Real.sqrt 2 ≤ Real.sqrt (32 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
  have hue := hu.2
  rw [suzukiRootSlopeDiscrepancy_eq_on_block block_thirtyTwo_thirtySeven hu.1.1.le hu.1.2] at hue
  apply strictMonoOn_suzukiRootArchSlope.injOn (h2.trans hu.1.1.le) (h2.trans hr.1.le)
  linarith

end RHGarden
