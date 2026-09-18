import RHGarden.SuzukiForwardDifference
import RHGarden.SuzukiEventPartition

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

Finite-interval calculus and qualitative recovery of the actual signed
Mangoldt discrepancy. Recovery is not a reserve or positivity certificate.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace RHGarden

theorem monotone_suzukiMangoldtSlope : Monotone suzukiMangoldtSlope := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hmn)
    (fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

theorem suzukiRootSlopeDiscrepancy_exp_half (t : ℝ) :
    suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) =
      deriv suzukiPsiArchimedean t - suzukiMangoldtSlope ⌊Real.exp t⌋₊ := by
  have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simp [suzukiRootSlopeDiscrepancy, suzukiRootArchSlope, suzukiRootMangoldtSlope, he,
    show 2 * (t / 2) = t by ring]

theorem intervalIntegrable_suzukiDiscrepancy_exp_half {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => suzukiRootSlopeDiscrepancy (Real.exp (t / 2)))
      volume a b := by
  have hc : ContinuousOn (deriv suzukiPsiArchimedean) (Icc a b) := by
    intro t ht
    exact (hasDerivAt_deriv_suzukiPsiArchimedean (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hm : Monotone (fun t : ℝ => suzukiMangoldtSlope ⌊Real.exp t⌋₊) :=
    monotone_suzukiMangoldtSlope.comp (fun _ _ h => Nat.floor_mono (Real.exp_le_exp.mpr h))
  simpa only [suzukiRootSlopeDiscrepancy_exp_half] using
    (hc.intervalIntegrable_of_Icc hab).sub hm.intervalIntegrable

private theorem log_cell_of_log_two_le {t : ℝ} (ht : Real.log 2 ≤ t) :
    2 ≤ ⌊Real.exp t⌋₊ ∧ Real.log (⌊Real.exp t⌋₊ : ℝ) ≤ t ∧
      t < Real.log ((⌊Real.exp t⌋₊ : ℝ) + 1) := by
  have he2 : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hn : 2 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor he2
  refine ⟨hn, ?_, ?_⟩
  · calc
      Real.log (⌊Real.exp t⌋₊ : ℝ) ≤ Real.log (Real.exp t) :=
        Real.log_le_log (by exact_mod_cast (show 0 < ⌊Real.exp t⌋₊ by omega))
          (Nat.floor_le (Real.exp_pos t).le)
      _ = t := Real.log_exp t
  · calc
      t = Real.log (Real.exp t) := (Real.log_exp t).symm
      _ < _ := Real.log_lt_log (Real.exp_pos t) (Nat.lt_floor_add_one _)

/-- At an event the derivative is taken from the right, so it includes
the event's downward jump. This is not a claim of global differentiability. -/
theorem hasDerivWithinAt_suzukiPsi_right {t : ℝ} (ht : Real.log 2 ≤ t) :
    HasDerivWithinAt suzukiPsi
      (suzukiRootSlopeDiscrepancy (Real.exp (t / 2))) (Ioi t) t := by
  obtain ⟨hn, hnt, htn⟩ := log_cell_of_log_two_le ht
  let n := ⌊Real.exp t⌋₊
  have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  have hd := ((differentiableAt_suzukiPsiArchimedean_of_pos htpos).hasDerivAt.sub
    ((hasDerivAt_id t).const_mul (suzukiMangoldtSlope n))).add_const
      (suzukiMangoldtIntercept n)
  rw [suzukiRootSlopeDiscrepancy_exp_half]
  simp only [mul_one] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds htn).filter_mono nhdsWithin_le_nhds] with v hv hvn
    exact suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_cell (by omega : 1 ≤ n)
      (hnt.trans hv.le) hvn
  · exact suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_cell (by omega : 1 ≤ n) hnt htn

/-- Arbitrary finite endpoints: no negative-excursion, recovery, or
integrability premise is required. -/
theorem suzukiPsi_sub_eq_integral_rootDiscrepancy {a b : ℝ}
    (ha : Real.log 2 ≤ a) (hab : a ≤ b) :
    suzukiPsi b - suzukiPsi a =
      ∫ t in a..b, suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    continuous_suzukiPsi.continuousOn
    (fun t ht => hasDerivWithinAt_suzukiPsi_right (ha.trans ht.1.le))
  exact intervalIntegrable_suzukiDiscrepancy_exp_half
    ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ha) hab

theorem suzukiRootSlopeDiscrepancy_cofinal_pos {U : ℝ} (hU : Real.sqrt 2 ≤ U) :
    ∃ u : ℝ, U < u ∧ 0 < suzukiRootSlopeDiscrepancy u := by
  by_contra hn
  push Not at hn
  have hU0 : 0 < U := (Real.sqrt_pos.mpr (by norm_num)).trans_le hU
  obtain ⟨ell, hell, hp, _⟩ := suzukiForwardDifference_cofinal_signs
  obtain ⟨t, ht, hdiff⟩ := hp (max (Real.log 2) (2 * Real.log U))
  have ht2 : Real.log 2 ≤ t := (le_max_left _ _).trans ht.le
  have hI := suzukiPsi_sub_eq_integral_rootDiscrepancy ht2
    (by linarith : t ≤ t + ell)
  have hnonpos : (∫ v in t..t + ell,
      suzukiRootSlopeDiscrepancy (Real.exp (v / 2))) ≤ 0 := by
    have hnn : 0 ≤ (∫ v in t..t + ell,
        -suzukiRootSlopeDiscrepancy (Real.exp (v / 2))) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro v hv
      apply neg_nonneg.mpr
      apply hn
      rw [← Real.exp_log hU0]
      apply Real.exp_lt_exp.mpr
      have := (le_max_right (Real.log 2) (2 * Real.log U)).trans_lt ht
      linarith [hv.1]
    rw [intervalIntegral.integral_neg] at hnn
    linarith
  dsimp [suzukiForwardDifference] at hdiff
  linarith

theorem suzukiRootSlopeDiscrepancy_cofinal_neg {U : ℝ} (hU : Real.sqrt 2 ≤ U) :
    ∃ u : ℝ, U < u ∧ suzukiRootSlopeDiscrepancy u < 0 := by
  by_contra hn
  push Not at hn
  have hU0 : 0 < U := (Real.sqrt_pos.mpr (by norm_num)).trans_le hU
  obtain ⟨ell, hell, _, hp⟩ := suzukiForwardDifference_cofinal_signs
  obtain ⟨t, ht, hdiff⟩ := hp (max (Real.log 2) (2 * Real.log U))
  have ht2 : Real.log 2 ≤ t := (le_max_left _ _).trans ht.le
  have hI := suzukiPsi_sub_eq_integral_rootDiscrepancy ht2
    (by linarith : t ≤ t + ell)
  have hnonneg : 0 ≤ (∫ v in t..t + ell,
      suzukiRootSlopeDiscrepancy (Real.exp (v / 2))) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro v hv
    apply hn
    rw [← Real.exp_log hU0]
    apply Real.exp_lt_exp.mpr
    have := (le_max_right (Real.log 2) (2 * Real.log U)).trans_lt ht
    linarith [hv.1]
  dsimp [suzukiForwardDifference] at hdiff
  linarith

/-- The arithmetic state cannot jump upward in the discrepancy. -/
theorem discrepancy_sub_le_archSlope_sub {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    suzukiRootSlopeDiscrepancy v - suzukiRootSlopeDiscrepancy u ≤
      suzukiRootArchSlope v - suzukiRootArchSlope u := by
  have hm := monotone_suzukiMangoldtSlope
    (Nat.floor_mono (show u ^ 2 ≤ v ^ 2 by nlinarith))
  dsimp [suzukiRootSlopeDiscrepancy, suzukiRootMangoldtSlope]
  linarith

theorem rootMangoldtSlope_eventuallyEq_right {u : ℝ} (hu : 0 ≤ u) :
    suzukiRootMangoldtSlope =ᶠ[𝓝[≥] u] fun _ => suzukiRootMangoldtSlope u := by
  have htop : u ^ 2 < (⌊u ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have he : ∀ᶠ v : ℝ in 𝓝 u, v ^ 2 < (⌊u ^ 2⌋₊ : ℝ) + 1 :=
    (continuousAt_id.pow 2).eventually_lt continuousAt_const htop
  filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds] with v hv hvtop
  have hvu : u ≤ v := hv
  have hfloor : ⌊v ^ 2⌋₊ = ⌊u ^ 2⌋₊ := by
    apply Nat.floor_eq_iff (sq_nonneg v) |>.mpr
    exact ⟨(Nat.floor_le (sq_nonneg u)).trans (by nlinarith), hvtop⟩
  simp only [suzukiRootMangoldtSlope, hfloor]

theorem continuousWithinAt_discrepancy_right {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    ContinuousWithinAt suzukiRootSlopeDiscrepancy (Ici u) u := by
  have hm := rootMangoldtSlope_eventuallyEq_right ((Real.sqrt_nonneg 2).trans hu)
  apply ((hasDerivAt_suzukiRootArchSlope hu).continuousAt.sub
    (continuousAt_const (y := suzukiRootMangoldtSlope u))).continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [hm] with v hv
    simp only [suzukiRootSlopeDiscrepancy, hv, Pi.sub_apply]
  · rfl

private theorem negative_right_interval {a : ℝ} (ha : Real.sqrt 2 ≤ a)
    (hneg : suzukiRootSlopeDiscrepancy a < 0) :
    ∃ c : ℝ, a < c ∧ ∀ u ∈ Ico a c, suzukiRootSlopeDiscrepancy u < 0 := by
  have he : ∀ᶠ u in 𝓝[≥] a, suzukiRootSlopeDiscrepancy u < 0 :=
    (continuousWithinAt_discrepancy_right ha).eventually
      (Iio_mem_nhds hneg)
  exact mem_nhdsGE_iff_exists_Ico_subset.mp he

/-- A first actual zero before any later strictly positive state. The
proof uses right continuity and the no-upward-jump inequality, not global
continuity of the sawtooth. A zero left limit followed by a downward jump
is therefore not incorrectly selected as a recovery. -/
theorem first_recovery_before_positive {a c : ℝ} (ha : Real.sqrt 2 ≤ a)
    (hneg : suzukiRootSlopeDiscrepancy a < 0) (hac : a < c)
    (hpos : 0 < suzukiRootSlopeDiscrepancy c) :
    ∃ b : ℝ, a < b ∧ b ≤ c ∧ suzukiRootSlopeDiscrepancy b = 0 ∧
      ∀ u : ℝ, a ≤ u → u < b → suzukiRootSlopeDiscrepancy u < 0 := by
  let S : Set ℝ := {u | a ≤ u ∧ 0 ≤ suzukiRootSlopeDiscrepancy u}
  have hS : S.Nonempty := ⟨c, hac.le, hpos.le⟩
  have hbelow : BddBelow S := ⟨a, fun u hu => hu.1⟩
  let b := sInf S
  have hab : a ≤ b := le_csInf hS (fun u hu => hu.1)
  have hbc : b ≤ c := csInf_le hbelow ⟨hac.le, hpos.le⟩
  have hbefore : ∀ u : ℝ, a ≤ u → u < b → suzukiRootSlopeDiscrepancy u < 0 := by
    intro u hau hub
    by_contra hn
    have hmem : u ∈ S := ⟨hau, le_of_not_gt hn⟩
    exact (not_lt_of_ge (csInf_le hbelow hmem)) hub
  have hab' : a < b := by
    obtain ⟨d, had, hd⟩ := negative_right_interval ha hneg
    have hdb : d ≤ b := le_csInf hS (by
      intro u hu
      by_contra hdu
      exact (not_lt_of_ge hu.2) (hd u ⟨hu.1, lt_of_not_ge hdu⟩))
    exact had.trans_le hdb
  have hbroot := ha.trans hab
  have hbnonneg : 0 ≤ suzukiRootSlopeDiscrepancy b := by
    by_contra hn
    obtain ⟨d, hbd, hd⟩ := negative_right_interval hbroot (lt_of_not_ge hn)
    have hdb : d ≤ b := le_csInf hS (by
      intro u hu
      by_contra hdu
      exact (not_lt_of_ge hu.2)
        (hd u ⟨csInf_le hbelow hu, lt_of_not_ge hdu⟩))
    exact (not_lt_of_ge hdb) hbd
  have hbnonpos : suzukiRootSlopeDiscrepancy b ≤ 0 := by
    by_contra hn
    have hbp : 0 < suzukiRootSlopeDiscrepancy b := lt_of_not_ge hn
    have hcont : ContinuousAt (fun u => suzukiRootArchSlope b - suzukiRootArchSlope u) b :=
      continuousAt_const.sub (hasDerivAt_suzukiRootArchSlope hbroot).continuousAt
    have he : ∀ᶠ u in 𝓝 b,
        suzukiRootArchSlope b - suzukiRootArchSlope u < suzukiRootSlopeDiscrepancy b :=
      hcont.eventually (Iio_mem_nhds (by simpa using hbp))
    obtain ⟨d, hdb, hd⟩ := exists_Ioc_subset_of_mem_nhds he ⟨a, hab'⟩
    obtain ⟨u, hlu, hub⟩ := exists_between (max_lt hab' hdb)
    have hau : a ≤ u := ((le_max_left a d).trans_lt hlu).le
    have hdu : d < u := (le_max_right a d).trans_lt hlu
    have hbound := discrepancy_sub_le_archSlope_sub
      ((Real.sqrt_nonneg 2).trans (ha.trans hau)) hub.le
    have hsmall := hd ⟨hdu, hub.le⟩
    change suzukiRootArchSlope b - suzukiRootArchSlope u < suzukiRootSlopeDiscrepancy b at hsmall
    have hnegative := hbefore u hau hub
    linarith
  exact ⟨b, hab', hbc, le_antisymm hbnonpos hbnonneg, hbefore⟩

/-- Unconditional finite first recovery. This theorem gives no bound on
the recovery time, excursion depth, or reserve spent before recovery. -/
theorem suzukiRootSlopeDiscrepancy_first_recovery {a : ℝ}
    (ha : Real.sqrt 2 ≤ a) (hneg : suzukiRootSlopeDiscrepancy a < 0) :
    ∃ b : ℝ, a < b ∧ suzukiRootSlopeDiscrepancy b = 0 ∧
      ∀ u : ℝ, a ≤ u → u < b → suzukiRootSlopeDiscrepancy u < 0 := by
  obtain ⟨c, hac, hc⟩ := suzukiRootSlopeDiscrepancy_cofinal_pos ha
  obtain ⟨b, hab, _, hb, hbefore⟩ := first_recovery_before_positive ha hneg hac hc
  exact ⟨b, hab, hb, hbefore⟩

theorem suzukiRootSlopeDiscrepancy_first_recovery_unique {a b c : ℝ}
    (hab : a < b) (hac : a < c)
    (hb : suzukiRootSlopeDiscrepancy b = 0)
    (hc : suzukiRootSlopeDiscrepancy c = 0)
    (hbeforeB : ∀ u : ℝ, a ≤ u → u < b → suzukiRootSlopeDiscrepancy u < 0)
    (hbeforeC : ∀ u : ℝ, a ≤ u → u < c → suzukiRootSlopeDiscrepancy u < 0) : b = c := by
  rcases lt_trichotomy b c with h | h | h
  · have := hbeforeC b hab.le h
    rw [hb] at this
    exact (lt_irrefl _ this).elim
  · exact h
  · have := hbeforeB c hac.le h
    rw [hc] at this
    exact (lt_irrefl _ this).elim

/-- The existing negative-excursion interface is inhabited at every
negative starting state, without an eventual-recovery premise. Its cost
and starting-reserve inequalities remain separate arithmetic obligations. -/
theorem exists_completed_suzukiRootNegativeExcursion {a : ℝ}
    (ha : Real.sqrt 2 ≤ a) (hneg : suzukiRootSlopeDiscrepancy a < 0) :
    ∃ b : ℝ, a < b ∧ suzukiRootSlopeDiscrepancy b = 0 ∧
      IsSuzukiRootNegativeExcursion a b := by
  obtain ⟨b, hab, hb, hn⟩ := suzukiRootSlopeDiscrepancy_first_recovery ha hneg
  refine ⟨b, hab, hb, hab.le, fun u hu => ?_⟩
  rcases hu.2.eq_or_lt with rfl | hlt
  · exact hb.le
  · exact (hn u hu.1 hlt).le

theorem no_neverRecovering_suzukiRoot_excursion (a : ℝ) :
    ¬ ∀ u : ℝ, a ≤ u → suzukiRootSlopeDiscrepancy u ≤ 0 := by
  intro hn
  obtain ⟨u, hu, hp⟩ := suzukiRootSlopeDiscrepancy_cofinal_pos
    (le_max_right a (Real.sqrt 2))
  exact (not_lt_of_ge (hn u ((le_max_left _ _).trans hu.le))) hp

/-- The qualitative recovery lies in a finite canonical, event-complete
cover. The cover includes proper prime powers and is not an external table. -/
theorem first_recovery_has_finite_event_cover {a : ℝ}
    (ha : Real.sqrt 2 ≤ a) (hneg : suzukiRootSlopeDiscrepancy a < 0) :
    ∃ b : ℝ, a < b ∧ suzukiRootSlopeDiscrepancy b = 0 ∧
      (∀ u : ℝ, a ≤ u → u < b → suzukiRootSlopeDiscrepancy u < 0) ∧
      ∃ (m n : ℕ) (chain : SuzukiEventChain m n),
        2 ≤ m ∧ Real.sqrt m ≤ a ∧ b < Real.sqrt n ∧
          chain.points = suzukiMangoldtEventPartition m n := by
  obtain ⟨b, hab, hb, hbefore⟩ := suzukiRootSlopeDiscrepancy_first_recovery ha hneg
  have ha0 : 0 ≤ a := (Real.sqrt_nonneg 2).trans ha
  have hb0 : 0 ≤ b := ha0.trans hab.le
  have ha2 : (2 : ℝ) ≤ a ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hmn : ⌊a ^ 2⌋₊ ≤ ⌊b ^ 2⌋₊ + 1 :=
    (Nat.floor_mono (show a ^ 2 ≤ b ^ 2 by nlinarith)).trans (Nat.le_succ _)
  obtain ⟨chain, hchain⟩ := SuzukiEventChain.exists_canonical _ _ hmn
  refine ⟨b, hab, hb, hbefore, ⌊a ^ 2⌋₊, ⌊b ^ 2⌋₊ + 1, chain,
    Nat.le_floor ha2, ?_, ?_, hchain⟩
  · exact (Real.sqrt_le_iff).mpr ⟨ha0, Nat.floor_le (sq_nonneg a)⟩
  · apply (Real.lt_sqrt hb0).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (b ^ (2 : ℕ))

end RHGarden
