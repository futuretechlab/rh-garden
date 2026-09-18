import RHGarden.SuzukiRootRecovery
import RHGarden.SuzukiOneSidedGrowth

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

Actual minima and recovery floors. A uniform floor is an arithmetic premise,
not a consequence of qualitative recovery. Constants, unlike endpoint-growing
allowances, can be transferred from a future recovery to an earlier point.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RHGarden

def SuzukiFirstRecovery (a b : ℝ) : Prop :=
  a < b ∧ suzukiRootSlopeDiscrepancy b = 0 ∧
    ∀ v : ℝ, a ≤ v → v < b → suzukiRootSlopeDiscrepancy v < 0

def SuzukiRecoveryEndpoint (U b : ℝ) : Prop :=
  ∃ a : ℝ, U ≤ a ∧ suzukiRootSlopeDiscrepancy a < 0 ∧ SuzukiFirstRecovery a b

private theorem deriv_nonpos_of_min_left {f : ℝ → ℝ} {x d : ℝ}
    (hd : HasDerivAt f d x)
    (hmin : ∀ᶠ v in 𝓝[<] x, f x ≤ f v) : d ≤ 0 := by
  apply le_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x))
  filter_upwards [hmin, self_mem_nhdsWithin] with v hv hvx
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr (sub_nonpos.mpr hvx.le))
    (sub_nonneg.mpr hv)

private theorem deriv_nonneg_of_min_right {f : ℝ → ℝ} {x d : ℝ}
    (hd : HasDerivWithinAt f d (Ioi x) x)
    (hmin : ∀ᶠ v in 𝓝[>] x, f x ≤ f v) : 0 ≤ d := by
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Ioi x)).mp hd
  apply ge_of_tendsto hlim
  filter_upwards [hmin, self_mem_nhdsWithin] with v hv hvx
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hvx.le)) (sub_nonneg.mpr hv)

/-- Every logarithmic point has an actual complete Mangoldt block to its
right. Non-event integer boundaries remain inside the same block. -/
theorem exists_mangoldtBlock_at_log_point {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ q r : ℕ, IsMangoldtBlock q r ∧ Real.log q ≤ t ∧ t < Real.log r := by
  have he2 : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  obtain ⟨q, r, hblock, hqn, hnr⟩ := exists_mangoldtBlock_containing_nat
    ⌊Real.exp t⌋₊ (Nat.le_floor he2)
  refine ⟨q, r, hblock, ?_, ?_⟩
  · apply (Real.log_le_iff_le_exp (by exact_mod_cast hblock.left_pos)).mpr
    exact (by exact_mod_cast hqn : (q : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.exp_pos t).le)
  · apply (Real.lt_log_iff_exp_lt (by exact_mod_cast hblock.right_pos)).mpr
    exact (Nat.floor_lt (Real.exp_pos t).le).mp hnr

private theorem pre_event_deriv_nonpos {q : ℕ} (hq : 2 < q)
    (hmin : ∀ᶠ v in 𝓝[<] (Real.log q), suzukiPsi (Real.log q) ≤ suzukiPsi v) :
    deriv suzukiPsiArchimedean (Real.log q) - suzukiMangoldtSlope (q - 1) ≤ 0 := by
  have hpred : 1 ≤ q - 1 := by omega
  have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ q by omega)
  have hlogpred : Real.log (q - 1 : ℕ) < Real.log q :=
    Real.log_lt_log (by exact_mod_cast (show 0 < q - 1 by omega))
      (by exact_mod_cast (show q - 1 < q by omega))
  apply deriv_nonpos_of_min_left (hasDerivAt_suzukiMangoldtBlockProfile (q - 1)
    (Real.log_pos (by exact_mod_cast (show 1 < q by omega))))
  filter_upwards [hmin, self_mem_nhdsWithin,
    (eventually_gt_nhds hlogpred).filter_mono nhdsWithin_le_nhds] with v hv hvt hvp
  have heq := suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell hpred
    hlogpred.le (by rw [hcast])
  have heqv := suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell hpred
    hvp.le (by simpa only [hcast] using hvt.le)
  simpa only [suzukiMangoldtBlockProfile, ← heq, ← heqv] using hv

/-- The actual post-jump discrepancy at a left-sided reserve minimum is
nonpositive. At a genuine event the pre-jump derivative is strictly larger. -/
theorem discrepancy_nonpos_of_psi_min_left {t : ℝ} (ht : Real.log 2 < t)
    (hmin : ∀ᶠ v in 𝓝[<] t, suzukiPsi t ≤ suzukiPsi v) :
    suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) ≤ 0 := by
  obtain ⟨q, r, hblock, hqt, htr⟩ := exists_mangoldtBlock_at_log_point ht.le
  have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans ht
  have hstate : suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) =
      deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q := by
    rw [suzukiRootSlopeDiscrepancy_exp_half]
    congr 1
    apply mangoldtSlope_eq_on_block hblock
    · exact Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hblock.left_pos)).mp hqt)
    · exact (Nat.floor_lt (Real.exp_pos t).le).mpr
        ((Real.lt_log_iff_exp_lt (by exact_mod_cast hblock.right_pos)).mp htr)
  rw [hstate]
  rcases hqt.eq_or_lt with heq | hqt
  · subst t
    have hq2 : 2 < q := by
      by_contra hn
      have hh := Real.log_le_log (by exact_mod_cast hblock.left_pos)
        (by exact_mod_cast (le_of_not_gt hn) : (q : ℝ) ≤ 2)
      linarith
    have hleft := pre_event_deriv_nonpos hq2 hmin
    have hm := monotone_suzukiMangoldtSlope (show q - 1 ≤ q by omega)
    linarith
  · apply deriv_nonpos_of_min_left (hasDerivAt_suzukiMangoldtBlockProfile q htpos)
    filter_upwards [hmin, self_mem_nhdsWithin,
      (eventually_gt_nhds hqt).filter_mono nhdsWithin_le_nhds] with v hv hvt hvq
    simpa only [suzukiMangoldtBlockProfile,
      ← suzukiPsi_eq_mangoldtBlock hblock hqt.le htr.le,
      ← suzukiPsi_eq_mangoldtBlock hblock hvq.le (hvt.le.trans htr.le)] using hv

/-- A zero post-jump state with a left reserve minimum is strictly inside
an active complete event block. A nonzero downward jump cannot be a minimum. -/
theorem active_block_of_zero_and_min_left {t : ℝ} (ht : Real.log 2 < t)
    (hzero : suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) = 0)
    (hmin : ∀ᶠ v in 𝓝[<] t, suzukiPsi t ≤ suzukiPsi v) :
    ∃ q r : ℕ, IsActiveMangoldtBlock q r ∧
      t = suzukiArchDualOptimizer (suzukiMangoldtSlope q) ∧
      Real.log q < t ∧ t < Real.log r := by
  obtain ⟨q, r, hblock, hqt, htr⟩ := exists_mangoldtBlock_at_log_point ht.le
  have hslope : deriv suzukiPsiArchimedean t = suzukiMangoldtSlope q := by
    rw [suzukiRootSlopeDiscrepancy_exp_half] at hzero
    have hs := mangoldtSlope_eq_on_block hblock
      (Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hblock.left_pos)).mp hqt))
      ((Nat.floor_lt (Real.exp_pos t).le).mpr
        ((Real.lt_log_iff_exp_lt (by exact_mod_cast hblock.right_pos)).mp htr))
    rw [hs] at hzero
    exact sub_eq_zero.mp hzero
  have hqt' : Real.log q < t := by
    by_contra hn
    have heq : t = Real.log q := le_antisymm (le_of_not_gt hn) hqt
    subst t
    have hq2 : 2 < q := by
      by_contra hh
      have hle := Real.log_le_log (by exact_mod_cast hblock.left_pos)
        (by exact_mod_cast (le_of_not_gt hh) : (q : ℝ) ≤ 2)
      linarith
    have hleft := pre_event_deriv_nonpos hq2 hmin
    have hj := suzukiMangoldtSlope_succ (q - 1)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ q)] at hj
    have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ q by omega)
    rw [hcast] at hj
    have hjpos : 0 < ArithmeticFunction.vonMangoldt q / Real.sqrt q :=
      div_pos (isMangoldtEvent_iff_pos.mp hblock.left_event)
        (Real.sqrt_pos.mpr (by exact_mod_cast hblock.left_pos))
    rw [hslope] at hleft
    linarith
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num)
    (by exact_mod_cast hblock.left_event.two_le)
  have hactive : IsActiveMangoldtBlock q r := by
    refine ⟨hblock, ?_, ?_⟩
    · rw [← hslope]
      exact deriv_suzukiPsiArchimedean_strictMonoOn hlogq ht.le hqt'
    · rw [← hslope]
      exact deriv_suzukiPsiArchimedean_strictMonoOn ht.le (ht.le.trans htr.le) htr
  have hopt := suzukiArchDualOptimizer_deriv_archimedean ht.le
  rw [hslope] at hopt
  exact ⟨q, r, hactive, hopt.symm, hqt', htr⟩

theorem discrepancy_exp_half_eq_on_mangoldtBlock {q r : ℕ}
    (h : IsMangoldtBlock q r) {t : ℝ} (hqt : Real.log q ≤ t) (htr : t < Real.log r) :
    suzukiRootSlopeDiscrepancy (Real.exp (t / 2)) =
      deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q := by
  rw [suzukiRootSlopeDiscrepancy_exp_half]
  congr 1
  exact mangoldtSlope_eq_on_block h
    (Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast h.left_pos)).mp hqt))
    ((Nat.floor_lt (Real.exp_pos t).le).mpr
      ((Real.lt_log_iff_exp_lt (by exact_mod_cast h.right_pos)).mp htr))

theorem active_optimizer_is_recovery {U t : ℝ} (hU : Real.sqrt 2 ≤ U)
    (hUt : 2 * Real.log U < t) {q r : ℕ} (h : IsActiveMangoldtBlock q r)
    (hopt : t = suzukiArchDualOptimizer (suzukiMangoldtSlope q)) :
    SuzukiRecoveryEndpoint U (Real.exp (t / 2)) := by
  have hmem := h.optimizer_mem_Ioo
  rw [← hopt] at hmem
  have hU0 : 0 < U := (Real.sqrt_pos.mpr (by norm_num)).trans_le hU
  have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num)
    (by exact_mod_cast h.1.left_event.two_le)
  have hslope : deriv suzukiPsiArchimedean t = suzukiMangoldtSlope q := by
    rw [hopt]
    exact deriv_archimedean_at_dualOptimizer_of_lt (by rw [← hopt]; exact hlog2.trans_lt hmem.1)
  obtain ⟨k, hk, hkt⟩ := exists_between (max_lt hUt hmem.1)
  have hkU : 2 * Real.log U < k := (le_max_left _ _).trans_lt hk
  have hkq : Real.log q < k := (le_max_right _ _).trans_lt hk
  have hUa : U ≤ Real.exp (k / 2) := by
    rw [← Real.exp_log hU0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hab : Real.exp (k / 2) < Real.exp (t / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hneg : ∀ v : ℝ, Real.exp (k / 2) ≤ v → v < Real.exp (t / 2) →
      suzukiRootSlopeDiscrepancy v < 0 := by
    intro v hav hvb
    have hv0 := (Real.exp_pos (k / 2)).trans_le hav
    have hlo := Real.log_le_log (Real.exp_pos (k / 2)) hav
    have hhi := Real.log_lt_log hv0 hvb
    rw [Real.log_exp] at hlo hhi
    have hqv : Real.log q ≤ 2 * Real.log v := by linarith
    have hvt : 2 * Real.log v < t := by linarith
    have hd := discrepancy_exp_half_eq_on_mangoldtBlock h.1 hqv (hvt.trans hmem.2)
    rw [show 2 * Real.log v / 2 = Real.log v by ring, Real.exp_log hv0] at hd
    rw [hd, ← hslope]
    exact sub_neg.mpr (deriv_suzukiPsiArchimedean_strictMonoOn
      (hlog2.trans hqv) (hlog2.trans hmem.1.le) hvt)
  refine ⟨Real.exp (k / 2), hUa, hneg _ le_rfl hab, hab, ?_, hneg⟩
  rw [discrepancy_exp_half_eq_on_mangoldtBlock h.1 hmem.1.le hmem.2, hslope, sub_self]

/-- Every tail value dominates the initial value or an ACTUAL recovery
value, possibly at a future point. No recovery-time bound is required. -/
theorem suzukiPsiRoot_minimum_covered_by_recovery {U u : ℝ}
    (hU : Real.sqrt 2 ≤ U) (hu : U ≤ u) :
    ∃ c : ℝ, (c = U ∨ SuzukiRecoveryEndpoint U c) ∧
      suzukiPsiRoot c ≤ suzukiPsiRoot u := by
  have hU0 : 0 < U := (Real.sqrt_pos.mpr (by norm_num)).trans_le hU
  have hu0 := hU0.trans_le hu
  obtain ⟨R, huR, hRpos⟩ := suzukiRootSlopeDiscrepancy_cofinal_pos (hU.trans hu)
  have hR0 := hu0.trans huR
  let A := 2 * Real.log U
  let B := 2 * Real.log R
  have hAB : A < B := by
    dsimp [A, B]
    have := Real.log_lt_log hU0 (hu.trans_lt huR)
    linarith
  have hlog2 : Real.log 2 ≤ A := by
    have hh := Real.log_le_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) hU
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
    dsimp [A]
    linarith
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hAB.le)
    continuous_suzukiPsi.continuousOn
  have htu : suzukiPsi t ≤ suzukiPsiRoot u := by
    apply hmin
    constructor
    · dsimp [A]; have := Real.log_le_log hU0 hu; linarith
    · dsimp [B]; have := Real.log_le_log hu0 huR.le; linarith
  by_cases htA : t = A
  · exact ⟨U, Or.inl rfl, by simpa [htA, A, suzukiPsiRoot] using htu⟩
  have hAt : A < t := lt_of_le_of_ne ht.1 (Ne.symm htA)
  have hleft : ∀ᶠ v in 𝓝[<] t, suzukiPsi t ≤ suzukiPsi v := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hAt).filter_mono nhdsWithin_le_nhds] with v hvt hvA
    exact hmin ⟨hvA.le, hvt.le.trans ht.2⟩
  have hn := discrepancy_nonpos_of_psi_min_left (hlog2.trans_lt hAt) hleft
  have htB : t < B := by
    by_contra hnot
    have heq : t = B := le_antisymm ht.2 (le_of_not_gt hnot)
    have hR : Real.exp (t / 2) = R := by rw [heq]; dsimp [B]; rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.exp_log hR0]
    rw [hR] at hn
    exact (not_lt_of_ge hn) hRpos
  have hp := deriv_nonneg_of_min_right (hasDerivWithinAt_suzukiPsi_right (hlog2.trans ht.1)) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds htB).filter_mono nhdsWithin_le_nhds] with v htv hvB
    exact hmin ⟨ht.1.trans htv.le, hvB.le⟩)
  obtain ⟨q, r, hactive, hopt, _, _⟩ := active_block_of_zero_and_min_left
    (hlog2.trans_lt hAt) (le_antisymm hn hp) hleft
  refine ⟨Real.exp (t / 2), Or.inr (active_optimizer_is_recovery hU hAt hactive hopt), ?_⟩
  simpa only [suzukiPsiRoot, Real.log_exp, show 2 * (t / 2) = t by ring] using htu

/-- Constant recovery floors cover every real prefix, including a point
whose chosen minimum is a future recovery. No growing floor is transferred. -/
theorem suzukiPsiRoot_ge_min_of_recovery_floor {U B : ℝ}
    (hU : Real.sqrt 2 ≤ U)
    (hfloor : ∀ b : ℝ, SuzukiRecoveryEndpoint U b → -B ≤ suzukiPsiRoot b)
    {u : ℝ} (hu : U ≤ u) :
    min (suzukiPsiRoot U) (-B) ≤ suzukiPsiRoot u := by
  obtain ⟨c, hc, hcu⟩ := suzukiPsiRoot_minimum_covered_by_recovery hU hu
  rcases hc with rfl | hc
  · exact (min_le_left _ _).trans hcu
  · exact (min_le_right _ _).trans ((hfloor c hc).trans hcu)

/-- A finite uniform recovery allowance is RH-equivalent. This does NOT
assert such an allowance for the actual arithmetic margins. -/
theorem riemannHypothesis_iff_bounded_recovery_floor :
    RiemannHypothesis ↔ ∃ U : ℝ, Real.sqrt 2 ≤ U ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ b : ℝ, SuzukiRecoveryEndpoint U b → -B ≤ suzukiPsiRoot b := by
  constructor
  · intro hRH
    refine ⟨Real.sqrt 2, le_rfl, 0, le_rfl, fun b _ => ?_⟩
    have hp := riemannHypothesis_iff_shifted_zero_nonnegative.mp hRH (2 * Real.log b)
    simpa [suzukiPsiRoot] using hp
  · rintro ⟨U, hU, B, hB, hfloor⟩
    apply riemannHypothesis_iff_suzukiPsi_eventually_bounded_below.mpr
    refine ⟨max B (-suzukiPsiRoot U), hB.trans (le_max_left _ _),
      max 0 (2 * Real.log U), le_max_left _ _, fun t ht => ?_⟩
    have hU0 : 0 < U := (Real.sqrt_pos.mpr (by norm_num)).trans_le hU
    have hu : U ≤ Real.exp (t / 2) := by
      rw [← Real.exp_log hU0]
      apply Real.exp_le_exp.mpr
      have := (le_max_right 0 (2 * Real.log U)).trans ht
      linarith
    have hf := suzukiPsiRoot_ge_min_of_recovery_floor hU hfloor hu
    have hc : -max B (-suzukiPsiRoot U) ≤ min (suzukiPsiRoot U) (-B) := by
      apply le_min <;> linarith [le_max_left B (-suzukiPsiRoot U), le_max_right B (-suzukiPsiRoot U)]
    simpa only [suzukiPsiRoot, Real.log_exp, show 2 * (t / 2) = t by ring] using hc.trans hf

/-- If RH fails, completed actual recoveries have arbitrarily negative
reserve after every cutoff. No rate, density, or endpoint bound is asserted. -/
theorem arbitrarily_deep_recoveries_of_not_RH (hRH : ¬ RiemannHypothesis)
    {U B : ℝ} (hU : Real.sqrt 2 ≤ U) (hB : 0 ≤ B) :
    ∃ a : ℝ, U ≤ a ∧ suzukiRootSlopeDiscrepancy a < 0 ∧
      ∃ b : ℝ, SuzukiFirstRecovery a b ∧ suzukiPsiRoot b < -B := by
  by_contra hn
  apply hRH
  apply riemannHypothesis_iff_bounded_recovery_floor.mpr
  refine ⟨U, hU, B, hB, fun b hb => ?_⟩
  obtain ⟨a, ha, hneg, hab⟩ := hb
  exact le_of_not_gt (fun hlt => hn ⟨a, ha, hneg, b, hab, hlt⟩)

/-- Actual first recoveries are interior minima of active COMPLETE
Mangoldt blocks. This excludes a pre-jump zero at an event endpoint. -/
theorem recoveryEndpoint_active_block {U b : ℝ} (hU : Real.sqrt 2 ≤ U)
    (hb : SuzukiRecoveryEndpoint U b) :
    ∃ q r : ℕ, IsActiveMangoldtBlock q r ∧
      2 * Real.log b = suzukiArchDualOptimizer (suzukiMangoldtSlope q) ∧
      Real.log q < 2 * Real.log b ∧ 2 * Real.log b < Real.log r ∧
      suzukiPsiRoot b = suzukiGlobalDualMargin q := by
  obtain ⟨a, hUa, _, hab, hbzero, hbefore⟩ := hb
  have ha0 : 0 < a := (Real.sqrt_pos.mpr (by norm_num)).trans_le (hU.trans hUa)
  have hb0 : 0 < b := ha0.trans hab
  have hlog2a : Real.log 2 ≤ 2 * Real.log a := by
    have hh := Real.log_le_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) (hU.trans hUa)
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
    linarith
  have hlogab : 2 * Real.log a < 2 * Real.log b := by
    have := Real.log_lt_log ha0 hab
    linarith
  have hexpb : Real.exp ((2 * Real.log b) / 2) = b := by
    rw [show 2 * Real.log b / 2 = Real.log b by ring, Real.exp_log hb0]
  have hleft : ∀ᶠ v in 𝓝[<] (2 * Real.log b),
      suzukiPsi (2 * Real.log b) ≤ suzukiPsi v := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hlogab).filter_mono nhdsWithin_le_nhds] with v hvb hva
    have hI := suzukiPsi_sub_eq_integral_rootDiscrepancy (hlog2a.trans hva.le) hvb.le
    have hnonneg : 0 ≤ ∫ w in v..2 * Real.log b,
        -suzukiRootSlopeDiscrepancy (Real.exp (w / 2)) := by
      apply intervalIntegral.integral_nonneg hvb.le
      intro w hw
      apply neg_nonneg.mpr
      have hwa : a ≤ Real.exp (w / 2) := by
        rw [← Real.exp_log ha0]
        exact Real.exp_le_exp.mpr (by linarith [hw.1])
      have hwb : Real.exp (w / 2) ≤ b := by
        rw [← hexpb]
        exact Real.exp_le_exp.mpr (by linarith [hw.2])
      rcases hwb.eq_or_lt with heq | hlt
      · simpa only [heq, hbzero] using (le_refl (0 : ℝ))
      · exact (hbefore _ hwa hlt).le
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  obtain ⟨q, r, hactive, hopt, hqt, htr⟩ := active_block_of_zero_and_min_left
    (hlog2a.trans_lt hlogab) (by simpa only [hexpb] using hbzero) hleft
  refine ⟨q, r, hactive, hopt, hqt, htr, ?_⟩
  rw [suzukiPsiRoot, hopt,
    ← suzukiMangoldtBlockMargin_eq_psi_optimizer_of_active hactive,
    suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active hactive]

/-- A tail statement on ACTIVE blocks yields a recovery floor at a genuine
event cutoff. Choosing an event at or beyond N explicitly excludes blocks
straddling that cutoff; no unrestricted inactive dual margin is assumed. -/
theorem recovery_floor_of_active_block_tail {B : ℝ} (_hB : 0 ≤ B) {N : ℕ}
    (hfloor : ∀ q r : ℕ, N ≤ q → IsActiveMangoldtBlock q r →
      -B ≤ suzukiGlobalDualMargin q) :
    ∃ p : ℕ, N ≤ p ∧ IsMangoldtEvent p ∧
      ∀ b : ℝ, SuzukiRecoveryEndpoint (Real.sqrt p) b → -B ≤ suzukiPsiRoot b := by
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (max N 2)
  have hp2 : 2 ≤ p := (le_max_right N 2).trans hNp
  have hNp' : N ≤ p := (le_max_left N 2).trans hNp
  have hevent : IsMangoldtEvent p := isMangoldtEvent_iff_primePower.mpr hp.isPrimePow
  refine ⟨p, hNp', hevent, fun b hb => ?_⟩
  have hroot : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp2)
  obtain ⟨q, r, hactive, _, _, htr, hmargin⟩ := recoveryEndpoint_active_block hroot hb
  obtain ⟨a, hpa, _, hab, _, _⟩ := hb
  have hpb : Real.log p < 2 * Real.log b := by
    have hh := Real.log_lt_log (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)) (hpa.trans_lt hab)
    rw [Real.log_sqrt (Nat.cast_nonneg p)] at hh
    linarith
  have hpr : p < r := by
    have hl := hpb.trans htr
    have hc := (Real.log_lt_log_iff (by exact_mod_cast hp.pos)
      (by exact_mod_cast hactive.1.right_pos)).mp hl
    exact_mod_cast hc
  have hpq : p ≤ q := by
    by_contra hn
    exact hevent (hactive.1.eq_zero_between (lt_of_not_ge hn) hpr)
  rw [hmargin]
  exact hfloor q r (hNp'.trans hpq) hactive

/-- The corrected active-block arithmetic target is an equivalence of
OPEN propositions, not a supplied tail estimate. -/
theorem riemannHypothesis_iff_active_block_tail_floor :
    RiemannHypothesis ↔ ∃ B : ℝ, 0 ≤ B ∧ ∃ N : ℕ,
      ∀ q r : ℕ, N ≤ q → IsActiveMangoldtBlock q r →
        -B ≤ suzukiGlobalDualMargin q := by
  constructor
  · intro hRH
    refine ⟨0, le_rfl, 0, fun q r _ h => ?_⟩
    rw [← suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active h,
      suzukiMangoldtBlockMargin_eq_psi_optimizer_of_active h]
    have hp := riemannHypothesis_iff_shifted_zero_nonnegative.mp hRH
      (suzukiArchDualOptimizer (suzukiMangoldtSlope q))
    simpa using hp
  · rintro ⟨B, hB, N, hfloor⟩
    obtain ⟨p, _, hp, hrec⟩ := recovery_floor_of_active_block_tail hB hfloor
    exact riemannHypothesis_iff_bounded_recovery_floor.mpr
      ⟨Real.sqrt p, Real.sqrt_le_sqrt (by exact_mod_cast hp.two_le), B, hB, hrec⟩

end RHGarden
