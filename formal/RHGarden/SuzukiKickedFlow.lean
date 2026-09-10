import RHGarden.SuzukiDualDynamics

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace RHGarden

/-! ## Event-boundary coordinates -/

/-- The value of Suzuki's function at a Mangoldt event boundary. -/
noncomputable def suzukiEventValue (q : ℕ) : ℝ :=
  suzukiPsi (Real.log q)

/-- The logarithmic length of a complete Mangoldt block. -/
noncomputable def suzukiMangoldtLogGap (q r : ℕ) : ℝ :=
  Real.log r - Real.log q

/-- Smooth archimedean slope recovery across a complete block. -/
noncomputable def suzukiArchSlopeDrift (q r : ℕ) : ℝ :=
  deriv suzukiPsiArchimedean (Real.log r) -
    deriv suzukiPsiArchimedean (Real.log q)

/-- The convex Taylor remainder of the archimedean term across a block. -/
noncomputable def suzukiArchConvexRemainder (q r : ℕ) : ℝ :=
  suzukiPsiArchimedean (Real.log r) -
    suzukiPsiArchimedean (Real.log q) -
      deriv suzukiPsiArchimedean (Real.log q) *
        suzukiMangoldtLogGap q r

/-- The smooth profile followed by `Psi` immediately to the right of event
`q`, until the next Mangoldt event. -/
noncomputable def suzukiMangoldtBlockProfile (q : ℕ) (t : ℝ) : ℝ :=
  suzukiPsiArchimedean t - suzukiMangoldtSlope q * t +
    suzukiMangoldtIntercept q

theorem hasDerivAt_suzukiMangoldtBlockProfile (q : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (suzukiMangoldtBlockProfile q)
      (deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q) t := by
  have hlin : HasDerivAt (fun x : ℝ => suzukiMangoldtSlope q * x)
      (suzukiMangoldtSlope q) t := by
    simpa using (hasDerivAt_id t).const_mul (suzukiMangoldtSlope q)
  change HasDerivAt
    (fun x : ℝ => suzukiPsiArchimedean x - suzukiMangoldtSlope q * x +
      suzukiMangoldtIntercept q)
    (deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q) t
  exact ((differentiableAt_suzukiPsiArchimedean_of_pos ht).hasDerivAt.sub
    hlin).add_const (suzukiMangoldtIntercept q)

/-- The derivative of the block profile at its left endpoint is exactly the
post-event slope deficit.  The within derivative records the right-hand
derivative of `Psi`, without differentiating through its kink globally. -/
theorem deriv_suzukiPsi_right_at_event
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    HasDerivWithinAt suzukiPsi (suzukiEventSlopeDeficit q)
      (Icc (Real.log q) (Real.log r)) (Real.log q) := by
  have hqlog : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hp : HasDerivWithinAt (suzukiMangoldtBlockProfile q)
      (suzukiEventSlopeDeficit q) (Icc (Real.log q) (Real.log r))
      (Real.log q) := by
    simpa [suzukiEventSlopeDeficit] using
      (hasDerivAt_suzukiMangoldtBlockProfile q hqlog).hasDerivWithinAt
  exact hp.congr_of_mem
    (fun t ht => suzukiPsi_eq_mangoldtBlock h ht.1 ht.2)
    ⟨le_rfl, Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le)⟩

/-- Exact value component of the kicked convex-flow recurrence. -/
theorem suzukiEventValue_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventValue r = suzukiEventValue q +
      suzukiEventSlopeDeficit q * suzukiMangoldtLogGap q r +
        suzukiArchConvexRemainder q r := by
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le)
  rw [suzukiEventValue, suzukiEventValue,
    suzukiPsi_eq_mangoldtBlock h hlog le_rfl,
    suzukiPsi_eq_mangoldtBlock h le_rfl hlog]
  simp only [suzukiEventSlopeDeficit, suzukiMangoldtLogGap,
    suzukiArchConvexRemainder]
  ring

/-- Exact slope component of the kicked convex-flow recurrence. -/
theorem suzukiEventSlope_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventSlopeDeficit r = suzukiEventSlopeDeficit q +
      suzukiArchSlopeDrift q r - suzukiMangoldtEventWeight r := by
  simpa [suzukiArchSlopeDrift] using suzukiEventSlopeDeficit_next h

/-! ## Strong-convexity flow bounds -/

theorem suzukiMangoldtLogGap_pos
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    0 < suzukiMangoldtLogGap q r := by
  unfold suzukiMangoldtLogGap
  exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast h.left_pos)
    (by exact_mod_cast h.left_lt))

/-- Unit archimedean curvature makes slope recovery dominate logarithmic
elapsed time. -/
theorem logGap_le_archSlopeDrift
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtLogGap q r ≤ suzukiArchSlopeDrift q r := by
  have hqlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)
  have hrlog : Real.log 2 ≤ Real.log r := hqlog.trans
    (Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le))
  have hm := monotoneOn_archDeriv_sub_id hqlog hrlog
    (Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le))
  unfold suzukiMangoldtLogGap suzukiArchSlopeDrift
  linarith

/-- Unit archimedean curvature makes the convex remainder at least half the
square of elapsed logarithmic time. -/
theorem half_logGap_sq_le_archConvexRemainder
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtLogGap q r ^ 2 / 2 ≤
      suzukiArchConvexRemainder q r := by
  have hqlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)
  have hrlog : Real.log 2 ≤ Real.log r := hqlog.trans
    (Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le))
  have hs := suzukiArchimedean_strong_tangent_lower hqlog hrlog
  simp only [suzukiMangoldtLogGap, suzukiArchConvexRemainder]
  linarith

/-- The slope drift is literally the integral of archimedean curvature. -/
theorem suzukiArchSlopeDrift_eq_integral_curvature
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiArchSlopeDrift q r =
      ∫ t in Real.log q..Real.log r, suzukiPsiCurvature t := by
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le)
  have hqpos : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlog
  · intro t ht
    exact (hasDerivAt_deriv_suzukiPsiArchimedean
      (hqpos.trans_le ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact hasDerivAt_deriv_suzukiPsiArchimedean (hqpos.trans ht.1)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlog]
    intro t ht
    have htpos : 0 < t := hqpos.trans_le ht.1
    let y : ℝ → ℝ := fun x => Real.exp (x / 2)
    have hyc : ContinuousAt y t := by dsimp [y]; fun_prop
    have hygt : 1 < y t := by
      dsimp [y]
      rw [← Real.exp_zero, Real.exp_lt_exp]
      linarith
    have hy2gt : 1 < (y t) ^ 2 := by nlinarith [sq_nonneg (y t - 1)]
    have hy4gt : 1 < (y t) ^ 4 := by
      nlinarith [sq_nonneg ((y t) ^ 2 - 1),
        show ((y t) ^ 2) ^ 2 = (y t) ^ 4 by ring]
    change ContinuousWithinAt
      (fun x => y x + 1 / y x - y x ^ 3 / (y x ^ 4 - 1))
      (Icc (Real.log q) (Real.log r)) t
    exact (hyc.add (continuousAt_const.div hyc (by positivity))).sub
      ((hyc.pow 3).div ((hyc.pow 4).sub continuousAt_const)
        (sub_ne_zero.mpr (ne_of_gt hy4gt))) |>.continuousWithinAt

/-- The convex remainder is the accumulated excess slope above its value at
the block entrance. -/
theorem suzukiArchConvexRemainder_eq_integral_slope_excess
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiArchConvexRemainder q r =
      ∫ t in Real.log q..Real.log r,
        (deriv suzukiPsiArchimedean t -
          deriv suzukiPsiArchimedean (Real.log q)) := by
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by exact_mod_cast h.left_pos)
      (by exact_mod_cast h.left_lt.le)
  have hqpos : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hFTC :
      (∫ t in Real.log q..Real.log r, deriv suzukiPsiArchimedean t) =
        suzukiPsiArchimedean (Real.log r) -
          suzukiPsiArchimedean (Real.log q) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlog
    · intro t ht
      exact (differentiableAt_suzukiPsiArchimedean_of_pos
        (hqpos.trans_le ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      exact (differentiableAt_suzukiPsiArchimedean_of_pos
        (hqpos.trans ht.1)).hasDerivAt
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hlog]
      intro t ht
      exact (hasDerivAt_deriv_suzukiPsiArchimedean
        (hqpos.trans_le ht.1)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (deriv suzukiPsiArchimedean)
      MeasureTheory.volume (Real.log q) (Real.log r) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlog]
    intro t ht
    exact (hasDerivAt_deriv_suzukiPsiArchimedean
      (hqpos.trans_le ht.1)).continuousAt.continuousWithinAt
  have hconst : IntervalIntegrable
      (fun _t : ℝ => deriv suzukiPsiArchimedean (Real.log q))
      MeasureTheory.volume (Real.log q) (Real.log r) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hint hconst, hFTC]
  simp only [intervalIntegral.integral_const]
  unfold suzukiArchConvexRemainder suzukiMangoldtLogGap
  ring

/-! ## A strong-convexity safety certificate -/

/-- The nonnegative magnitude of a descending slope. -/
noncomputable def suzukiNegativePart (d : ℝ) : ℝ := max (-d) 0

theorem suzukiNegativePart_nonneg (d : ℝ) : 0 ≤ suzukiNegativePart d := by
  exact le_max_right _ _

/-- Boundary value after reserving the worst quadratic drawdown permitted by
unit strong convexity. -/
noncomputable def suzukiEventSafetyEnergy (q : ℕ) : ℝ :=
  suzukiEventValue q - suzukiNegativePart (suzukiEventSlopeDeficit q) ^ 2 / 2

private theorem negativePart_quadratic_lower (d x : ℝ) (hx : 0 ≤ x) :
    -(suzukiNegativePart d) ^ 2 / 2 ≤ d * x + x ^ 2 / 2 := by
  by_cases hd : 0 ≤ d
  · have hneg : suzukiNegativePart d = 0 := by
      simp [suzukiNegativePart, max_eq_right, hd]
    rw [hneg]
    nlinarith [sq_nonneg x]
  · have hd' : d < 0 := lt_of_not_ge hd
    have hneg : suzukiNegativePart d = -d := by
      simp [suzukiNegativePart, max_eq_left, le_of_lt hd']
    rw [hneg]
    nlinarith [sq_nonneg (x + d)]

/-- The safety energy is a certified lower bound for `Psi` at every point
of the complete block beginning at `q`. -/
theorem eventSafetyEnergy_le_suzukiPsi_on_block
    {q r : ℕ} (h : IsMangoldtBlock q r)
    {t : ℝ} (htq : Real.log q ≤ t) (htr : t ≤ Real.log r) :
    suzukiEventSafetyEnergy q ≤ suzukiPsi t := by
  have hqlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)
  have htlog : Real.log 2 ≤ t := hqlog.trans htq
  have hs := suzukiArchimedean_strong_tangent_lower hqlog htlog
  have hquad := negativePart_quadratic_lower
    (suzukiEventSlopeDeficit q) (t - Real.log q) (sub_nonneg.mpr htq)
  unfold suzukiEventSafetyEnergy suzukiEventValue
  rw [suzukiPsi_eq_mangoldtBlock h htq htr,
    suzukiPsi_eq_mangoldtBlock h le_rfl
      (Real.log_le_log (by exact_mod_cast h.left_pos)
        (by exact_mod_cast h.left_lt.le))]
  unfold suzukiEventSlopeDeficit at hquad ⊢
  nlinarith

/-- A nonnegative boundary safety energy certifies the whole following
Mangoldt block. -/
theorem mangoldtBlock_nonnegative_of_eventSafetyEnergy
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hE : 0 ≤ suzukiEventSafetyEnergy q) :
    ∀ t, Real.log q ≤ t → t ≤ Real.log r → 0 ≤ suzukiPsi t := by
  intro t htq htr
  exact hE.trans (eventSafetyEnergy_le_suzukiPsi_on_block h htq htr)

/-- Safety energy is a conservative lower bound for the exact block
minimum. -/
theorem eventSafetyEnergy_le_blockMargin
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventSafetyEnergy q ≤ suzukiMangoldtBlockMargin q r := by
  obtain ⟨t, ht, hmargin, _⟩ := mangoldtBlockMargin_eq_minimum h
  rw [hmargin]
  exact eventSafetyEnergy_le_suzukiPsi_on_block h ht.1 ht.2

/-- The compact initial interval plus nonnegative event safety at every
complete block is a sufficient criterion for RH.  No premise is discharged
here. -/
theorem riemannHypothesis_of_initial_and_eventSafety
    (hinit : SuzukiInitialNonnegative)
    (hE : ∀ q r : ℕ, IsMangoldtBlock q r →
      0 ≤ suzukiEventSafetyEnergy q) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_initial_and_all_mangoldtBlockMargins]
  refine ⟨hinit, ?_⟩
  intro q r h
  exact (hE q r h).trans (eventSafetyEnergy_le_blockMargin h)

/-! ## Fenchel-gap interpretation -/

/-- The Fenchel gap between the event location and the arithmetic slope. -/
noncomputable def suzukiEventFenchelGap (q : ℕ) : ℝ :=
  suzukiPsiArchimedean (Real.log q) +
    suzukiArchDual (suzukiMangoldtSlope q) -
      suzukiMangoldtSlope q * Real.log q

theorem suzukiEventFenchelGap_nonneg
    {q : ℕ} (hq : 2 ≤ q) :
    0 ≤ suzukiEventFenchelGap q := by
  have hlog : Real.log q ∈ Ici (Real.log 2) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hm := suzukiArchDualOptimizer_isMaxOn (suzukiMangoldtSlope q) hlog
  change suzukiArchCellObjective (suzukiMangoldtSlope q) (Real.log q) ≤
    suzukiArchCellObjective (suzukiMangoldtSlope q)
      (suzukiArchDualOptimizer (suzukiMangoldtSlope q)) at hm
  unfold suzukiEventFenchelGap
  rw [suzukiArchDual_eq_optimizer]
  unfold suzukiArchCellObjective at hm
  linarith

/-- The event value is the global dual margin plus its nonnegative Fenchel
gap. -/
theorem suzukiEventValue_eq_globalDualMargin_add_fenchelGap
    {q : ℕ} (hq : 2 ≤ q) :
    suzukiEventValue q = suzukiGlobalDualMargin q +
      suzukiEventFenchelGap q := by
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hnext : Real.log q ≤ Real.log (q + 1) :=
    Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hq))
      (by exact_mod_cast Nat.le_succ q)
  rw [suzukiEventValue,
    suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      hq1 le_rfl hnext]
  unfold suzukiGlobalDualMargin suzukiEventFenchelGap
  ring

/-- Unit strong convexity of `A` makes the conjugate Fenchel gap no larger
than half the squared slope mismatch. -/
theorem suzukiArchFenchelGap_le_half_slope_sq
    {S t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiPsiArchimedean t + suzukiArchDual S - S * t ≤
      (deriv suzukiPsiArchimedean t - S) ^ 2 / 2 := by
  let p := deriv suzukiPsiArchimedean t
  have hopt : suzukiArchDualOptimizer p = t :=
    suzukiArchDualOptimizer_deriv_archimedean ht
  have hdualP : suzukiArchDual p = p * t - suzukiPsiArchimedean t := by
    rw [suzukiArchDual_eq_optimizer, hopt]
  rcases le_total S p with hSp | hpS
  · have hinc : suzukiArchDual p - suzukiArchDual S =
        ∫ s in S..p, suzukiArchDualOptimizer s := by
      convert suzukiArchDual_sub_eq_integral_optimizer
        (S := S) (lambda := p - S) (sub_nonneg.mpr hSp) using 1 <;> ring
    have hInt :
        (∫ s in S..p, (t - suzukiArchDualOptimizer s)) ≤
          ∫ s in S..p, (p - s) := by
      apply intervalIntegral.integral_mono_on hSp
        ((continuous_const.sub continuous_suzukiArchDualOptimizer).intervalIntegrable _ _)
        ((continuous_const.sub continuous_id).intervalIntegrable _ _)
      intro s hs
      have hlip := suzukiArchDualOptimizer_lipschitz.dist_le_mul p s
      rw [Real.dist_eq, Real.dist_eq] at hlip
      norm_num at hlip
      rw [hopt, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hlip
      exact (le_abs_self _).trans hlip
    have hleft :
        (∫ s in S..p, (t - suzukiArchDualOptimizer s)) =
          (p - S) * t - (suzukiArchDual p - suzukiArchDual S) := by
      rw [intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        (continuous_suzukiArchDualOptimizer.intervalIntegrable _ _), hinc]
      simp only [intervalIntegral.integral_const]
      ring
    have hright : (∫ s in S..p, (p - s)) = (p - S) ^ 2 / 2 := by
      change (∫ s in S..p, (fun _x : ℝ => p) s - id s) = _
      rw [intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)]
      simp only [Function.id_def, intervalIntegral.integral_const, integral_id]
      ring
    rw [hleft, hright] at hInt
    dsimp [p] at hInt hdualP ⊢
    nlinarith [hdualP]
  · have hinc : suzukiArchDual S - suzukiArchDual p =
        ∫ s in p..S, suzukiArchDualOptimizer s := by
      convert suzukiArchDual_sub_eq_integral_optimizer
        (S := p) (lambda := S - p) (sub_nonneg.mpr hpS) using 1 <;> ring
    have hInt :
        (∫ s in p..S, (suzukiArchDualOptimizer s - t)) ≤
          ∫ s in p..S, (s - p) := by
      apply intervalIntegral.integral_mono_on hpS
        ((continuous_suzukiArchDualOptimizer.sub continuous_const).intervalIntegrable _ _)
        ((continuous_id.sub continuous_const).intervalIntegrable _ _)
      intro s hs
      have hlip := suzukiArchDualOptimizer_lipschitz.dist_le_mul s p
      rw [Real.dist_eq, Real.dist_eq] at hlip
      norm_num at hlip
      rw [hopt, abs_of_nonneg (sub_nonneg.mpr hs.1)] at hlip
      exact (le_abs_self _).trans hlip
    have hleft :
        (∫ s in p..S, (suzukiArchDualOptimizer s - t)) =
          (suzukiArchDual S - suzukiArchDual p) - (S - p) * t := by
      rw [intervalIntegral.integral_sub
        (continuous_suzukiArchDualOptimizer.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), hinc]
      simp only [intervalIntegral.integral_const]
      ring
    have hright : (∫ s in p..S, (s - p)) = (S - p) ^ 2 / 2 := by
      change (∫ s in p..S, id s - (fun _x : ℝ => p) s) = _
      rw [intervalIntegral.integral_sub
        (continuous_id.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)]
      simp only [Function.id_def, intervalIntegral.integral_const, integral_id]
      ring
    rw [hleft, hright] at hInt
    dsimp [p] at hInt hdualP ⊢
    nlinarith [hdualP]

theorem suzukiEventFenchelGap_le_half_deficit_sq
    {q : ℕ} (hq : 2 ≤ q) :
    suzukiEventFenchelGap q ≤ suzukiEventSlopeDeficit q ^ 2 / 2 := by
  have hlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  simpa [suzukiEventFenchelGap, suzukiEventSlopeDeficit] using
    (suzukiArchFenchelGap_le_half_slope_sq
      (S := suzukiMangoldtSlope q) hlog)

/-- On a descending event boundary, safety energy is also a lower bound for
the unrestricted global dual margin. -/
theorem eventSafetyEnergy_le_globalDualMargin_of_deficit_nonpos
    {q : ℕ} (hq : 2 ≤ q) (hd : suzukiEventSlopeDeficit q ≤ 0) :
    suzukiEventSafetyEnergy q ≤ suzukiGlobalDualMargin q := by
  have hdecomp := suzukiEventValue_eq_globalDualMargin_add_fenchelGap hq
  have hgap := suzukiEventFenchelGap_le_half_deficit_sq hq
  have hneg : suzukiNegativePart (suzukiEventSlopeDeficit q) =
      -suzukiEventSlopeDeficit q := by
    simp [suzukiNegativePart, max_eq_left, hd]
  unfold suzukiEventSafetyEnergy
  rw [hneg]
  nlinarith

/-! ## Optimizer displacement and kick response -/

/-- Event location relative to the unrestricted optimizer of its post-event
arithmetic slope. -/
noncomputable def suzukiEventOptimizerDisplacement (q : ℕ) : ℝ :=
  Real.log q - suzukiArchDualOptimizer (suzukiMangoldtSlope q)

/-- Rightward movement of the dual optimizer caused by the event impulse at
`r`. -/
noncomputable def suzukiOptimizerKickDisplacement (q r : ℕ) : ℝ :=
  suzukiArchDualOptimizer
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) -
    suzukiArchDualOptimizer (suzukiMangoldtSlope q)

theorem suzukiOptimizerKickDisplacement_nonneg (q r : ℕ) :
    0 ≤ suzukiOptimizerKickDisplacement q r := by
  unfold suzukiOptimizerKickDisplacement
  exact sub_nonneg.mpr (suzukiArchDualOptimizer_monotone
    (le_add_of_nonneg_right (suzukiMangoldtEventWeight_nonneg r)))

theorem suzukiOptimizerKickDisplacement_le_weight (q r : ℕ) :
    suzukiOptimizerKickDisplacement q r ≤ suzukiMangoldtEventWeight r := by
  unfold suzukiOptimizerKickDisplacement
  have h := suzukiArchDualOptimizer_lipschitz.dist_le_mul
    (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r)
    (suzukiMangoldtSlope q)
  rw [Real.dist_eq, Real.dist_eq] at h
  norm_num at h
  rw [abs_of_nonneg (suzukiMangoldtEventWeight_nonneg r)] at h
  exact (le_abs_self _).trans h

/-- The optimizer displacement follows a sawtooth recurrence: free motion
by the logarithmic gap, followed by the optimizer's response to the next
Mangoldt kick. -/
theorem suzukiEventOptimizerDisplacement_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventOptimizerDisplacement r =
      suzukiEventOptimizerDisplacement q + suzukiMangoldtLogGap q r -
        suzukiOptimizerKickDisplacement q r := by
  rw [suzukiEventOptimizerDisplacement, suzukiEventOptimizerDisplacement,
    suzukiOptimizerKickDisplacement, mangoldtSlope_right_event h]
  unfold suzukiMangoldtLogGap
  ring

/-- A block is active exactly when the frozen optimizer is to the right of
its entrance but to the left of its exit. -/
theorem isActiveMangoldtBlock_iff_displacement_crossing
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsActiveMangoldtBlock q r ↔
      suzukiEventOptimizerDisplacement q < 0 ∧
        0 < suzukiEventOptimizerDisplacement q +
          suzukiMangoldtLogGap q r := by
  rw [isActiveMangoldtBlock_iff_optimizer_mem h]
  unfold suzukiEventOptimizerDisplacement suzukiMangoldtLogGap
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Area swept by the optimizer during the kick at `r`, based at the
pre-kick state from event `q`.  The slope-coordinate form avoids an
unnecessary change-of-variables theorem. -/
noncomputable def suzukiOptimizerKickArea (q r : ℕ) : ℝ :=
  ∫ s in suzukiMangoldtSlope q..
      suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
    (suzukiArchDualOptimizer s -
      suzukiArchDualOptimizer (suzukiMangoldtSlope q))

theorem suzukiOptimizerKickArea_nonneg (q r : ℕ) :
    0 ≤ suzukiOptimizerKickArea q r := by
  unfold suzukiOptimizerKickArea
  apply intervalIntegral.integral_nonneg
    (by linarith [suzukiMangoldtEventWeight_nonneg r])
  intro s hs
  exact sub_nonneg.mpr (suzukiArchDualOptimizer_monotone hs.1)

/-- The kick area is at most the triangular `lambda^2/2` envelope supplied
by the one-Lipschitz optimizer. -/
theorem suzukiOptimizerKickArea_le_half_sq (q r : ℕ) :
    suzukiOptimizerKickArea q r ≤ suzukiMangoldtEventWeight r ^ 2 / 2 := by
  let S := suzukiMangoldtSlope q
  let lambda := suzukiMangoldtEventWeight r
  have hlambda : 0 ≤ lambda := suzukiMangoldtEventWeight_nonneg r
  have hmonoInt :
      (∫ s in S..S + lambda,
          (suzukiArchDualOptimizer s - suzukiArchDualOptimizer S)) ≤
        ∫ s in S..S + lambda, (s - S) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      ((continuous_suzukiArchDualOptimizer.sub continuous_const).intervalIntegrable _ _)
      ((continuous_id.sub continuous_const).intervalIntegrable _ _)
    intro s hs
    have hlip := suzukiArchDualOptimizer_lipschitz.dist_le_mul s S
    rw [Real.dist_eq, Real.dist_eq] at hlip
    norm_num at hlip
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)] at hlip
    exact (le_abs_self _).trans hlip
  have hlinear :
      (∫ s in S..S + lambda, (s - S)) = lambda ^ 2 / 2 := by
    have hid : Continuous (fun s : ℝ => s) := continuous_id
    have hc : Continuous (fun _s : ℝ => S) := continuous_const
    rw [intervalIntegral.integral_sub (hid.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    simp only [integral_id, intervalIntegral.integral_const]
    ring
  dsimp [S, lambda] at hmonoInt hlinear ⊢
  rw [hlinear] at hmonoInt
  exact hmonoInt

private theorem mangoldtIntercept_right_event
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtIntercept r = suzukiMangoldtIntercept q +
      suzukiMangoldtEventWeight r * Real.log r := by
  have hrpos : 0 < r := h.right_pos
  have hpred : q ≤ r - 1 := Nat.le_sub_one_of_lt h.left_lt
  have hpredlt : r - 1 < r := Nat.sub_lt hrpos (by omega)
  have hstate := mangoldtIntercept_eq_on_block h hpred hpredlt
  have hsucc := suzukiMangoldtIntercept_succ (r - 1)
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrpos)
  rw [Nat.sub_add_cancel hr1] at hsucc
  have hcast : (((r - 1 : ℕ) : ℝ) + 1) = (r : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hr1
  rw [hcast] at hsucc
  rw [hsucc, hstate]
  unfold suzukiMangoldtEventWeight
  ring

/-- The global dual-margin update is free gap gain minus the optimizer's
kick-response area. -/
theorem globalDualMargin_block_update_kickArea
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q =
      suzukiMangoldtEventWeight r *
          (suzukiEventOptimizerDisplacement q +
            suzukiMangoldtLogGap q r) -
        suzukiOptimizerKickArea q r := by
  have hlambda : 0 ≤ suzukiMangoldtEventWeight r :=
    suzukiMangoldtEventWeight_nonneg r
  have hdual := suzukiArchDual_sub_eq_integral_optimizer
    (S := suzukiMangoldtSlope q) hlambda
  rw [suzukiGlobalDualMargin, suzukiGlobalDualMargin,
    mangoldtSlope_right_event h, mangoldtIntercept_right_event h]
  have hconst :
      (∫ _s in suzukiMangoldtSlope q..
          suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
        suzukiArchDualOptimizer (suzukiMangoldtSlope q)) =
        suzukiMangoldtEventWeight r *
          suzukiArchDualOptimizer (suzukiMangoldtSlope q) := by
    simp [hlambda]
  have hintOpt : IntervalIntegrable suzukiArchDualOptimizer MeasureTheory.volume
      (suzukiMangoldtSlope q)
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) :=
    continuous_suzukiArchDualOptimizer.intervalIntegrable _ _
  have hintConst : IntervalIntegrable
      (fun _s : ℝ => suzukiArchDualOptimizer (suzukiMangoldtSlope q))
      MeasureTheory.volume (suzukiMangoldtSlope q)
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) :=
    continuous_const.intervalIntegrable _ _
  calc
    _ = suzukiMangoldtEventWeight r * Real.log r -
        (suzukiArchDual
            (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) -
          suzukiArchDual (suzukiMangoldtSlope q)) := by ring
    _ = suzukiMangoldtEventWeight r * Real.log r -
        ∫ s in suzukiMangoldtSlope q..
            suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
          suzukiArchDualOptimizer s := by rw [hdual]
    _ = _ := by
      unfold suzukiOptimizerKickArea suzukiEventOptimizerDisplacement
        suzukiMangoldtLogGap
      rw [intervalIntegral.integral_sub hintOpt hintConst, hconst]
      ring

/-- Immediate event-update bounds in displacement coordinates. -/
theorem globalDualMargin_block_update_kickArea_bounds
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtEventWeight r *
          (suzukiEventOptimizerDisplacement q + suzukiMangoldtLogGap q r) -
        suzukiMangoldtEventWeight r ^ 2 / 2 ≤
      suzukiGlobalDualMargin r - suzukiGlobalDualMargin q ∧
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q ≤
      suzukiMangoldtEventWeight r *
        (suzukiEventOptimizerDisplacement q + suzukiMangoldtLogGap q r) := by
  rw [globalDualMargin_block_update_kickArea h]
  constructor
  · linarith [suzukiOptimizerKickArea_le_half_sq q r]
  · linarith [suzukiOptimizerKickArea_nonneg q r]

end RHGarden
