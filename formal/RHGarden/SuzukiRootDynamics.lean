import RHGarden.SuzukiTrueCurvature

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace RHGarden

/-! ## Elementary curvature in the square-root coordinate -/

/-- The dimensionless correction multiplying the leading root-coordinate
curvature. -/
def suzukiCurvatureFactor (u : ℝ) : ℝ :=
  1 - 1 / (u ^ 2 * (u ^ 4 - 1))

theorem secondDeriv_arch_eq_u_mul_factor
    {t : ℝ} (ht : 0 < t) :
    deriv (deriv suzukiPsiArchimedean) t =
      Real.exp (t / 2) * suzukiCurvatureFactor (Real.exp (t / 2)) := by
  simpa [suzukiCurvatureFactor] using secondDeriv_arch_eq_exp_mul_factor ht

private theorem curvatureFactor_den_ge_six
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    (6 : ℝ) ≤ u ^ 2 * (u ^ 4 - 1) := by
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg 2).trans hu
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hu2 : (2 : ℝ) ≤ u ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu),
      mul_nonneg (Real.sqrt_nonneg 2) (sub_nonneg.mpr hu)]
  have hu4 : (4 : ℝ) ≤ u ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2 - 2), show (u ^ 2) ^ 2 = u ^ 4 by ring]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu2)
    (sub_nonneg.mpr (show 3 ≤ u ^ 4 - 1 by linarith))]

theorem five_sixths_le_suzukiCurvatureFactor
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    (5 / 6 : ℝ) ≤ suzukiCurvatureFactor u := by
  have hden := curvatureFactor_den_ge_six hu
  have hinv : 1 / (u ^ 2 * (u ^ 4 - 1)) ≤ (1 / 6 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hden
  unfold suzukiCurvatureFactor
  linarith

theorem suzukiCurvatureFactor_lt_one
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    suzukiCurvatureFactor u < 1 := by
  have hden : 0 < u ^ 2 * (u ^ 4 - 1) :=
    lt_of_lt_of_le (by norm_num) (curvatureFactor_den_ge_six hu)
  have hinv : 0 < 1 / (u ^ 2 * (u ^ 4 - 1)) := one_div_pos.mpr hden
  unfold suzukiCurvatureFactor
  linarith

theorem suzukiCurvatureFactor_pos
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    0 < suzukiCurvatureFactor u :=
  lt_of_lt_of_le (by norm_num) (five_sixths_le_suzukiCurvatureFactor hu)

theorem continuousAt_suzukiCurvatureFactor
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    ContinuousAt suzukiCurvatureFactor u := by
  have hden : u ^ 2 * (u ^ 4 - 1) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (curvatureFactor_den_ge_six hu))
  unfold suzukiCurvatureFactor
  fun_prop

/-! ## The dual optimizer in root coordinates -/

/-- The natural root coordinate `uStar(S)=exp(tStar(S)/2)` of the
archimedean dual optimizer. -/
noncomputable def suzukiArchDualRoot (S : ℝ) : ℝ :=
  Real.exp (suzukiArchDualOptimizer S / 2)

theorem suzukiArchDualRoot_pos (S : ℝ) :
    0 < suzukiArchDualRoot S := by
  unfold suzukiArchDualRoot
  positivity

theorem continuous_suzukiArchDualRoot :
    Continuous suzukiArchDualRoot := by
  unfold suzukiArchDualRoot
  exact Real.continuous_exp.comp
    (continuous_suzukiArchDualOptimizer.div_const 2)

private theorem exp_half_log_nat_eq_sqrt
    {n : ℕ} (hn : 0 < n) :
    Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt n := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [← Real.log_sqrt (by positivity), Real.exp_log hsqrtpos]

theorem sqrt_two_le_suzukiArchDualRoot (S : ℝ) :
    Real.sqrt 2 ≤ suzukiArchDualRoot S := by
  change Real.sqrt (2 : ℝ) ≤ suzukiArchDualRoot S
  have hsqrt : Real.exp (Real.log (2 : ℝ) / 2) = Real.sqrt (2 : ℝ) := by
    have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    rw [← Real.log_sqrt (by norm_num), Real.exp_log hsqrtpos]
  rw [← hsqrt]
  unfold suzukiArchDualRoot
  exact Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (suzukiArchDualOptimizer_mem_Ici S) (by norm_num))

theorem suzukiArchDualOptimizer_eq_two_mul_log_root (S : ℝ) :
    suzukiArchDualOptimizer S = 2 * Real.log (suzukiArchDualRoot S) := by
  unfold suzukiArchDualRoot
  rw [Real.log_exp]
  ring

theorem archSlope_at_root
    {S : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    deriv suzukiPsiArchimedean
        (2 * Real.log (suzukiArchDualRoot S)) = S := by
  rw [← suzukiArchDualOptimizer_eq_two_mul_log_root]
  exact deriv_archimedean_at_dualOptimizer hS

private theorem hasDerivAt_suzukiArchDualOptimizer_of_interior
    {S : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    HasDerivAt suzukiArchDualOptimizer
      (suzukiPsiCurvature (suzukiArchDualOptimizer S))⁻¹ S := by
  have htmem := suzukiArchDualOptimizer_mem_Ici S
  have htlt : Real.log 2 < suzukiArchDualOptimizer S := by
    exact lt_of_le_of_ne htmem (fun heq =>
      (not_le_of_gt hS) (le_archDeriv_log_two_of_optimizer_eq heq.symm))
  have htpos : 0 < suzukiArchDualOptimizer S :=
    (Real.log_pos (by norm_num)).trans htlt
  have hcurv : suzukiPsiCurvature (suzukiArchDualOptimizer S) ≠ 0 := by
    rw [← secondDeriv_suzukiPsiArchimedean htpos]
    exact ne_of_gt (lt_of_lt_of_le (by positivity)
      (five_sixths_exp_le_secondDeriv_arch htmem))
  apply (hasDerivAt_deriv_suzukiPsiArchimedean htpos).of_local_left_inverse
    continuous_suzukiArchDualOptimizer.continuousAt hcurv
  filter_upwards [eventually_gt_nhds hS] with y hy
  exact deriv_archimedean_at_dualOptimizer hy

/-- In the interior optimizer regime, the root coordinate has the elementary
derivative `1/(2*F(uStar))`. -/
theorem hasDerivAt_suzukiArchDualRoot
    {S : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    HasDerivAt suzukiArchDualRoot
      (1 / (2 * suzukiCurvatureFactor (suzukiArchDualRoot S))) S := by
  have ht := hasDerivAt_suzukiArchDualOptimizer_of_interior hS
  have hinner := ht.div_const (2 : ℝ)
  have hcomp := (Real.hasDerivAt_exp
    (suzukiArchDualOptimizer S / 2)).comp S hinner
  have htlt : Real.log 2 < suzukiArchDualOptimizer S := by
    have htmem := suzukiArchDualOptimizer_mem_Ici S
    exact lt_of_le_of_ne htmem (fun heq =>
      (not_le_of_gt hS) (le_archDeriv_log_two_of_optimizer_eq heq.symm))
  have htpos : 0 < suzukiArchDualOptimizer S :=
    (Real.log_pos (by norm_num)).trans htlt
  have hfactor := secondDeriv_arch_eq_u_mul_factor htpos
  have hcurv := (secondDeriv_suzukiPsiArchimedean htpos).symm.trans hfactor
  have hrootpos := suzukiArchDualRoot_pos S
  have hfactorpos := suzukiCurvatureFactor_pos
    (sqrt_two_le_suzukiArchDualRoot S)
  have hcoeff :
      Real.exp (suzukiArchDualOptimizer S / 2) *
          ((suzukiPsiCurvature (suzukiArchDualOptimizer S))⁻¹ / 2) =
        1 / (2 * suzukiCurvatureFactor (suzukiArchDualRoot S)) := by
    rw [hcurv]
    unfold suzukiArchDualRoot
    field_simp
  rw [← hcoeff]
  apply hcomp.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem half_lt_deriv_suzukiArchDualRoot
    {S : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    (1 / 2 : ℝ) < deriv suzukiArchDualRoot S := by
  rw [(hasDerivAt_suzukiArchDualRoot hS).deriv]
  have hFpos := suzukiCurvatureFactor_pos (sqrt_two_le_suzukiArchDualRoot S)
  have hFlt := suzukiCurvatureFactor_lt_one (sqrt_two_le_suzukiArchDualRoot S)
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    (mul_pos (by norm_num) hFpos)).2
  nlinarith

theorem deriv_suzukiArchDualRoot_le_three_fifths
    {S : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    deriv suzukiArchDualRoot S ≤ (3 / 5 : ℝ) := by
  rw [(hasDerivAt_suzukiArchDualRoot hS).deriv]
  have hF := five_sixths_le_suzukiCurvatureFactor
    (sqrt_two_le_suzukiArchDualRoot S)
  have hFpos := suzukiCurvatureFactor_pos (sqrt_two_le_suzukiArchDualRoot S)
  apply (div_le_iff₀ (mul_pos (by norm_num) hFpos)).2
  nlinarith

/-- In the interior optimizer regime, an increment of the slope by `lambda`
moves the natural root coordinate by between `lambda/2` and `3*lambda/5`. -/
theorem suzukiArchDualRoot_increment_bounds
    {S lambda : ℝ}
    (hS : deriv suzukiPsiArchimedean (Real.log 2) < S)
    (hlambda : 0 ≤ lambda) :
    lambda / 2 ≤ suzukiArchDualRoot (S + lambda) - suzukiArchDualRoot S ∧
      suzukiArchDualRoot (S + lambda) - suzukiArchDualRoot S ≤
        3 * lambda / 5 := by
  rcases hlambda.eq_or_lt with rfl | hlambda
  · simp
  · have hcont : ContinuousOn suzukiArchDualRoot (Icc S (S + lambda)) :=
      continuous_suzukiArchDualRoot.continuousOn
    have hdiff : DifferentiableOn ℝ suzukiArchDualRoot (Ioo S (S + lambda)) := by
      intro s hs
      exact (hasDerivAt_suzukiArchDualRoot (hS.trans hs.1)).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope suzukiArchDualRoot
      (by linarith : S < S + lambda) hcont hdiff
    have hslope' : deriv suzukiArchDualRoot c =
        (suzukiArchDualRoot (S + lambda) - suzukiArchDualRoot S) / lambda := by
      simpa only [add_sub_cancel_left] using hslope
    have heq : deriv suzukiArchDualRoot c * lambda =
        suzukiArchDualRoot (S + lambda) - suzukiArchDualRoot S :=
      (eq_div_iff (ne_of_gt hlambda)).mp hslope'
    have hlo := half_lt_deriv_suzukiArchDualRoot (hS.trans hc.1)
    have hhi := deriv_suzukiArchDualRoot_le_three_fifths (hS.trans hc.1)
    constructor <;> nlinarith

theorem suzukiArchDualRoot_monotone :
    Monotone suzukiArchDualRoot := by
  intro S₁ S₂ hS
  unfold suzukiArchDualRoot
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (suzukiArchDualOptimizer_monotone hS) (by norm_num))

/-! ## The interior regime for every arithmetic event state -/

theorem suzukiMangoldtSlope_monotone :
    Monotone suzukiMangoldtSlope := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      rw [suzukiMangoldtSlope_succ]
      exact ih.trans (le_add_of_nonneg_right
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.sqrt_nonneg _)))

/-- The exact cell-two derivative bounds place the first arithmetic slope
strictly above the boundary slope of the half-line dual. -/
theorem archDeriv_log_two_lt_suzukiMangoldtSlope_two :
    deriv suzukiPsiArchimedean (Real.log 2) < suzukiMangoldtSlope 2 := by
  have hlog2le : Real.log 2 ≤ (9 : ℝ) / 10 := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hmono := monotoneOn_archDeriv_sub_id
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hlog2le) hlog2le
  have hcell := deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_cell
    (n := 2) (t := (9 : ℝ) / 10) (by norm_num)
      (by
        have h := Real.log_two_lt_d9
        norm_num at h ⊢
        linarith)
      (by
        have h := Real.log_three_gt_d9
        norm_num at h ⊢
        linarith)
  have hderiv : deriv suzukiPsi ((9 : ℝ) / 10) ≤ (13 : ℝ) / 100 :=
    (le_abs_self _).trans abs_deriv_suzukiPsi_nine_tenths_le
  have hloghi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    convert Real.log_two_lt_d9 using 1 <;> norm_num
  rw [hcell] at hderiv
  norm_num at hmono hderiv hloghi ⊢
  linarith

theorem archDeriv_log_two_lt_suzukiMangoldtSlope_of_two_le
    {q : ℕ} (hq : 2 ≤ q) :
    deriv suzukiPsiArchimedean (Real.log 2) < suzukiMangoldtSlope q :=
  archDeriv_log_two_lt_suzukiMangoldtSlope_two.trans_le
    (suzukiMangoldtSlope_monotone hq)

theorem archDeriv_log_two_lt_suzukiMangoldtSlope_of_event
    {q : ℕ} (hq : IsMangoldtEvent q) :
    deriv suzukiPsiArchimedean (Real.log 2) < suzukiMangoldtSlope q :=
  archDeriv_log_two_lt_suzukiMangoldtSlope_of_two_le hq.two_le

/-! ## Mangoldt events in the root coordinate -/

/-- Event location minus the root-coordinate optimizer.  Positive values
mean that the optimizer is to the left of the event. -/
noncomputable def suzukiRootDisplacement (q : ℕ) : ℝ :=
  Real.sqrt q - suzukiArchDualRoot (suzukiMangoldtSlope q)

/-- The optimizer's root-coordinate response to the Mangoldt impulse at the
right endpoint `r` of a block starting at `q`. -/
noncomputable def suzukiRootKick (q r : ℕ) : ℝ :=
  suzukiArchDualRoot
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) -
    suzukiArchDualRoot (suzukiMangoldtSlope q)

theorem suzukiRootKick_nonneg (q r : ℕ) :
    0 ≤ suzukiRootKick q r := by
  unfold suzukiRootKick
  exact sub_nonneg.mpr (suzukiArchDualRoot_monotone
    (le_add_of_nonneg_right (suzukiMangoldtEventWeight_nonneg r)))

theorem suzukiRootKick_eq_state_sub
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootKick q r =
      suzukiArchDualRoot (suzukiMangoldtSlope r) -
        suzukiArchDualRoot (suzukiMangoldtSlope q) := by
  rw [suzukiRootKick, mangoldtSlope_right_event h]

/-- Sharp root-coordinate kick bounds, conditional only on the pre-event
slope lying in the interior optimizer regime. -/
theorem suzukiRootKick_bounds
    {q r : ℕ}
    (hinterior : deriv suzukiPsiArchimedean (Real.log 2) <
      suzukiMangoldtSlope q) :
    suzukiMangoldtEventWeight r / 2 ≤ suzukiRootKick q r ∧
      suzukiRootKick q r ≤ 3 * suzukiMangoldtEventWeight r / 5 := by
  simpa only [suzukiRootKick] using
    suzukiArchDualRoot_increment_bounds hinterior
      (suzukiMangoldtEventWeight_nonneg r)

theorem suzukiRootKick_bounds_of_block
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtEventWeight r / 2 ≤ suzukiRootKick q r ∧
      suzukiRootKick q r ≤ 3 * suzukiMangoldtEventWeight r / 5 :=
  suzukiRootKick_bounds
    (archDeriv_log_two_lt_suzukiMangoldtSlope_of_event h.left_event)

theorem suzukiRootKick_bounds_vonMangoldt
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    ArithmeticFunction.vonMangoldt r / (2 * Real.sqrt r) ≤
        suzukiRootKick q r ∧
      suzukiRootKick q r ≤
        3 * ArithmeticFunction.vonMangoldt r / (5 * Real.sqrt r) := by
  have hk := suzukiRootKick_bounds_of_block h
  rw [suzukiMangoldtEventWeight] at hk
  constructor
  · calc
      ArithmeticFunction.vonMangoldt r / (2 * Real.sqrt r) =
          (ArithmeticFunction.vonMangoldt r / Real.sqrt r) / 2 := by ring
      _ ≤ suzukiRootKick q r := hk.1
  · calc
      suzukiRootKick q r ≤
          3 * (ArithmeticFunction.vonMangoldt r / Real.sqrt r) / 5 := hk.2
      _ = 3 * ArithmeticFunction.vonMangoldt r / (5 * Real.sqrt r) := by ring

/-- Exact kicked-flow recurrence in the square-root event coordinate. -/
theorem suzukiRootDisplacement_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootDisplacement r = suzukiRootDisplacement q +
      (Real.sqrt r - Real.sqrt q) - suzukiRootKick q r := by
  rw [suzukiRootDisplacement, suzukiRootDisplacement,
    suzukiRootKick, mangoldtSlope_right_event h]
  ring

/-- If the square-root gap dominates the largest possible root kick, the
event displacement cannot decrease. -/
theorem suzukiRootDisplacement_mono_of_gap_ge
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hinterior : deriv suzukiPsiArchimedean (Real.log 2) <
      suzukiMangoldtSlope q)
    (hgap : 3 * suzukiMangoldtEventWeight r / 5 ≤
      Real.sqrt r - Real.sqrt q) :
    suzukiRootDisplacement q ≤ suzukiRootDisplacement r := by
  rw [suzukiRootDisplacement_next h]
  linarith [(suzukiRootKick_bounds (q := q) (r := r) hinterior).2]

theorem suzukiRootDisplacement_mono_of_block_gap_ge
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hgap : 3 * suzukiMangoldtEventWeight r / 5 ≤
      Real.sqrt r - Real.sqrt q) :
    suzukiRootDisplacement q ≤ suzukiRootDisplacement r :=
  suzukiRootDisplacement_mono_of_gap_ge h
    (archDeriv_log_two_lt_suzukiMangoldtSlope_of_event h.left_event) hgap

theorem isActiveMangoldtBlock_iff_root_mem
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsActiveMangoldtBlock q r ↔
      Real.sqrt q < suzukiArchDualRoot (suzukiMangoldtSlope q) ∧
        suzukiArchDualRoot (suzukiMangoldtSlope q) < Real.sqrt r := by
  rw [isActiveMangoldtBlock_iff_optimizer_mem h]
  have hq := exp_half_log_nat_eq_sqrt h.left_pos
  have hr := exp_half_log_nat_eq_sqrt h.right_pos
  unfold suzukiArchDualRoot
  rw [← hq, ← hr]
  constructor
  · intro ht
    exact ⟨Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right (by norm_num)).2 ht.1),
      Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right (by norm_num)).2 ht.2)⟩
  · intro ht
    exact ⟨(div_lt_div_iff_of_pos_right (by norm_num)).1 (Real.exp_lt_exp.mp ht.1),
      (div_lt_div_iff_of_pos_right (by norm_num)).1 (Real.exp_lt_exp.mp ht.2)⟩

theorem isActiveMangoldtBlock_iff_rootDisplacement_crossing
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsActiveMangoldtBlock q r ↔
      suzukiRootDisplacement q < 0 ∧
        0 < suzukiRootDisplacement q + (Real.sqrt r - Real.sqrt q) := by
  rw [isActiveMangoldtBlock_iff_root_mem h]
  unfold suzukiRootDisplacement
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

/-! ## Event-margin area in root coordinates -/

theorem log_suzukiArchDualRoot (S : ℝ) :
    Real.log (suzukiArchDualRoot S) = suzukiArchDualOptimizer S / 2 := by
  unfold suzukiArchDualRoot
  rw [Real.log_exp]

/-- Block form of the signed-area update, before changing from optimizer
location to its root coordinate. -/
theorem globalDualMargin_block_update_integral
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q =
      ∫ s in suzukiMangoldtSlope q..
          suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
        (Real.log r - suzukiArchDualOptimizer s) := by
  have hlambda : 0 ≤ suzukiMangoldtEventWeight r :=
    suzukiMangoldtEventWeight_nonneg r
  have hintOpt : IntervalIntegrable suzukiArchDualOptimizer MeasureTheory.volume
      (suzukiMangoldtSlope q)
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) :=
    continuous_suzukiArchDualOptimizer.intervalIntegrable _ _
  have hintConst : IntervalIntegrable (fun _s : ℝ => Real.log r)
      MeasureTheory.volume (suzukiMangoldtSlope q)
      (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r) :=
    continuous_const.intervalIntegrable _ _
  rw [globalDualMargin_block_update_kickArea h]
  rw [intervalIntegral.integral_sub hintConst hintOpt]
  simp only [intervalIntegral.integral_const, add_sub_cancel_left,
    smul_eq_mul, one_mul]
  unfold suzukiOptimizerKickArea suzukiEventOptimizerDisplacement
    suzukiMangoldtLogGap
  rw [intervalIntegral.integral_sub hintOpt
    (continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, add_sub_cancel_left,
    smul_eq_mul, one_mul]
  ring

/-- Exact margin update in the natural root coordinate.  Its sign is the
signed area of `log (sqrt r / uStar)` over the slope impulse. -/
theorem globalMargin_event_update_root
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q =
      2 * ∫ s in suzukiMangoldtSlope q..
          suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
        Real.log (Real.sqrt r / suzukiArchDualRoot s) := by
  rw [globalDualMargin_block_update_integral h]
  have hsqrtpos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast h.right_pos)
  have hpoint : ∀ s : ℝ,
      Real.log (r : ℝ) - suzukiArchDualOptimizer s =
        2 * Real.log (Real.sqrt r / suzukiArchDualRoot s) := by
    intro s
    rw [Real.log_div hsqrtpos.ne' (suzukiArchDualRoot_pos s).ne',
      Real.log_sqrt (by exact_mod_cast h.right_pos.le), log_suzukiArchDualRoot]
    ring
  calc
    (∫ s in suzukiMangoldtSlope q..
        suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
      (Real.log r - suzukiArchDualOptimizer s)) =
        ∫ s in suzukiMangoldtSlope q..
          suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
        2 * Real.log (Real.sqrt r / suzukiArchDualRoot s) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact hpoint s
    _ = 2 * ∫ s in suzukiMangoldtSlope q..
          suzukiMangoldtSlope q + suzukiMangoldtEventWeight r,
        Real.log (Real.sqrt r / suzukiArchDualRoot s) := by
          rw [intervalIntegral.integral_const_mul]

/-- Root-space version of the already checked margin localization: if the
post-event optimizer is no farther right than the event, the global margin
cannot decrease. -/
theorem globalMargin_nondec_of_root_after_le_event
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hroot : suzukiArchDualRoot (suzukiMangoldtSlope r) ≤ Real.sqrt r) :
    suzukiGlobalDualMargin q ≤ suzukiGlobalDualMargin r := by
  have hsqrt := exp_half_log_nat_eq_sqrt h.right_pos
  have ht : suzukiArchDualOptimizer (suzukiMangoldtSlope r) ≤ Real.log r := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).1
    apply Real.exp_le_exp.mp
    simpa only [suzukiArchDualRoot, hsqrt] using hroot
  apply globalMargin_nondec_of_postEventOptimizer_left h
  unfold suzukiEventOptimizerDisplacement
  linarith

/-- Full change of variables from slope to root coordinate.  The interior
hypothesis is explicit: proving it for every actual Mangoldt state is a
separate finite-base arithmetic certificate. -/
theorem globalMargin_event_update_root_integral
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hinterior : deriv suzukiPsiArchimedean (Real.log 2) <
      suzukiMangoldtSlope q) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q =
      4 * ∫ u in suzukiArchDualRoot (suzukiMangoldtSlope q)..
          suzukiArchDualRoot (suzukiMangoldtSlope r),
        suzukiCurvatureFactor u *
          Real.log (Real.sqrt r / u) := by
  let S := suzukiMangoldtSlope q
  let lambda := suzukiMangoldtEventWeight r
  let R := Real.sqrt (r : ℝ)
  let f' : ℝ → ℝ := fun s =>
    1 / (2 * suzukiCurvatureFactor (suzukiArchDualRoot s))
  let g : ℝ → ℝ := fun u =>
    4 * suzukiCurvatureFactor u * Real.log (R / u)
  have hlambda : 0 ≤ lambda := suzukiMangoldtEventWeight_nonneg r
  have hSle : S ≤ S + lambda := le_add_of_nonneg_right hlambda
  have hderiv : ∀ s ∈ Set.uIcc S (S + lambda),
      HasDerivAt suzukiArchDualRoot (f' s) s := by
    intro s hs
    rw [Set.uIcc_of_le hSle] at hs
    exact hasDerivAt_suzukiArchDualRoot (hinterior.trans_le hs.1)
  have hf' : ContinuousOn f' (Set.uIcc S (S + lambda)) := by
    intro s _
    have hF := (continuousAt_suzukiCurvatureFactor
      (sqrt_two_le_suzukiArchDualRoot s)).comp
        continuous_suzukiArchDualRoot.continuousAt
    have hFne := (suzukiCurvatureFactor_pos
      (sqrt_two_le_suzukiArchDualRoot s)).ne'
    exact (continuousAt_const.div (continuousAt_const.mul hF)
      (mul_ne_zero (by norm_num) hFne)).continuousWithinAt
  have hg : ContinuousOn g
      (suzukiArchDualRoot '' Set.uIcc S (S + lambda)) := by
    rintro u ⟨s, _, rfl⟩
    have hu := sqrt_two_le_suzukiArchDualRoot s
    have hupos := suzukiArchDualRoot_pos s
    have hRpos : 0 < R := Real.sqrt_pos.2 (by
      exact_mod_cast h.right_pos)
    have hF := continuousAt_suzukiCurvatureFactor hu
    have hquot : ContinuousAt (fun u : ℝ => R / u) (suzukiArchDualRoot s) :=
      continuousAt_const.div continuousAt_id hupos.ne'
    have hlog := (Real.continuousAt_log
      (div_ne_zero hRpos.ne' hupos.ne')).comp hquot
    exact ((continuousAt_const.mul hF).mul hlog).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := S) (b := S + lambda) hderiv hf' hg
  have hleft : (∫ s in S..S + lambda,
      (g ∘ suzukiArchDualRoot) s * f' s) =
      2 * ∫ s in S..S + lambda,
        Real.log (R / suzukiArchDualRoot s) := by
    calc
      _ = ∫ s in S..S + lambda,
          2 * Real.log (R / suzukiArchDualRoot s) := by
            apply intervalIntegral.integral_congr
            intro s _
            have hFpos := suzukiCurvatureFactor_pos
              (sqrt_two_le_suzukiArchDualRoot s)
            dsimp [g, f']
            field_simp
            ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [globalMargin_event_update_root h]
  change 2 * (∫ s in S..S + lambda,
      Real.log (R / suzukiArchDualRoot s)) = _
  rw [← hleft, hsub]
  rw [mangoldtSlope_right_event h]
  dsimp [g, R, S, lambda]
  calc
    (∫ u in suzukiArchDualRoot (suzukiMangoldtSlope q)..
        suzukiArchDualRoot
          (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r),
      4 * suzukiCurvatureFactor u * Real.log (Real.sqrt r / u)) =
        ∫ u in suzukiArchDualRoot (suzukiMangoldtSlope q)..
          suzukiArchDualRoot
            (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r),
          4 * (suzukiCurvatureFactor u * Real.log (Real.sqrt r / u)) := by
            apply intervalIntegral.integral_congr
            intro u _
            ring
    _ = 4 * ∫ u in suzukiArchDualRoot (suzukiMangoldtSlope q)..
          suzukiArchDualRoot
            (suzukiMangoldtSlope q + suzukiMangoldtEventWeight r),
        suzukiCurvatureFactor u * Real.log (Real.sqrt r / u) := by
          exact intervalIntegral.integral_const_mul
            (r := (4 : ℝ))
            (f := fun u : ℝ => suzukiCurvatureFactor u *
              Real.log (Real.sqrt r / u))

theorem globalMargin_event_update_root_integral_of_block
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q =
      4 * ∫ u in suzukiArchDualRoot (suzukiMangoldtSlope q)..
          suzukiArchDualRoot (suzukiMangoldtSlope r),
        suzukiCurvatureFactor u * Real.log (Real.sqrt r / u) :=
  globalMargin_event_update_root_integral h
    (archDeriv_log_two_lt_suzukiMangoldtSlope_of_event h.left_event)

/-- Pointwise loss bound for the negative part of the root-area integrand.
It is zero before the optimizer overshoots the event root and at most linear
in the overshoot afterward. -/
theorem rootMarginIntegrand_ge_neg_linear
    {r : ℕ} (hr : 0 < r) {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    -4 * max (u - Real.sqrt r) 0 / Real.sqrt r ≤
      4 * suzukiCurvatureFactor u * Real.log (Real.sqrt r / u) := by
  have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le hu
  have hR0 : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hF0 : 0 < suzukiCurvatureFactor u := suzukiCurvatureFactor_pos hu
  have hF1 : suzukiCurvatureFactor u ≤ 1 :=
    (suzukiCurvatureFactor_lt_one hu).le
  rcases le_total u (Real.sqrt r) with hur | hru
  · rw [max_eq_right (by linarith)]
    simp only [mul_zero, neg_zero, zero_div]
    have hratio : 1 ≤ Real.sqrt r / u :=
      (le_div_iff₀ hu0).2 (by simpa using hur)
    have hlog : 0 ≤ Real.log (Real.sqrt r / u) := Real.log_nonneg hratio
    positivity
  · rw [max_eq_left (sub_nonneg.mpr hru)]
    have hratio0 : 0 < u / Real.sqrt r := div_pos hu0 hR0
    have hlogle := Real.log_le_sub_one_of_pos hratio0
    have hloginv : Real.log (Real.sqrt r / u) =
        -Real.log (u / Real.sqrt r) := by
      rw [Real.log_div hR0.ne' hu0.ne', Real.log_div hu0.ne' hR0.ne']
      ring
    have hfrac : u / Real.sqrt r - 1 =
        (u - Real.sqrt r) / Real.sqrt r := by
      field_simp
    have hlinear : -(u - Real.sqrt r) / Real.sqrt r ≤
        Real.log (Real.sqrt r / u) := by
      rw [hloginv]
      have hneg := neg_le_neg hlogle
      rw [hfrac] at hneg
      simpa only [neg_div] using hneg
    have hratiole : Real.sqrt r / u ≤ 1 :=
      (div_le_one hu0).2 (by simpa using hru)
    have hlognonpos : Real.log (Real.sqrt r / u) ≤ 0 :=
      Real.log_nonpos (div_nonneg hR0.le hu0.le) hratiole
    have hscaled : Real.log (Real.sqrt r / u) ≤
        suzukiCurvatureFactor u * Real.log (Real.sqrt r / u) := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hF1) hlognonpos]
    have hfour := mul_le_mul_of_nonneg_left (hlinear.trans hscaled)
      (by norm_num : (0 : ℝ) ≤ 4)
    calc
      -4 * (u - Real.sqrt r) / Real.sqrt r =
          4 * (-(u - Real.sqrt r) / Real.sqrt r) := by ring
      _ ≤ 4 * (suzukiCurvatureFactor u *
          Real.log (Real.sqrt r / u)) := hfour
      _ = 4 * suzukiCurvatureFactor u *
          Real.log (Real.sqrt r / u) := by ring

/-! ## Dimensionless root state -/

/-- Optimizer root normalized by the square-root event scale. -/
noncomputable def suzukiRootRatio (q : ℕ) : ℝ :=
  suzukiArchDualRoot (suzukiMangoldtSlope q) / Real.sqrt q

/-- Positive part of the amount by which the optimizer root lies beyond the
current event scale. -/
noncomputable def suzukiRootOvershoot (q : ℕ) : ℝ :=
  max (suzukiArchDualRoot (suzukiMangoldtSlope q) - Real.sqrt q) 0

/-- Exact normalized recurrence.  The root impulse is divided by the new
event scale, so its natural size is much smaller than the raw slope impulse. -/
theorem suzukiRootRatio_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootRatio r =
      Real.sqrt q / Real.sqrt r * suzukiRootRatio q +
        suzukiRootKick q r / Real.sqrt r := by
  have hq : Real.sqrt (q : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)).ne'
  have hr : Real.sqrt (r : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast h.right_pos)).ne'
  rw [suzukiRootRatio, suzukiRootRatio, suzukiRootKick_eq_state_sub h]
  field_simp
  ring

theorem suzukiRootRatio_next_upper
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hinterior : deriv suzukiPsiArchimedean (Real.log 2) <
      suzukiMangoldtSlope q) :
    suzukiRootRatio r ≤
      Real.sqrt q / Real.sqrt r * suzukiRootRatio q +
        (3 * suzukiMangoldtEventWeight r / 5) / Real.sqrt r := by
  rw [suzukiRootRatio_next h]
  have hr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast h.right_pos)
  have hk := div_le_div_of_nonneg_right
    (suzukiRootKick_bounds (q := q) (r := r) hinterior).2 hr.le
  linarith

theorem suzukiRootRatio_next_upper_of_block
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootRatio r ≤
      Real.sqrt q / Real.sqrt r * suzukiRootRatio q +
        (3 * suzukiMangoldtEventWeight r / 5) / Real.sqrt r :=
  suzukiRootRatio_next_upper h
    (archDeriv_log_two_lt_suzukiMangoldtSlope_of_event h.left_event)

theorem suzukiRootOvershoot_eq_negativePartDisplacement (q : ℕ) :
    suzukiRootOvershoot q = max (-suzukiRootDisplacement q) 0 := by
  unfold suzukiRootOvershoot suzukiRootDisplacement
  congr 1
  ring

end RHGarden
