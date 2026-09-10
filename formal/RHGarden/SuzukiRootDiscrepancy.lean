import RHGarden.SuzukiRootDynamics

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

namespace RHGarden

/-! ## Smooth and arithmetic slopes in the square-root coordinate -/

/-- The smooth archimedean slope after the change of variables `t = 2 log u`. -/
noncomputable def suzukiRootArchSlope (u : ℝ) : ℝ :=
  deriv suzukiPsiArchimedean (2 * Real.log u)

/-- The arithmetic slope is a right-continuous step function in the root coordinate. -/
noncomputable def suzukiRootMangoldtSlope (u : ℝ) : ℝ :=
  suzukiMangoldtSlope ⌊u ^ 2⌋₊

/-- Smooth reference slope minus accumulated Mangoldt slope. -/
noncomputable def suzukiRootSlopeDiscrepancy (u : ℝ) : ℝ :=
  suzukiRootArchSlope u - suzukiRootMangoldtSlope u

/-- Suzuki's function in the natural square-root coordinate. -/
noncomputable def suzukiPsiRoot (u : ℝ) : ℝ :=
  suzukiPsi (2 * Real.log u)

private theorem sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := by positivity

private theorem one_lt_of_sqrt_two_le {u : ℝ} (hu : Real.sqrt 2 ≤ u) : 1 < u := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

private theorem two_mul_log_sqrt_nat {n : ℕ} (hn : 0 < n) :
    2 * Real.log (Real.sqrt n) = Real.log n := by
  rw [Real.log_sqrt (by exact_mod_cast hn.le)]
  ring

/-- In root coordinates the smooth slope flows with speed exactly `2 F(u)`. -/
theorem hasDerivAt_suzukiRootArchSlope
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    HasDerivAt suzukiRootArchSlope (2 * suzukiCurvatureFactor u) u := by
  have hu0 : 0 < u := sqrt_two_pos.trans_le hu
  have hlog : 0 < 2 * Real.log u := by
    have := Real.log_pos (one_lt_of_sqrt_two_le hu)
    linarith
  have hinner : HasDerivAt (fun x : ℝ => 2 * Real.log x) (2 * u⁻¹) u := by
    simpa using (Real.hasDerivAt_log hu0.ne').const_mul 2
  have hcomp := (hasDerivAt_deriv_suzukiPsiArchimedean hlog).comp u hinner
  have hcurv : suzukiPsiCurvature (2 * Real.log u) =
      u * suzukiCurvatureFactor u := by
    rw [← secondDeriv_suzukiPsiArchimedean hlog,
      secondDeriv_arch_eq_u_mul_factor hlog]
    rw [show (2 * Real.log u) / 2 = Real.log u by ring, Real.exp_log hu0]
  rw [hcurv] at hcomp
  have hcoef : u * suzukiCurvatureFactor u * (2 * u⁻¹) =
      2 * suzukiCurvatureFactor u := by
    field_simp [hu0.ne']
  have hcomp' : HasDerivAt
      (deriv suzukiPsiArchimedean ∘ fun x : ℝ => 2 * Real.log x)
      (2 * suzukiCurvatureFactor u) u := hcomp.congr_deriv hcoef
  have heq : suzukiRootArchSlope =ᶠ[nhds u]
      (deriv suzukiPsiArchimedean ∘ fun x : ℝ => 2 * Real.log x) := by
    filter_upwards with x
    rfl
  exact hcomp'.congr_of_eventuallyEq heq

theorem five_thirds_le_deriv_suzukiRootArchSlope
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    (5 / 3 : ℝ) ≤ deriv suzukiRootArchSlope u := by
  rw [(hasDerivAt_suzukiRootArchSlope hu).deriv]
  nlinarith [five_sixths_le_suzukiCurvatureFactor hu]

theorem deriv_suzukiRootArchSlope_lt_two
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    deriv suzukiRootArchSlope u < 2 := by
  rw [(hasDerivAt_suzukiRootArchSlope hu).deriv]
  nlinarith [suzukiCurvatureFactor_lt_one hu]

private theorem floor_sq_mem_block
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    q ≤ ⌊u ^ 2⌋₊ ∧ ⌊u ^ 2⌋₊ < r := by
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg q).trans hqu
  have hqcast : (q : ℝ) ≤ u ^ 2 := by
    have hmul : 0 ≤ (u + Real.sqrt q) * (u - Real.sqrt q) :=
      mul_nonneg (add_nonneg hu0 (Real.sqrt_nonneg q)) (sub_nonneg.mpr hqu)
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg q)]
  have hrcast : u ^ 2 < (r : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r)]
  exact ⟨Nat.le_floor hqcast, (Nat.floor_lt (sq_nonneg u)).2 hrcast⟩

/-- The root arithmetic slope is constant throughout the half-open block. -/
theorem suzukiRootMangoldtSlope_eq_on_block
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiRootMangoldtSlope u = suzukiMangoldtSlope q := by
  unfold suzukiRootMangoldtSlope
  exact mangoldtSlope_eq_on_block h
    (floor_sq_mem_block h hqu hur).1 (floor_sq_mem_block h hqu hur).2

theorem suzukiRootMangoldtSlope_sqrt_event
    {q : ℕ} (hq : IsMangoldtEvent q) :
    suzukiRootMangoldtSlope (Real.sqrt q) = suzukiMangoldtSlope q := by
  unfold suzukiRootMangoldtSlope
  rw [Real.sq_sqrt (Nat.cast_nonneg q), Nat.floor_natCast]

/-- The discrepancy is the smooth block slope minus its frozen arithmetic state. -/
theorem suzukiRootSlopeDiscrepancy_eq_on_block
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiRootSlopeDiscrepancy u =
      suzukiRootArchSlope u - suzukiMangoldtSlope q := by
  rw [suzukiRootSlopeDiscrepancy, suzukiRootMangoldtSlope_eq_on_block h hqu hur]

/-- At an event, right continuity makes the root discrepancy exactly the post-kick deficit. -/
theorem suzukiRootSlopeDiscrepancy_sqrt_event
    {q : ℕ} (hq : IsMangoldtEvent q) :
    suzukiRootSlopeDiscrepancy (Real.sqrt q) = suzukiEventSlopeDeficit q := by
  rw [suzukiRootSlopeDiscrepancy, suzukiRootArchSlope,
    suzukiRootMangoldtSlope_sqrt_event hq, suzukiEventSlopeDeficit,
    two_mul_log_sqrt_nat (lt_of_lt_of_le (by norm_num) hq.two_le)]

/-! ## Sawtooth flow and jumps -/

/-- Away from event boundaries the discrepancy recovers at speed `2 F(u)`. -/
theorem rootSlopeDiscrepancy_hasDerivAt
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q < u) (hur : u < Real.sqrt r) :
    HasDerivAt suzukiRootSlopeDiscrepancy
      (2 * suzukiCurvatureFactor u) u := by
  have hsqrt2q : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)
  have harch := hasDerivAt_suzukiRootArchSlope (hsqrt2q.trans hqu.le)
  have heq : suzukiRootSlopeDiscrepancy =ᶠ[nhds u]
      fun v => suzukiRootArchSlope v - suzukiMangoldtSlope q := by
    filter_upwards [eventually_gt_nhds hqu, eventually_lt_nhds hur] with v hvq hvr
    exact suzukiRootSlopeDiscrepancy_eq_on_block h hvq.le hvr
  exact (harch.sub_const (suzukiMangoldtSlope q)).congr_of_eventuallyEq heq

theorem rootSlopeDiscrepancy_deriv_bounds
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q < u) (hur : u < Real.sqrt r) :
    (5 / 3 : ℝ) ≤ deriv suzukiRootSlopeDiscrepancy u ∧
      deriv suzukiRootSlopeDiscrepancy u < 2 := by
  rw [(rootSlopeDiscrepancy_hasDerivAt h hqu hur).deriv]
  have hsqrt2q : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)
  constructor
  · nlinarith [five_sixths_le_suzukiCurvatureFactor
      (hsqrt2q.trans hqu.le)]
  · nlinarith [suzukiCurvatureFactor_lt_one (hsqrt2q.trans hqu.le)]

/-- The event impulse subtracts exactly its Mangoldt weight from the pre-event discrepancy. -/
theorem rootSlopeDiscrepancy_event_jump
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootSlopeDiscrepancy (Real.sqrt r) =
      (suzukiRootArchSlope (Real.sqrt r) - suzukiMangoldtSlope q) -
        suzukiMangoldtEventWeight r := by
  rw [suzukiRootSlopeDiscrepancy_sqrt_event h.right_event,
    suzukiEventSlopeDeficit, suzukiRootArchSlope,
    two_mul_log_sqrt_nat h.right_pos, mangoldtSlope_right_event h]
  ring

/-! ## Suzuki Psi as weighted discrepancy area -/

private theorem hasDerivAt_rootBlockProfile
    {q : ℕ} {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    HasDerivAt (fun v => suzukiMangoldtBlockProfile q (2 * Real.log v))
      (2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q)) u := by
  have hu0 : 0 < u := sqrt_two_pos.trans_le hu
  have hlog : 0 < 2 * Real.log u := by
    linarith [Real.log_pos (one_lt_of_sqrt_two_le hu)]
  have hinner : HasDerivAt (fun x : ℝ => 2 * Real.log x) (2 * u⁻¹) u := by
    simpa using (Real.hasDerivAt_log hu0.ne').const_mul 2
  have hcomp := (hasDerivAt_suzukiMangoldtBlockProfile q hlog).comp u hinner
  have hcoef :
      (deriv suzukiPsiArchimedean (2 * Real.log u) - suzukiMangoldtSlope q) *
          (2 * u⁻¹) =
        2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q) := by
    rw [suzukiRootArchSlope]
    field_simp [hu0.ne']
    <;> ring
  have hcomp' : HasDerivAt
      (suzukiMangoldtBlockProfile q ∘ fun x : ℝ => 2 * Real.log x)
      (2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q)) u :=
    hcomp.congr_deriv hcoef
  have heq : (fun v : ℝ => suzukiMangoldtBlockProfile q (2 * Real.log v)) =ᶠ[nhds u]
      (suzukiMangoldtBlockProfile q ∘ fun x : ℝ => 2 * Real.log x) := by
    filter_upwards with x
    rfl
  exact hcomp'.congr_of_eventuallyEq heq

/-- On the interior of a block, `H'(u)=2D(u)/u`. -/
theorem hasDerivAt_suzukiPsiRoot
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q < u) (hur : u < Real.sqrt r) :
    HasDerivAt suzukiPsiRoot
      (2 / u * suzukiRootSlopeDiscrepancy u) u := by
  have hu0 : 0 < u := (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)).trans hqu
  have hsqrt2q : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)
  have hp := hasDerivAt_rootBlockProfile (q := q) (hsqrt2q.trans hqu.le)
  have heq : suzukiPsiRoot =ᶠ[nhds u]
      fun v => suzukiMangoldtBlockProfile q (2 * Real.log v) := by
    filter_upwards [eventually_gt_nhds hqu, eventually_lt_nhds hur] with v hvq hvr
    have hv0 : 0 < v := (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)).trans hvq
    have htq : Real.log q ≤ 2 * Real.log v := by
      rw [← two_mul_log_sqrt_nat h.left_pos]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (Real.sqrt_pos.2
        (by exact_mod_cast h.left_pos)) hvq.le) (by norm_num)
    have htr : 2 * Real.log v ≤ Real.log r := by
      rw [← two_mul_log_sqrt_nat h.right_pos]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hv0 hvr.le) (by norm_num)
    unfold suzukiPsiRoot suzukiMangoldtBlockProfile
    exact suzukiPsi_eq_mangoldtBlock h htq htr
  rw [suzukiRootSlopeDiscrepancy_eq_on_block h hqu.le hur]
  exact hp.congr_of_eventuallyEq heq

theorem deriv_suzukiPsiRoot
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q < u) (hur : u < Real.sqrt r) :
    deriv suzukiPsiRoot u = 2 / u * suzukiRootSlopeDiscrepancy u :=
  (hasDerivAt_suzukiPsiRoot h hqu hur).deriv

/-- Exact weighted discrepancy area between arbitrary points of one complete block. -/
theorem suzukiPsiRoot_sub_eq_integral_discrepancy_on_block
    {q r : ℕ} (h : IsMangoldtBlock q r) {a b : ℝ}
    (hqa : Real.sqrt q ≤ a) (hab : a ≤ b) (hbr : b ≤ Real.sqrt r) :
    suzukiPsiRoot b - suzukiPsiRoot a =
      ∫ u in a..b, 2 / u * suzukiRootSlopeDiscrepancy u := by
  have hq0 : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)
  have ha0 : 0 < a := hq0.trans_le hqa
  have hsqrt2q : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)
  let profile : ℝ → ℝ := fun u => suzukiMangoldtBlockProfile q (2 * Real.log u)
  have hcont : ContinuousOn profile (Icc a b) := by
    intro u hu
    exact (hasDerivAt_rootBlockProfile (q := q)
      (hsqrt2q.trans (hqa.trans hu.1))).continuousAt.continuousWithinAt
  have hderiv : ∀ u ∈ Ioo a b, HasDerivAt profile
      (2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q)) u := by
    intro u hu
    exact hasDerivAt_rootBlockProfile (q := q)
      (hsqrt2q.trans (hqa.trans hu.1.le))
  have hint : IntervalIntegrable
      (fun u => 2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q))
      volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    have hu0 := ha0.trans_le hu.1
    exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
      ((hasDerivAt_suzukiRootArchSlope
        ((Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)).trans
          (hqa.trans hu.1))).continuousAt.sub continuousAt_const)).continuousWithinAt
  have hFTC : (∫ u in a..b,
      2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q)) =
      profile b - profile a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  have hroot : suzukiPsiRoot b - suzukiPsiRoot a = profile b - profile a := by
    have endpoint (u : ℝ) (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
        suzukiPsiRoot u = profile u := by
      have hu0 := hq0.trans_le hqu
      have htq : Real.log q ≤ 2 * Real.log u := by
        rw [← two_mul_log_sqrt_nat h.left_pos]
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hq0 hqu) (by norm_num)
      have htr : 2 * Real.log u ≤ Real.log r := by
        rw [← two_mul_log_sqrt_nat h.right_pos]
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hu0 hur) (by norm_num)
      exact suzukiPsi_eq_mangoldtBlock h htq htr
    rw [endpoint b (hqa.trans hab) hbr, endpoint a hqa (hab.trans hbr)]
  rw [hroot, ← hFTC]
  apply intervalIntegral.integral_congr_uIoo
  intro u hu
  rw [uIoo_of_le hab] at hu
  change 2 / u * (suzukiRootArchSlope u - suzukiMangoldtSlope q) =
    2 / u * suzukiRootSlopeDiscrepancy u
  rw [suzukiRootSlopeDiscrepancy_eq_on_block h
    (hqa.trans hu.1.le) (hu.2.trans_le hbr)]

/-- Event values differ by the exact weighted discrepancy area across the block. -/
theorem suzukiEventValue_sub_eq_rootDiscrepancyArea
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventValue r - suzukiEventValue q =
      ∫ u in Real.sqrt q..Real.sqrt r,
        2 / u * suzukiRootSlopeDiscrepancy u := by
  simpa [suzukiPsiRoot, suzukiEventValue,
    two_mul_log_sqrt_nat h.left_pos, two_mul_log_sqrt_nat h.right_pos] using
    suzukiPsiRoot_sub_eq_integral_discrepancy_on_block h
      (a := Real.sqrt q) (b := Real.sqrt r) le_rfl
      (Real.sqrt_le_sqrt (by exact_mod_cast h.left_lt.le)) le_rfl

/-- The root-coordinate prefix-area condition, anchored at each complete
Mangoldt block's left event.  The blockwise formulation avoids any choice of
an enumeration of all prime-power events. -/
def RootDiscrepancyPrefixNonnegative : Prop :=
  ∀ q r : ℕ, IsMangoldtBlock q r → ∀ u : ℝ,
    Real.sqrt q ≤ u → u ≤ Real.sqrt r →
      0 ≤ suzukiEventValue q +
        ∫ x in Real.sqrt q..u, 2 / x * suzukiRootSlopeDiscrepancy x

theorem suzukiEventValue_add_rootDiscrepancyArea
    {q r : ℕ} (h : IsMangoldtBlock q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiEventValue q +
        ∫ x in Real.sqrt q..u, 2 / x * suzukiRootSlopeDiscrepancy x =
      suzukiPsiRoot u := by
  have harea := suzukiPsiRoot_sub_eq_integral_discrepancy_on_block h
    (a := Real.sqrt q) (b := u) le_rfl hqu hur
  have hleft : suzukiPsiRoot (Real.sqrt q) = suzukiEventValue q := by
    simp only [suzukiPsiRoot, suzukiEventValue,
      two_mul_log_sqrt_nat h.left_pos]
  linarith

private theorem sqrt_nat_le_exp_half_of_log_le
    {n : ℕ} (hn : 0 < n) {t : ℝ} (h : Real.log n ≤ t) :
    Real.sqrt n ≤ Real.exp (t / 2) := by
  rw [← Real.exp_log (Real.sqrt_pos.2 (by exact_mod_cast hn)),
    Real.log_sqrt (Nat.cast_nonneg n)]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem exp_half_le_sqrt_nat_of_le_log
    {n : ℕ} (hn : 0 < n) {t : ℝ} (h : t ≤ Real.log n) :
    Real.exp (t / 2) ≤ Real.sqrt n := by
  rw [← Real.exp_log (Real.sqrt_pos.2 (by exact_mod_cast hn)),
    Real.log_sqrt (Nat.cast_nonneg n)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- One exact scalar block margin is nonnegative exactly when every weighted
root-area prefix in that block preserves nonnegative reserve. -/
theorem mangoldtBlockMargin_nonneg_iff_rootDiscrepancyPrefix
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    0 ≤ suzukiMangoldtBlockMargin q r ↔
      ∀ u : ℝ, Real.sqrt q ≤ u → u ≤ Real.sqrt r →
        0 ≤ suzukiEventValue q +
          ∫ x in Real.sqrt q..u, 2 / x * suzukiRootSlopeDiscrepancy x := by
  rw [mangoldtBlockMargin_nonneg_iff h]
  constructor
  · intro hpsi u hqu hur
    rw [suzukiEventValue_add_rootDiscrepancyArea h hqu hur]
    unfold suzukiPsiRoot
    apply hpsi
    · rw [← two_mul_log_sqrt_nat h.left_pos]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)) hqu)
        (by norm_num)
    · rw [← two_mul_log_sqrt_nat h.right_pos]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log
          ((Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)).trans_le hqu) hur)
        (by norm_num)
  · intro hprefix t htq htr
    let u := Real.exp (t / 2)
    have hqu : Real.sqrt q ≤ u :=
      sqrt_nat_le_exp_half_of_log_le h.left_pos htq
    have hur : u ≤ Real.sqrt r :=
      exp_half_le_sqrt_nat_of_le_log h.right_pos htr
    have hp := hprefix u hqu hur
    rw [suzukiEventValue_add_rootDiscrepancyArea h hqu hur] at hp
    simpa only [suzukiPsiRoot, u, Real.log_exp, show 2 * (t / 2) = t by ring] using hp

/-- RH as the initial interval condition plus nonnegative weighted
root-discrepancy prefixes on every complete Mangoldt block.  This is an
equivalence only; it does not assert either open positivity premise. -/
theorem riemannHypothesis_iff_initial_and_rootDiscrepancyPrefixes :
    RiemannHypothesis ↔
      SuzukiInitialNonnegative ∧ RootDiscrepancyPrefixNonnegative := by
  rw [riemannHypothesis_iff_initial_and_all_mangoldtBlockMargins]
  constructor
  · rintro ⟨hinit, hmargins⟩
    refine ⟨hinit, ?_⟩
    intro q r h u hqu hur
    exact (mangoldtBlockMargin_nonneg_iff_rootDiscrepancyPrefix h).mp
      (hmargins q r h) u hqu hur
  · rintro ⟨hinit, hprefix⟩
    refine ⟨hinit, ?_⟩
    intro q r h
    exact (mangoldtBlockMargin_nonneg_iff_rootDiscrepancyPrefix h).mpr
      (hprefix q r h)

/-! ## Backlog, exact excursion loss, and service/arrival recurrence -/

/-- Negative part of the root-slope discrepancy. -/
noncomputable def suzukiRootSlopeBacklog (u : ℝ) : ℝ :=
  max (-suzukiRootSlopeDiscrepancy u) 0

theorem rootSlopeDiscrepancy_neg_iff_backlog_pos (u : ℝ) :
    suzukiRootSlopeDiscrepancy u < 0 ↔ 0 < suzukiRootSlopeBacklog u := by
  unfold suzukiRootSlopeBacklog
  constructor
  · intro h
    rw [max_eq_left (by linarith)]
    linarith
  · intro h
    by_contra hn
    rw [max_eq_right (by linarith)] at h
    exact (lt_irrefl 0) h

/-- A finite root interval on which the slope discrepancy is nonpositive.
This intentionally avoids a maximal-component construction: numerical busy
periods may join several such block pieces across Mangoldt impulses. -/
def IsSuzukiRootNegativeExcursion (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ u ∈ Icc a b, suzukiRootSlopeDiscrepancy u ≤ 0

/-- Reserve consumed between the endpoints of a negative root excursion. -/
noncomputable def suzukiBusyPeriodLoss (a b : ℝ) : ℝ :=
  suzukiPsiRoot a - suzukiPsiRoot b

/-- Exact reserve consumed on a block subinterval where the discrepancy is nonpositive. -/
theorem suzukiPsiRoot_loss_eq_integral_backlog
    {q r : ℕ} (h : IsMangoldtBlock q r) {a b : ℝ}
    (hqa : Real.sqrt q ≤ a) (hab : a ≤ b) (hbr : b ≤ Real.sqrt r)
    (hneg : ∀ u ∈ Icc a b, suzukiRootSlopeDiscrepancy u ≤ 0) :
    suzukiPsiRoot a - suzukiPsiRoot b =
      ∫ u in a..b, 2 / u * suzukiRootSlopeBacklog u := by
  rw [show suzukiPsiRoot a - suzukiPsiRoot b =
      -(suzukiPsiRoot b - suzukiPsiRoot a) by ring,
    suzukiPsiRoot_sub_eq_integral_discrepancy_on_block h hqa hab hbr,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  have hback : suzukiRootSlopeBacklog u = -suzukiRootSlopeDiscrepancy u := by
    rw [suzukiRootSlopeBacklog, max_eq_left]
    linarith [hneg u hu]
  change -(2 / u * suzukiRootSlopeDiscrepancy u) =
    2 / u * suzukiRootSlopeBacklog u
  rw [hback]
  ring

/-- On one block piece, busy-period loss is exactly weighted backlog area. -/
theorem suzukiBusyPeriodLoss_eq_integral_backlog
    {q r : ℕ} (h : IsMangoldtBlock q r) {a b : ℝ}
    (hqa : Real.sqrt q ≤ a) (hbr : b ≤ Real.sqrt r)
    (hexc : IsSuzukiRootNegativeExcursion a b) :
    suzukiBusyPeriodLoss a b =
      ∫ u in a..b, 2 / u * suzukiRootSlopeBacklog u := by
  exact suzukiPsiRoot_loss_eq_integral_backlog h hqa hexc.1 hbr hexc.2

/-- Smooth service supplied between two event roots. -/
noncomputable def suzukiRootSlopeService (q r : ℕ) : ℝ :=
  suzukiRootArchSlope (Real.sqrt r) - suzukiRootArchSlope (Real.sqrt q)

theorem suzukiRootSlopeService_eq_archSlopeDrift
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootSlopeService q r = suzukiArchSlopeDrift q r := by
  simp only [suzukiRootSlopeService, suzukiRootArchSlope, suzukiArchSlopeDrift,
    two_mul_log_sqrt_nat h.left_pos, two_mul_log_sqrt_nat h.right_pos]

theorem suzukiRootSlopeService_eq_integral
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootSlopeService q r =
      ∫ u in Real.sqrt q..Real.sqrt r, 2 * suzukiCurvatureFactor u := by
  have hqr : Real.sqrt (q : ℝ) ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_lt.le)
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hqr
  · intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      ((Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)).trans hu.1)).continuousAt.continuousWithinAt
  · intro u hu
    exact hasDerivAt_suzukiRootArchSlope
      ((Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)).trans hu.1.le)
  · apply ContinuousOn.intervalIntegrable_of_Icc hqr
    intro u hu
    exact (continuousAt_const.mul (continuousAt_suzukiCurvatureFactor
      ((Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)).trans hu.1))).continuousWithinAt

theorem suzukiRootSlopeService_bounds
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    (5 / 3 : ℝ) * (Real.sqrt r - Real.sqrt q) ≤
        suzukiRootSlopeService q r ∧
      suzukiRootSlopeService q r <
        2 * (Real.sqrt r - Real.sqrt q) := by
  have hqr : Real.sqrt (q : ℝ) < Real.sqrt r :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg q) (by exact_mod_cast h.left_lt)
  have hsqrt2q : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_event.two_le)
  have hcont : ContinuousOn suzukiRootArchSlope
      (Icc (Real.sqrt q) (Real.sqrt r)) := by
    intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      (hsqrt2q.trans hu.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ suzukiRootArchSlope
      (Ioo (Real.sqrt q) (Real.sqrt r)) := by
    intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      (hsqrt2q.trans hu.1.le)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope suzukiRootArchSlope hqr hcont hdiff
  have hgap : 0 < Real.sqrt r - Real.sqrt q := sub_pos.mpr hqr
  have hservice : suzukiRootSlopeService q r =
      deriv suzukiRootArchSlope c * (Real.sqrt r - Real.sqrt q) := by
    unfold suzukiRootSlopeService
    exact ((eq_div_iff hgap.ne').mp hslope).symm
  rw [hservice]
  constructor
  · have hc5 := five_thirds_le_deriv_suzukiRootArchSlope
      (hsqrt2q.trans hc.1.le)
    nlinarith
  · have hc2 := deriv_suzukiRootArchSlope_lt_two
      (hsqrt2q.trans hc.1.le)
    nlinarith

/-- Canonical queue recurrence: post-event discrepancy equals prior discrepancy plus service minus arrival. -/
theorem rootSlopeDiscrepancy_event_recurrence
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiRootSlopeDiscrepancy (Real.sqrt r) =
      suzukiRootSlopeDiscrepancy (Real.sqrt q) +
        suzukiRootSlopeService q r - suzukiMangoldtEventWeight r := by
  rw [suzukiRootSlopeDiscrepancy_sqrt_event h.right_event,
    suzukiRootSlopeDiscrepancy_sqrt_event h.left_event,
    suzukiRootSlopeService_eq_archSlopeDrift h]
  exact suzukiEventSlope_next h

/-! ## Arrival mass and Chebyshev partial summation -/

private theorem sum_Icc_eq_sum_Ioc_of_zero
    {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, c k = ∑ k ∈ Finset.Ioc 0 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc, zero_add]

/-- The finite Chebyshev psi sum needed by the root-arrival process.  This
definition deliberately stays within the already imported Suzuki dependency
surface, avoiding an otherwise unrelated rebuild of pinned Mathlib modules. -/
noncomputable def suzukiChebyshevPsi (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k

private theorem suzukiChebyshevPsi_eq_sum_Icc (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k =
      suzukiChebyshevPsi t := by
  rw [sum_Icc_eq_sum_Ioc_of_zero (by simp) ⌊t⌋₊]
  rfl

/-- Exact Abel/partial-summation formula for the cumulative arithmetic
arrival mass.  The pinned Zeta23 Chebyshev module uses the same specialization
privately; this public RH Garden statement is derived from Mathlib's public
`sum_mul_eq_sub_integral_mul₀` API. -/
theorem sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi
    {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n =
      x ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi x +
        2⁻¹ * ∫ t in Set.Ioc 1 x,
          t ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun y : ℝ => y ^ (-(2⁻¹ : ℝ))) t := by
    intro t ht
    exact Real.differentiableAt_rpow_const_of_ne _ (by nlinarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) =
      fun t : ℝ => -(2⁻¹ : ℝ) * t ^ (-(2⁻¹ : ℝ) - 1) :=
    Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(2⁻¹ : ℝ)))
      (Set.Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀
    (fun n => ArithmeticFunction.vonMangoldt n) (by simp) x hf_diff hf_int
  have hleft :
      ∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℝ) ^ (-(2⁻¹ : ℝ)) * ArithmeticFunction.vonMangoldt k =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    rw [sum_Icc_eq_sum_Ioc_of_zero (by simp) ⌊x⌋₊]
    refine Finset.sum_congr rfl fun k _hk => ?_
    have hrw : (k : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]
      norm_num
    rw [hrw, div_eq_mul_inv, mul_comm]
  rw [hleft, suzukiChebyshevPsi_eq_sum_Icc] at habel
  have hintegral :
      (∫ t in Set.Ioc 1 x,
          deriv (fun y : ℝ => y ^ (-(2⁻¹ : ℝ))) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k) =
        -(2⁻¹ : ℝ) * ∫ t in Set.Ioc 1 x,
          t ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hderiv]
    rw [suzukiChebyshevPsi_eq_sum_Icc]
    ring
  rw [habel, hintegral]
  ring

end RHGarden
