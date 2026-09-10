import RHGarden.SuzukiKickedFlow

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace RHGarden

/-! ## Exponential archimedean curvature -/

/-- The closed curvature is an exponential factor times a correction which
is already very close to one at the first Mangoldt event. -/
theorem secondDeriv_arch_eq_exp_mul_factor
    {t : ℝ} (ht : 0 < t) :
    deriv (deriv suzukiPsiArchimedean) t =
      Real.exp (t / 2) *
        (1 - 1 /
          (Real.exp (t / 2) ^ 2 *
            (Real.exp (t / 2) ^ 4 - 1))) := by
  let y := Real.exp (t / 2)
  have hy0 : y ≠ 0 := by dsimp [y]; positivity
  have hygt : 1 < y := by
    dsimp [y]
    rw [← Real.exp_zero, Real.exp_lt_exp]
    linarith
  have hy4gt : 1 < y ^ 4 := by
    have hy2gt : 1 < y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
    nlinarith [sq_nonneg (y ^ 2 - 1), show (y ^ 2) ^ 2 = y ^ 4 by ring]
  have hy4 : y ^ 4 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hy4gt)
  rw [secondDeriv_suzukiPsiArchimedean ht]
  change y + 1 / y - y ^ 3 / (y ^ 4 - 1) =
    y * (1 - 1 / (y ^ 2 * (y ^ 4 - 1)))
  field_simp [hy0, hy4]
  ring

/-- From `t=log 2` onward, the archimedean curvature retains at least
five sixths of its dominant exponential term. -/
theorem five_sixths_exp_le_secondDeriv_arch
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (5 / 6 : ℝ) * Real.exp (t / 2) ≤
      deriv (deriv suzukiPsiArchimedean) t := by
  have htpos : 0 < t :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  let y := Real.exp (t / 2)
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy2exp : y ^ 2 = Real.exp t := by
    dsimp [y]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hy2 : (2 : ℝ) ≤ y ^ 2 := by
    rw [hy2exp, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hy4 : (4 : ℝ) ≤ y ^ 4 := by
    nlinarith [sq_nonneg (y ^ 2 - 2), show (y ^ 2) ^ 2 = y ^ 4 by ring]
  have hden : (6 : ℝ) ≤ y ^ 2 * (y ^ 4 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2) (sub_nonneg.mpr (show 3 ≤ y ^ 4 - 1 by linarith))]
  have hdenpos : 0 < y ^ 2 * (y ^ 4 - 1) := lt_of_lt_of_le (by norm_num) hden
  have hinv : 1 / (y ^ 2 * (y ^ 4 - 1)) ≤ (1 / 6 : ℝ) := by
    exact (one_div_le_one_div_of_le (by norm_num) hden)
  rw [secondDeriv_arch_eq_exp_mul_factor htpos]
  change (5 / 6 : ℝ) * y ≤ y * (1 - 1 / (y ^ 2 * (y ^ 4 - 1)))
  nlinarith

/-! ## Curvature-weighted block safety -/

/-- A simple uniform curvature lower bound for the block starting at `q`. -/
noncomputable def suzukiMangoldtBlockCurvatureLower (q : ℕ) : ℝ :=
  (5 / 6 : ℝ) * Real.sqrt q

theorem suzukiMangoldtBlockCurvatureLower_pos
    {q : ℕ} (hq : 2 ≤ q) :
    0 < suzukiMangoldtBlockCurvatureLower q := by
  unfold suzukiMangoldtBlockCurvatureLower
  positivity

private theorem sqrt_nat_le_exp_half_of_log_nat_le
    {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : Real.log q ≤ t) :
    Real.sqrt q ≤ Real.exp (t / 2) := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hexp0 : 0 ≤ Real.exp (t / 2) := (Real.exp_pos _).le
  have hsqrt2 : (Real.sqrt q) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hexp2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hqexp : (q : ℝ) ≤ Real.exp t := by
    have hqreal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    calc
      (q : ℝ) = Real.exp (Real.log (q : ℝ)) := (Real.exp_log hqreal).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  nlinarith

/-- On the interior of a complete block the actual Suzuki function has the
same exponentially large curvature as its archimedean profile. -/
theorem blockCurvatureLower
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (ht : t ∈ Ioo (Real.log q) (Real.log r)) :
    suzukiMangoldtBlockCurvatureLower q ≤
      deriv (deriv suzukiPsi) t := by
  have htpos : 0 < t :=
    (Real.log_pos (by exact_mod_cast h.left_event.two_le)).trans ht.1
  have heq : deriv suzukiPsi =ᶠ[nhds t]
      (fun x => deriv suzukiPsiArchimedean x - suzukiMangoldtSlope q) := by
    filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with x hxq hxr
    exact deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_mangoldtBlock h ⟨hxq, hxr⟩
  have hderiv : deriv (deriv suzukiPsi) t =
      deriv (deriv suzukiPsiArchimedean) t := by
    rw [heq.deriv_eq]
    calc
      deriv (fun x => deriv suzukiPsiArchimedean x - suzukiMangoldtSlope q) t =
          suzukiPsiCurvature t :=
        ((hasDerivAt_deriv_suzukiPsiArchimedean htpos).sub_const
          (suzukiMangoldtSlope q)).deriv
      _ = deriv (deriv suzukiPsiArchimedean) t :=
        (secondDeriv_suzukiPsiArchimedean htpos).symm
  rw [hderiv]
  have hfive := five_sixths_exp_le_secondDeriv_arch
    ((Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)).trans
      ht.1.le)
  have hsqrt := sqrt_nat_le_exp_half_of_log_nat_le h.left_pos ht.1.le
  unfold suzukiMangoldtBlockCurvatureLower
  nlinarith

private theorem arch_tangent_lower_of_secondDeriv_ge
    {x y m : ℝ} (hx : Real.log 2 ≤ x) (hxy : x ≤ y) (hm : 0 < m)
    (hsecond : ∀ z ∈ Ioo x y,
      m ≤ deriv (deriv suzukiPsiArchimedean) z) :
    suzukiPsiArchimedean x +
        deriv suzukiPsiArchimedean x * (y - x) +
        m * (y - x) ^ 2 / 2 ≤ suzukiPsiArchimedean y := by
  let g : ℝ → ℝ := fun z => suzukiPsiArchimedean z - m / 2 * z ^ 2
  let g' : ℝ → ℝ := fun z => deriv suzukiPsiArchimedean z - m * z
  let g'' : ℝ → ℝ := fun z => deriv (deriv suzukiPsiArchimedean) z - m
  have hxpos : 0 < x :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hx
  have hfdiff : DifferentiableOn ℝ suzukiPsiArchimedean (Ioo x y) := by
    intro z hz
    exact (differentiableAt_suzukiPsiArchimedean_of_pos
      (hxpos.trans hz.1)).differentiableWithinAt
  have hf2diff : DifferentiableOn ℝ (deriv suzukiPsiArchimedean) (Ioo x y) := by
    intro z hz
    exact (hasDerivAt_deriv_suzukiPsiArchimedean
      (hxpos.trans hz.1)).differentiableAt.differentiableWithinAt
  have hfirst : ∀ z ∈ Ioo x y, HasDerivAt g (g' z) z := by
    intro z hz
    have hz' : DifferentiableAt ℝ suzukiPsiArchimedean z :=
      (hfdiff z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
    have hsq := ((hasDerivAt_id z).pow 2).const_mul (m / 2)
    have hraw := hz'.hasDerivAt.sub hsq
    apply hraw.congr_deriv
    dsimp [g']
    ring
  have hsecond' : ∀ z ∈ Ioo x y, HasDerivAt g' (g'' z) z := by
    intro z hz
    have hz' : DifferentiableAt ℝ (deriv suzukiPsiArchimedean) z :=
      (hf2diff z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
    have hraw := hz'.hasDerivAt.sub ((hasDerivAt_id z).const_mul m)
    apply hraw.congr_deriv
    dsimp [g'']
    ring
  have hgcont : ContinuousOn g (Icc x y) := by
    intro z hz
    dsimp [g]
    exact ((differentiableAt_suzukiPsiArchimedean_of_pos
      (hxpos.trans_le hz.1)).continuousAt.sub
        (((continuousAt_id.pow 2).const_mul (m / 2)))).continuousWithinAt
  have hgconv : ConvexOn ℝ (Icc x y) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hgcont
    · intro z hz
      rw [interior_Icc] at hz
      exact (hfirst z hz).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hsecond' z hz).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      dsimp [g'']
      exact sub_nonneg.mpr (hsecond z hz)
  have hg'x : HasDerivAt g (g' x) x := by
    have hsq := ((hasDerivAt_id x).pow 2).const_mul (m / 2)
    have hraw :=
      (differentiableAt_suzukiPsiArchimedean_of_pos hxpos).hasDerivAt.sub hsq
    apply hraw.congr_deriv
    dsimp [g']
    ring
  rcases hxy.eq_or_lt with rfl | hxy'
  · simp
  · have hs := hgconv.le_slope_of_hasDerivAt
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy' hg'x
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hxy')).mp hs
    dsimp [g, g'] at hmul
    nlinarith

/-- Exponentially weighted strong convexity gives the blockwise quadratic
envelope based at its left event. -/
theorem curvatureWeighted_quadratic_envelope
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (htq : Real.log q ≤ t) (htr : t ≤ Real.log r) :
    suzukiEventValue q + suzukiEventSlopeDeficit q * (t - Real.log q) +
        suzukiMangoldtBlockCurvatureLower q * (t - Real.log q) ^ 2 / 2 ≤
      suzukiPsi t := by
  have hqlog2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)
  have hmpos := suzukiMangoldtBlockCurvatureLower_pos h.left_event.two_le
  have harch := arch_tangent_lower_of_secondDeriv_ge hqlog2 htq hmpos (by
    intro z hz
    have hfive := five_sixths_exp_le_secondDeriv_arch (hqlog2.trans hz.1.le)
    have hsqrt := sqrt_nat_le_exp_half_of_log_nat_le h.left_pos hz.1.le
    unfold suzukiMangoldtBlockCurvatureLower
    nlinarith)
  unfold suzukiEventValue suzukiEventSlopeDeficit
  rw [suzukiPsi_eq_mangoldtBlock h htq htr,
    suzukiPsi_eq_mangoldtBlock h le_rfl
      (Real.log_le_log (by exact_mod_cast h.left_pos)
        (by exact_mod_cast h.left_lt.le))]
  nlinarith

/-- The event safety energy obtained from the true prime-scale curvature
lower bound rather than the unit-curvature surrogate. -/
noncomputable def suzukiEventCurvatureSafetyEnergy (q : ℕ) : ℝ :=
  suzukiEventValue q -
    suzukiNegativePart (suzukiEventSlopeDeficit q) ^ 2 /
      (2 * suzukiMangoldtBlockCurvatureLower q)

private theorem negativePart_quadratic_lower_of_pos
    {m d x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    -(suzukiNegativePart d) ^ 2 / (2 * m) ≤
      d * x + m * x ^ 2 / 2 := by
  by_cases hd : 0 ≤ d
  · have hneg : suzukiNegativePart d = 0 := by
      simp [suzukiNegativePart, hd]
    rw [hneg]
    norm_num
    positivity
  · have hd' : d < 0 := lt_of_not_ge hd
    have hneg : suzukiNegativePart d = -d := by
      simp [suzukiNegativePart, le_of_lt hd']
    rw [hneg]
    have hden : 0 < 2 * m := by positivity
    apply (div_le_iff₀ hden).2
    field_simp [ne_of_gt hm]
    nlinarith [sq_nonneg (m * x + d)]

theorem curvatureSafetyEnergy_le_suzukiPsi_on_block
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (htq : Real.log q ≤ t) (htr : t ≤ Real.log r) :
    suzukiEventCurvatureSafetyEnergy q ≤ suzukiPsi t := by
  have hm := suzukiMangoldtBlockCurvatureLower_pos h.left_event.two_le
  have hquad := curvatureWeighted_quadratic_envelope h htq htr
  have hneg := negativePart_quadratic_lower_of_pos
    (d := suzukiEventSlopeDeficit q) (x := t - Real.log q)
    hm (sub_nonneg.mpr htq)
  have hneg' :
      -(suzukiNegativePart (suzukiEventSlopeDeficit q) ^ 2 /
        (2 * suzukiMangoldtBlockCurvatureLower q)) ≤
        suzukiEventSlopeDeficit q * (t - Real.log q) +
          suzukiMangoldtBlockCurvatureLower q * (t - Real.log q) ^ 2 / 2 := by
    simpa only [neg_div] using hneg
  unfold suzukiEventCurvatureSafetyEnergy
  calc
    suzukiEventValue q -
        suzukiNegativePart (suzukiEventSlopeDeficit q) ^ 2 /
          (2 * suzukiMangoldtBlockCurvatureLower q) =
        suzukiEventValue q +
          (-(suzukiNegativePart (suzukiEventSlopeDeficit q) ^ 2 /
            (2 * suzukiMangoldtBlockCurvatureLower q))) := by ring
    _ ≤ suzukiEventValue q +
        (suzukiEventSlopeDeficit q * (t - Real.log q) +
          suzukiMangoldtBlockCurvatureLower q * (t - Real.log q) ^ 2 / 2) :=
      add_le_add (le_refl _) hneg'
    _ = suzukiEventValue q + suzukiEventSlopeDeficit q * (t - Real.log q) +
        suzukiMangoldtBlockCurvatureLower q * (t - Real.log q) ^ 2 / 2 := by ring
    _ ≤ suzukiPsi t := hquad

theorem mangoldtBlock_nonnegative_of_curvatureSafetyEnergy
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hE : 0 ≤ suzukiEventCurvatureSafetyEnergy q) :
    ∀ t, Real.log q ≤ t → t ≤ Real.log r → 0 ≤ suzukiPsi t := by
  intro t htq htr
  exact hE.trans (curvatureSafetyEnergy_le_suzukiPsi_on_block h htq htr)

theorem curvatureSafetyEnergy_le_blockMargin
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventCurvatureSafetyEnergy q ≤ suzukiMangoldtBlockMargin q r := by
  obtain ⟨t, ht, hmargin, _⟩ := mangoldtBlockMargin_eq_minimum h
  rw [hmargin]
  exact curvatureSafetyEnergy_le_suzukiPsi_on_block h ht.1 ht.2

/-- The compact initial interval plus curvature-weighted event safety is a
strictly sufficient criterion for RH. No safety premise is asserted. -/
theorem riemannHypothesis_of_initial_and_curvatureEventSafety
    (hinit : SuzukiInitialNonnegative)
    (hE : ∀ q r : ℕ, IsMangoldtBlock q r →
      0 ≤ suzukiEventCurvatureSafetyEnergy q) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_initial_and_all_mangoldtBlockMargins]
  refine ⟨hinit, ?_⟩
  intro q r h
  exact (hE q r h).trans (curvatureSafetyEnergy_le_blockMargin h)

/-! ## Sharp geometry of an optimizer kick -/

/-- A monotone one-Lipschitz graph has area between the two extremal
triangles determined by its endpoint displacement. -/
theorem integral_monotone_oneLipschitz_endpoint_bounds
    {f : ℝ → ℝ} (hfmono : Monotone f) (hflip : LipschitzWith 1 f)
    {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 / 2 ≤ ∫ x in a..b, (f x - f a) ∧
      (∫ x in a..b, (f x - f a)) ≤
        (b - a) * (f b - f a) - (f b - f a) ^ 2 / 2 := by
  let D := f b - f a
  have hD0 : 0 ≤ D := sub_nonneg.mpr (hfmono hab)
  have hDle : D ≤ b - a := by
    have hlip := hflip.dist_le_mul b a
    rw [Real.dist_eq, Real.dist_eq] at hlip
    norm_num at hlip
    rw [abs_of_nonneg hD0, abs_of_nonneg (sub_nonneg.mpr hab)] at hlip
    exact hlip
  have hfcont : Continuous f := hflip.continuous
  have hgint : ∀ u v, IntervalIntegrable (fun x => f x - f a)
      MeasureTheory.volume u v := fun u v =>
    (hfcont.sub continuous_const).intervalIntegrable u v
  have hlinInt : ∀ u v, IntervalIntegrable (fun x : ℝ => x)
      MeasureTheory.volume u v := fun u v => continuous_id.intervalIntegrable u v
  have hcInt : ∀ (c u v : ℝ), IntervalIntegrable (fun _x : ℝ => c)
      MeasureTheory.volume u v := fun _c u v => continuous_const.intervalIntegrable u v
  constructor
  · let c := b - D
    have hac : a ≤ c := by dsimp [c]; linarith
    have hcb : c ≤ b := by dsimp [c]; linarith
    have hleft : 0 ≤ ∫ x in a..c, (f x - f a) := by
      apply intervalIntegral.integral_nonneg hac
      intro x hx
      exact sub_nonneg.mpr (hfmono hx.1)
    have hright :
        (∫ x in c..b, (D - (b - x))) ≤
          ∫ x in c..b, (f x - f a) := by
      apply intervalIntegral.integral_mono_on hcb
        ((continuous_const.sub (continuous_const.sub continuous_id)).intervalIntegrable _ _)
        (hgint _ _)
      intro x hx
      have hfxb : f x ≤ f b := hfmono hx.2
      have hlip := hflip.dist_le_mul b x
      rw [Real.dist_eq, Real.dist_eq] at hlip
      norm_num at hlip
      rw [abs_of_nonneg (sub_nonneg.mpr hfxb),
        abs_of_nonneg (sub_nonneg.mpr hx.2)] at hlip
      dsimp [D]
      linarith
    have htri : (∫ x in c..b, (D - (b - x))) = D ^ 2 / 2 := by
      rw [show (fun x : ℝ => D - (b - x)) = fun x => (D - b) + x by
        funext x
        ring]
      rw [intervalIntegral.integral_add (hcInt (D - b) _ _) (hlinInt _ _)]
      simp only [intervalIntegral.integral_const, integral_id]
      dsimp [c]
      ring
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgint a c) (hgint c b)
    rw [htri] at hright
    linarith
  · let c := a + D
    have hac : a ≤ c := by dsimp [c]; linarith
    have hcb : c ≤ b := by dsimp [c]; linarith
    have hleft :
        (∫ x in a..c, (f x - f a)) ≤ ∫ x in a..c, (x - a) := by
      apply intervalIntegral.integral_mono_on hac (hgint _ _)
        ((continuous_id.sub continuous_const).intervalIntegrable _ _)
      intro x hx
      have hfax : f a ≤ f x := hfmono hx.1
      have hlip := hflip.dist_le_mul x a
      rw [Real.dist_eq, Real.dist_eq] at hlip
      norm_num at hlip
      rw [abs_of_nonneg (sub_nonneg.mpr hfax),
        abs_of_nonneg (sub_nonneg.mpr hx.1)] at hlip
      exact hlip
    have hright :
        (∫ x in c..b, (f x - f a)) ≤ ∫ _x in c..b, D := by
      apply intervalIntegral.integral_mono_on hcb (hgint _ _)
        (hcInt D _ _)
      intro x hx
      dsimp [D]
      exact sub_le_sub_right (hfmono hx.2) _
    have hleftValue : (∫ x in a..c, (x - a)) = D ^ 2 / 2 := by
      rw [intervalIntegral.integral_sub (hlinInt _ _) (hcInt a _ _)]
      simp only [integral_id, intervalIntegral.integral_const]
      dsimp [c]
      ring
    have hrightValue : (∫ _x in c..b, D) = (b - a - D) * D := by
      simp only [intervalIntegral.integral_const]
      dsimp [c]
      ring
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgint a c) (hgint c b)
    rw [hleftValue] at hleft
    rw [hrightValue] at hright
    nlinarith

theorem optimizerKickArea_bounds_sharp (q r : ℕ) :
    suzukiOptimizerKickDisplacement q r ^ 2 / 2 ≤
        suzukiOptimizerKickArea q r ∧
      suzukiOptimizerKickArea q r ≤
        suzukiMangoldtEventWeight r * suzukiOptimizerKickDisplacement q r -
          suzukiOptimizerKickDisplacement q r ^ 2 / 2 := by
  have h := integral_monotone_oneLipschitz_endpoint_bounds
    suzukiArchDualOptimizer_monotone suzukiArchDualOptimizer_lipschitz
    (a := suzukiMangoldtSlope q)
    (b := suzukiMangoldtSlope q + suzukiMangoldtEventWeight r)
    (le_add_of_nonneg_right (suzukiMangoldtEventWeight_nonneg r))
  simpa [suzukiOptimizerKickArea, suzukiOptimizerKickDisplacement] using h

theorem globalMargin_event_update_lower_final
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtEventWeight r * suzukiEventOptimizerDisplacement r +
        suzukiOptimizerKickDisplacement q r ^ 2 / 2 ≤
      suzukiGlobalDualMargin r - suzukiGlobalDualMargin q := by
  rw [globalDualMargin_block_update_kickArea h,
    suzukiEventOptimizerDisplacement_next h]
  have harea := (optimizerKickArea_bounds_sharp q r).2
  ring_nf at harea ⊢
  linarith

theorem globalMargin_event_update_upper_final
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiGlobalDualMargin r - suzukiGlobalDualMargin q ≤
      suzukiMangoldtEventWeight r * suzukiEventOptimizerDisplacement r +
        suzukiMangoldtEventWeight r * suzukiOptimizerKickDisplacement q r -
          suzukiOptimizerKickDisplacement q r ^ 2 / 2 := by
  rw [globalDualMargin_block_update_kickArea h,
    suzukiEventOptimizerDisplacement_next h]
  have harea := (optimizerKickArea_bounds_sharp q r).1
  ring_nf at harea ⊢
  linarith

theorem globalMargin_nondec_of_postEventOptimizer_left
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hx : 0 ≤ suzukiEventOptimizerDisplacement r) :
    suzukiGlobalDualMargin q ≤ suzukiGlobalDualMargin r := by
  have hlower := globalMargin_event_update_lower_final h
  have hw := suzukiMangoldtEventWeight_nonneg r
  have hk := sq_nonneg (suzukiOptimizerKickDisplacement q r)
  nlinarith

/-- Queue-style workload: positive exactly while the archimedean optimizer
lies to the right of the current event. -/
noncomputable def suzukiOptimizerBacklog (q : ℕ) : ℝ :=
  max (-suzukiEventOptimizerDisplacement q) 0

theorem suzukiOptimizerBacklog_next_le
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiOptimizerBacklog r ≤
      max (suzukiOptimizerBacklog q + suzukiOptimizerKickDisplacement q r -
        suzukiMangoldtLogGap q r) 0 := by
  rw [suzukiOptimizerBacklog, suzukiOptimizerBacklog,
    suzukiEventOptimizerDisplacement_next h]
  apply max_le
  · apply le_max_of_le_left
    have hx : -suzukiEventOptimizerDisplacement q ≤
        max (-suzukiEventOptimizerDisplacement q) 0 := le_max_left _ _
    linarith
  · exact le_max_right _ _

/-! ## True-curvature control of optimizer displacement -/

private theorem monotoneOn_archDeriv_sub_expBase_mul_id
    {t₀ : ℝ} (ht₀ : Real.log 2 ≤ t₀) :
    MonotoneOn
      (fun t : ℝ => deriv suzukiPsiArchimedean t -
        ((5 / 6 : ℝ) * Real.exp (t₀ / 2)) * t)
      (Ici t₀) := by
  let m : ℝ := (5 / 6 : ℝ) * Real.exp (t₀ / 2)
  have ht₀pos : 0 < t₀ := (Real.log_pos (by norm_num)).trans_le ht₀
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t ht
    exact ((hasDerivAt_deriv_suzukiPsiArchimedean
      (ht₀pos.trans_le ht)).sub
        ((hasDerivAt_id t).const_mul m)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact ((hasDerivAt_deriv_suzukiPsiArchimedean
      (ht₀pos.trans ht)).sub
        ((hasDerivAt_id t).const_mul m)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    change t₀ < t at ht
    have hraw := ((hasDerivAt_deriv_suzukiPsiArchimedean
      (ht₀pos.trans ht)).sub ((hasDerivAt_id t).const_mul m)).deriv
    have hfive := five_sixths_exp_le_secondDeriv_arch (ht₀.trans ht.le)
    have hexp : Real.exp (t₀ / 2) ≤ Real.exp (t / 2) := by
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ht.le (by norm_num))
    change 0 ≤ deriv
      (deriv suzukiPsiArchimedean - fun t : ℝ => m * id t) t
    rw [hraw]
    rw [secondDeriv_suzukiPsiArchimedean (ht₀pos.trans ht)] at hfive
    dsimp [m]
    nlinarith

/-- The optimizer response is controlled by the actual exponential
curvature at its pre-kick location, not merely by unit curvature. -/
theorem optimizerKickDisplacement_le_exp_bound (q r : ℕ) :
    suzukiOptimizerKickDisplacement q r ≤
      (6 * suzukiMangoldtEventWeight r) /
        (5 * Real.exp
          (suzukiArchDualOptimizer (suzukiMangoldtSlope q) / 2)) := by
  let S := suzukiMangoldtSlope q
  let l := suzukiMangoldtEventWeight r
  let t₀ := suzukiArchDualOptimizer S
  let t₁ := suzukiArchDualOptimizer (S + l)
  let m : ℝ := (5 / 6 : ℝ) * Real.exp (t₀ / 2)
  have hl : 0 ≤ l := suzukiMangoldtEventWeight_nonneg r
  have ht₀mem : Real.log 2 ≤ t₀ := suzukiArchDualOptimizer_mem_Ici S
  have htmono : t₀ ≤ t₁ := suzukiArchDualOptimizer_monotone
    (le_add_of_nonneg_right hl)
  have hm : 0 < m := by dsimp [m]; positivity
  rcases htmono.eq_or_lt with heq | hlt
  · have hdisp : suzukiOptimizerKickDisplacement q r = 0 := by
      unfold suzukiOptimizerKickDisplacement
      dsimp [t₀, t₁, S, l] at heq ⊢
      exact sub_eq_zero.mpr heq.symm
    rw [hdisp]
    positivity
  · have hA₀ : S ≤ deriv suzukiPsiArchimedean t₀ := by
      rcases ht₀mem.eq_or_lt with heq₀ | hlt₀
      · rw [← heq₀]
        exact le_archDeriv_log_two_of_optimizer_eq heq₀.symm
      · exact le_of_eq (deriv_archimedean_at_dualOptimizer_of_lt hlt₀).symm
    have hA₁ : deriv suzukiPsiArchimedean t₁ = S + l :=
      deriv_archimedean_at_dualOptimizer_of_lt (lt_of_le_of_lt ht₀mem hlt)
    have hstrong := monotoneOn_archDeriv_sub_expBase_mul_id ht₀mem
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr htmono) htmono
    have hml : m * (t₁ - t₀) ≤ l := by
      dsimp [m, t₀, t₁, S, l] at hA₀ hA₁ hstrong ⊢
      nlinarith
    unfold suzukiOptimizerKickDisplacement
    dsimp [t₀, t₁, S, l, m] at hm hml ⊢
    have hden : 0 < 5 * Real.exp
        (suzukiArchDualOptimizer (suzukiMangoldtSlope q) / 2) := by positivity
    apply (le_div_iff₀ hden).2
    nlinarith

/-- Location of the next event relative to the optimizer before its Mangoldt
kick. -/
noncomputable def suzukiPreKickOptimizerDisplacement (q r : ℕ) : ℝ :=
  Real.log r - suzukiArchDualOptimizer (suzukiMangoldtSlope q)

/-- Event-local form of the true-curvature kick bound.  The exponential at
the old optimizer is rewritten using the event scale `sqrt r` and the
pre-kick displacement. -/
theorem optimizerKickDisplacement_le_event_scale
    {q r : ℕ} (hr : 0 < r) :
    suzukiOptimizerKickDisplacement q r ≤
      (6 / 5 : ℝ) * suzukiMangoldtEventWeight r *
        Real.exp (suzukiPreKickOptimizerDisplacement q r / 2) /
          Real.sqrt r := by
  have hsqrtpos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrt : Real.exp (Real.log (r : ℝ) / 2) = Real.sqrt r := by
    rw [← Real.log_sqrt (by positivity), Real.exp_log hsqrtpos]
  calc
    suzukiOptimizerKickDisplacement q r ≤
        (6 * suzukiMangoldtEventWeight r) /
          (5 * Real.exp
            (suzukiArchDualOptimizer (suzukiMangoldtSlope q) / 2)) :=
      optimizerKickDisplacement_le_exp_bound q r
    _ = (6 / 5 : ℝ) * suzukiMangoldtEventWeight r *
          Real.exp (suzukiPreKickOptimizerDisplacement q r / 2) /
            Real.sqrt r := by
      rw [suzukiPreKickOptimizerDisplacement, sub_div, Real.exp_sub, hsqrt]
      field_simp
      <;> ring

end RHGarden
