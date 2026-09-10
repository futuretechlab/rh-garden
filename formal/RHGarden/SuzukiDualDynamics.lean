import RHGarden.SuzukiMangoldtBlocks
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace RHGarden

/-! ## Global archimedean curvature and quadratic growth -/

/-- The archimedean term has curvature at least one on the complete
half-line beginning at the first Mangoldt event. -/
theorem one_le_secondDeriv_suzukiArchimedean
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    1 ≤ deriv (deriv suzukiPsiArchimedean) t :=
  one_le_secondDeriv_suzukiPsiArchimedean_of_log_two_le ht

/-- Subtracting the identity from the archimedean derivative leaves a
monotone function.  This is the differential form of unit strong
convexity. -/
theorem monotoneOn_archDeriv_sub_id :
    MonotoneOn (fun t : ℝ => deriv suzukiPsiArchimedean t - t)
      (Ici (Real.log 2)) := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t ht
    exact ((hasDerivAt_deriv_suzukiPsiArchimedean
      (ha.trans_le ht)).sub (hasDerivAt_id t)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact ((hasDerivAt_deriv_suzukiPsiArchimedean
      (ha.trans ht)).sub (hasDerivAt_id t)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    change 0 ≤ deriv (deriv suzukiPsiArchimedean - id) t
    rw [((hasDerivAt_deriv_suzukiPsiArchimedean
      (ha.trans ht)).sub (hasDerivAt_id t)).deriv]
    have hc : 1 ≤ suzukiPsiCurvature t := by
      rw [← (hasDerivAt_deriv_suzukiPsiArchimedean (ha.trans ht)).deriv]
      exact one_le_secondDeriv_suzukiArchimedean ht.le
    linarith

/-- The archimedean derivative is strictly increasing on the global
half-line. -/
theorem deriv_suzukiPsiArchimedean_strictMonoOn :
    StrictMonoOn (deriv suzukiPsiArchimedean) (Ici (Real.log 2)) := by
  intro x hx y hy hxy
  have hmono := monotoneOn_archDeriv_sub_id hx hy hxy.le
  linarith

/-- Unit curvature gives the exact quadratic supporting inequality at any
point on the archimedean half-line. -/
theorem suzukiArchimedean_strong_tangent_lower
    {x y : ℝ} (hx : Real.log 2 ≤ x) (hy : Real.log 2 ≤ y) :
    suzukiPsiArchimedean x + deriv suzukiPsiArchimedean x * (y - x) +
        (y - x) ^ 2 / 2 ≤ suzukiPsiArchimedean y := by
  let g : ℝ → ℝ := fun t => suzukiPsiArchimedean t - t ^ 2 / 2
  let q : ℝ → ℝ := fun t => deriv suzukiPsiArchimedean t - t
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgcont : ContinuousOn g (Ici (Real.log 2)) := by
    intro t ht
    dsimp [g]
    exact ((differentiableAt_suzukiPsiArchimedean_of_pos
      (ha.trans_le ht)).continuousAt.sub
        (((continuousAt_id.pow 2).div_const 2))).continuousWithinAt
  have hgconv : ConvexOn ℝ (Ici (Real.log 2)) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _) hgcont
    · intro t ht
      rw [interior_Ici] at ht
      have hsq : HasDerivAt (fun z : ℝ => z ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_id t).pow 2).div_const 2
      exact ((differentiableAt_suzukiPsiArchimedean_of_pos
        (ha.trans ht)).hasDerivAt.sub hsq).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact ((hasDerivAt_deriv_suzukiPsiArchimedean
        (ha.trans ht)).sub (hasDerivAt_id t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hc : 1 ≤ suzukiPsiCurvature t := by
        rw [← (hasDerivAt_deriv_suzukiPsiArchimedean (ha.trans ht)).deriv]
        exact one_le_secondDeriv_suzukiArchimedean ht.le
      linarith
  have hgx : HasDerivAt g (q x) x := by
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2 / 2) x x := by
      simpa using ((hasDerivAt_id x).pow 2).div_const 2
    exact (differentiableAt_suzukiPsiArchimedean_of_pos
      (ha.trans_le hx)).hasDerivAt.sub hsq
  have htangent : g x + q x * (y - x) ≤ g y := by
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have hs := hgconv.le_slope_of_hasDerivAt hx hy hxy hgx
      rw [slope_def_field] at hs
      have hmul := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
      linarith
    · simp
    · have hs := hgconv.slope_le_of_hasDerivAt hy hx hyx hgx
      rw [slope_def_field] at hs
      have hmul := (div_le_iff₀ (sub_pos.mpr hyx)).mp hs
      nlinarith
  dsimp [g, q] at htangent
  nlinarith

/-- Quadratic lower growth based at `log 2`. -/
theorem suzukiArchimedean_quadratic_lower
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiPsiArchimedean (Real.log 2) +
        deriv suzukiPsiArchimedean (Real.log 2) * (t - Real.log 2) +
        (t - Real.log 2) ^ 2 / 2 ≤ suzukiPsiArchimedean t :=
  suzukiArchimedean_strong_tangent_lower le_rfl ht

/-- The unrestricted dual objective is bounded above without using any
special-function asymptotic estimate. -/
theorem bddAbove_suzukiArchCellObjective_Ici (S : ℝ) :
    BddAbove (suzukiArchCellObjective S '' Ici (Real.log 2)) := by
  let a := Real.log 2
  let d := deriv suzukiPsiArchimedean a
  let B := S * a - suzukiPsiArchimedean a + (S - d) ^ 2 / 2
  refine ⟨B, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hA := suzukiArchimedean_quadratic_lower ht
  have hsq : 0 ≤ ((t - a) - (S - d)) ^ 2 := sq_nonneg _
  dsimp [a, d, B, suzukiArchCellObjective] at hA hsq ⊢
  nlinarith

/-- The unrestricted global dual margin is an unconditional sufficient
certificate for the margin of any complete Mangoldt block. -/
theorem globalDualMargin_nonneg_implies_mangoldtBlockMargin_nonneg
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hm : 0 ≤ suzukiGlobalDualMargin q) :
    0 ≤ suzukiMangoldtBlockMargin q r :=
  globalDualMargin_nonneg_implies_blockMargin_nonneg h
    (bddAbove_suzukiArchCellObjective_Ici _) hm

/-- A quantitative tail cutoff: past this explicit point the objective is
no larger than its value at the boundary `log 2`. -/
theorem suzukiArchCellObjective_le_boundary_of_large
    (S : ℝ) {t : ℝ}
    (ht : Real.log 2 +
        2 * (|S - deriv suzukiPsiArchimedean (Real.log 2)| + 1) ≤ t) :
    suzukiArchCellObjective S t ≤
      suzukiArchCellObjective S (Real.log 2) := by
  let a := Real.log 2
  let c := S - deriv suzukiPsiArchimedean a
  have hta : a ≤ t := by
    dsimp [a, c] at ht ⊢
    have : 0 ≤ |S - deriv suzukiPsiArchimedean (Real.log 2)| := abs_nonneg _
    linarith
  have hA := suzukiArchimedean_quadratic_lower hta
  have hx : 2 * (|c| + 1) ≤ t - a := by
    dsimp [a, c] at ht ⊢
    linarith
  have hc : c ≤ |c| := le_abs_self c
  have hxp : 0 ≤ t - a := sub_nonneg.mpr hta
  dsimp [a, c, suzukiArchCellObjective] at hA hc hx hxp ⊢
  nlinarith

/-- The objective tends to minus infinity, again solely from unit
curvature. -/
theorem tendsto_suzukiArchObjective_atTop (S : ℝ) :
    Tendsto (suzukiArchCellObjective S) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  let a := Real.log 2
  let c := S - deriv suzukiPsiArchimedean a
  let K := |c| + |suzukiArchCellObjective S a - b| + 1
  refine ⟨a + 2 * K, ?_⟩
  intro t ht
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have hc0 := abs_nonneg c
    have hb0 := abs_nonneg (suzukiArchCellObjective S a - b)
    linarith
  have hta : a ≤ t := by linarith
  have hA := suzukiArchimedean_quadratic_lower hta
  have hx : 2 * K ≤ t - a := by linarith
  have hc : c ≤ |c| := le_abs_self c
  have habs : -( |suzukiArchCellObjective S a - b| ) ≤
      b - suzukiArchCellObjective S a := by
    simpa [abs_sub_comm] using neg_abs_le (b - suzukiArchCellObjective S a)
  have hxp : 0 ≤ t - a := sub_nonneg.mpr hta
  have hcx : c * (t - a) ≤ |c| * (t - a) :=
    mul_le_mul_of_nonneg_right hc hxp
  have hmul : 0 ≤ (t - a - 2 * K) * (t - a) :=
    mul_nonneg (sub_nonneg.mpr hx) hxp
  have hobj : suzukiArchCellObjective S t ≤
      suzukiArchCellObjective S a + c * (t - a) - (t - a) ^ 2 / 2 := by
    dsimp [a, c, suzukiArchCellObjective] at hA ⊢
    nlinarith
  have hxone : 1 ≤ t - a := by nlinarith
  have htail : c * (t - a) - (t - a) ^ 2 / 2 ≤
      -|suzukiArchCellObjective S a - b| := by
    dsimp [K] at hx hmul hK0 hK1
    nlinarith [mul_nonneg (abs_nonneg (suzukiArchCellObjective S a - b))
      (sub_nonneg.mpr hxone)]
  linarith

/-! ## Attainment of the unrestricted dual -/

private noncomputable def suzukiArchObjectiveCutoff (S : ℝ) : ℝ :=
  Real.log 2 + 2 *
    (|S - deriv suzukiPsiArchimedean (Real.log 2)| + 1)

theorem exists_suzukiArchObjective_isMaxOn_Ici (S : ℝ) :
    ∃ t ∈ Ici (Real.log 2),
      IsMaxOn (suzukiArchCellObjective S) (Ici (Real.log 2)) t := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have haR : Real.log 2 ≤ suzukiArchObjectiveCutoff S := by
    unfold suzukiArchObjectiveCutoff
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (by positivity))
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr haR)
    (continuousOn_suzukiArchCellObjective_Icc (s := S) ha)
  refine ⟨t, ht.1, ?_⟩
  intro y hy
  by_cases hyR : y ≤ suzukiArchObjectiveCutoff S
  · exact hmax ⟨hy, hyR⟩
  · have htail : suzukiArchCellObjective S y ≤
        suzukiArchCellObjective S (Real.log 2) := by
      apply suzukiArchCellObjective_le_boundary_of_large
      simpa [suzukiArchObjectiveCutoff] using le_of_not_ge hyR
    exact htail.trans (hmax ⟨le_rfl, haR⟩)

/-- The unique maximizing location of the unrestricted archimedean dual. -/
noncomputable def suzukiArchDualOptimizer (S : ℝ) : ℝ :=
  Classical.choose (exists_suzukiArchObjective_isMaxOn_Ici S)

theorem suzukiArchDualOptimizer_mem_Ici (S : ℝ) :
    suzukiArchDualOptimizer S ∈ Ici (Real.log 2) :=
  (Classical.choose_spec (exists_suzukiArchObjective_isMaxOn_Ici S)).1

theorem suzukiArchDualOptimizer_isMaxOn (S : ℝ) :
    IsMaxOn (suzukiArchCellObjective S) (Ici (Real.log 2))
      (suzukiArchDualOptimizer S) :=
  (Classical.choose_spec (exists_suzukiArchObjective_isMaxOn_Ici S)).2

theorem suzukiArchDual_eq_optimizer (S : ℝ) :
    suzukiArchDual S =
      S * suzukiArchDualOptimizer S -
        suzukiPsiArchimedean (suzukiArchDualOptimizer S) := by
  unfold suzukiArchDual suzukiArchCellObjective
  apply IsGreatest.csSup_eq
  refine ⟨⟨suzukiArchDualOptimizer S,
    suzukiArchDualOptimizer_mem_Ici S, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact suzukiArchDualOptimizer_isMaxOn S ht

/-- The half-line objective is strictly concave, so its attained maximum is
unique. -/
theorem strictConcaveOn_suzukiArchCellObjective_Ici (S : ℝ) :
    StrictConcaveOn ℝ (Ici (Real.log 2)) (suzukiArchCellObjective S) := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn (suzukiArchCellObjective S) (Ici (Real.log 2)) := by
    intro t ht
    exact (hasDerivAt_suzukiArchCellObjective S
      (ha.trans_le ht)).continuousAt.continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Ici _) hcont
  intro t ht
  rw [interior_Ici] at ht
  change deriv (deriv (suzukiArchCellObjective S)) t < 0
  rw [secondDeriv_suzukiArchCellObjective S (ha.trans ht)]
  linarith [one_le_secondDeriv_suzukiArchimedean ht.le]

theorem suzukiArchDualOptimizer_unique
    {S t : ℝ} (ht : t ∈ Ici (Real.log 2))
    (hmax : IsMaxOn (suzukiArchCellObjective S) (Ici (Real.log 2)) t) :
    t = suzukiArchDualOptimizer S := by
  exact (strictConcaveOn_suzukiArchCellObjective_Ici S).eq_of_isMaxOn
    hmax (suzukiArchDualOptimizer_isMaxOn S)
    ht (suzukiArchDualOptimizer_mem_Ici S)

/-- Slopes below the boundary derivative are maximized at the boundary. -/
theorem suzukiArchDualOptimizer_eq_log_two_of_le
    {S : ℝ}
    (hS : S ≤ deriv suzukiPsiArchimedean (Real.log 2)) :
    suzukiArchDualOptimizer S = Real.log 2 := by
  have hmax : IsMaxOn (suzukiArchCellObjective S) (Ici (Real.log 2))
      (Real.log 2) := by
    intro t ht
    change suzukiArchCellObjective S t ≤
      suzukiArchCellObjective S (Real.log 2)
    have hA := suzukiArchimedean_strong_tangent_lower le_rfl ht
    have hprod : (S - deriv suzukiPsiArchimedean (Real.log 2)) *
        (t - Real.log 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hS) (sub_nonneg.mpr ht)
    unfold suzukiArchCellObjective
    ring_nf at hA hprod ⊢
    nlinarith [sq_nonneg (t - Real.log 2)]
  exact (suzukiArchDualOptimizer_unique (S := S)
    (Set.mem_Ici.mpr le_rfl) hmax).symm

/-- At an interior optimizer the archimedean derivative equals the dual
slope. -/
theorem deriv_archimedean_at_dualOptimizer_of_lt
    {S : ℝ}
    (hS : Real.log 2 < suzukiArchDualOptimizer S) :
    deriv suzukiPsiArchimedean (suzukiArchDualOptimizer S) = S := by
  have hnhds : Ici (Real.log 2) ∈ nhds (suzukiArchDualOptimizer S) :=
    mem_of_superset (Ioi_mem_nhds hS) Ioi_subset_Ici_self
  have hzero := (suzukiArchDualOptimizer_isMaxOn S).isLocalMax hnhds |>.deriv_eq_zero
  rw [(hasDerivAt_suzukiArchCellObjective S
    ((Real.log_pos (by norm_num)).trans hS)).deriv] at hzero
  linarith

/-- A boundary optimizer forces the slope to be no larger than the boundary
derivative. -/
theorem le_archDeriv_log_two_of_optimizer_eq
    {S : ℝ} (hopt : suzukiArchDualOptimizer S = Real.log 2) :
    S ≤ deriv suzukiPsiArchimedean (Real.log 2) := by
  let a := Real.log 2
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hmax : IsMaxOn (suzukiArchCellObjective S) (Ici a) a := by
    simpa [a, hopt] using suzukiArchDualOptimizer_isMaxOn S
  have hseg : segment ℝ a (a + 1) ⊆ Ici a := by
    rw [segment_eq_Icc (by linarith : a ≤ a + 1)]
    exact Icc_subset_Ici_self
  have hone : (1 : ℝ) ∈ posTangentConeAt (Ici a) a := by
    have := sub_mem_posTangentConeAt_of_segment_subset hseg
    simpa using this
  have hderiv := hasDerivAt_suzukiArchCellObjective S ha
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hone
  simpa [a, fderiv_eq_deriv_mul, hderiv.deriv] using hnonpos

theorem suzukiArchDualOptimizer_eq_log_two_iff (S : ℝ) :
    suzukiArchDualOptimizer S = Real.log 2 ↔
      S ≤ deriv suzukiPsiArchimedean (Real.log 2) := by
  exact ⟨le_archDeriv_log_two_of_optimizer_eq,
    suzukiArchDualOptimizer_eq_log_two_of_le⟩

/-- Above the boundary threshold, the optimizer is the unique inverse image
of the slope under the archimedean derivative. -/
theorem deriv_archimedean_at_dualOptimizer
    {S : ℝ} (hS : deriv suzukiPsiArchimedean (Real.log 2) < S) :
    deriv suzukiPsiArchimedean (suzukiArchDualOptimizer S) = S := by
  apply deriv_archimedean_at_dualOptimizer_of_lt
  have hmem := suzukiArchDualOptimizer_mem_Ici S
  exact lt_of_le_of_ne hmem (fun heq =>
    (not_le_of_gt hS) (le_archDeriv_log_two_of_optimizer_eq heq.symm))

/-! ## Monotonicity and the envelope theorem -/

theorem suzukiArchDualOptimizer_monotone :
    Monotone suzukiArchDualOptimizer := by
  intro S₁ S₂ hS
  let t₁ := suzukiArchDualOptimizer S₁
  let t₂ := suzukiArchDualOptimizer S₂
  have h₁ := suzukiArchDualOptimizer_isMaxOn S₁
    (suzukiArchDualOptimizer_mem_Ici S₂)
  have h₂ := suzukiArchDualOptimizer_isMaxOn S₂
    (suzukiArchDualOptimizer_mem_Ici S₁)
  change suzukiArchCellObjective S₁ t₂ ≤ suzukiArchCellObjective S₁ t₁ at h₁
  change suzukiArchCellObjective S₂ t₁ ≤ suzukiArchCellObjective S₂ t₂ at h₂
  dsimp [t₁, t₂, suzukiArchCellObjective] at h₁ h₂ ⊢
  rcases hS.eq_or_lt with hEq | hLt
  · subst S₂
    exact le_rfl
  · by_contra hnot
    have htt : suzukiArchDualOptimizer S₂ < suzukiArchDualOptimizer S₁ :=
      lt_of_not_ge hnot
    have hp : 0 < (S₂ - S₁) *
        (suzukiArchDualOptimizer S₁ - suzukiArchDualOptimizer S₂) :=
      mul_pos (sub_pos.mpr hLt) (sub_pos.mpr htt)
    nlinarith

private theorem suzukiArchDualOptimizer_sub_le
    {S₁ S₂ : ℝ} (hS : S₁ ≤ S₂) :
    suzukiArchDualOptimizer S₂ - suzukiArchDualOptimizer S₁ ≤ S₂ - S₁ := by
  let t₁ := suzukiArchDualOptimizer S₁
  let t₂ := suzukiArchDualOptimizer S₂
  have htmono : t₁ ≤ t₂ := suzukiArchDualOptimizer_monotone hS
  have ht₁ : Real.log 2 ≤ t₁ := suzukiArchDualOptimizer_mem_Ici S₁
  have ht₂ : Real.log 2 ≤ t₂ := suzukiArchDualOptimizer_mem_Ici S₂
  rcases ht₁.eq_or_lt with ht₁eq | ht₁lt
  · have hS₁ : S₁ ≤ deriv suzukiPsiArchimedean (Real.log 2) :=
      le_archDeriv_log_two_of_optimizer_eq ht₁eq.symm
    rcases ht₂.eq_or_lt with ht₂eq | ht₂lt
    · dsimp [t₁, t₂] at ht₁eq ht₂eq ⊢
      linarith
    · have hd₂ := deriv_archimedean_at_dualOptimizer_of_lt (S := S₂) ht₂lt
      have hstrong := monotoneOn_archDeriv_sub_id
        (Set.mem_Ici.mpr le_rfl)
        (suzukiArchDualOptimizer_mem_Ici S₂) ht₂
      dsimp [t₁, t₂] at ht₁eq ht₂lt hd₂ hstrong ⊢
      rw [← ht₁eq]
      linarith
  · have hd₁ := deriv_archimedean_at_dualOptimizer_of_lt (S := S₁) ht₁lt
    have ht₂lt : Real.log 2 < t₂ := ht₁lt.trans_le htmono
    have hd₂ := deriv_archimedean_at_dualOptimizer_of_lt (S := S₂) ht₂lt
    have hstrong := monotoneOn_archDeriv_sub_id ht₁ ht₂ htmono
    dsimp [t₁, t₂] at htmono ht₁ ht₂ ht₁lt ht₂lt hd₁ hd₂ hstrong ⊢
    linarith

/-- Unit curvature makes the inverse-gradient optimizer globally
one-Lipschitz, including the constant boundary regime. -/
theorem suzukiArchDualOptimizer_lipschitz :
    LipschitzWith 1 suzukiArchDualOptimizer := by
  apply LipschitzWith.of_dist_le_mul
  intro S₁ S₂
  norm_num only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total S₁ S₂ with hS | hS
  · have ht := suzukiArchDualOptimizer_monotone hS
    rw [abs_of_nonpos (sub_nonpos.mpr ht), abs_of_nonpos (sub_nonpos.mpr hS)]
    linarith [suzukiArchDualOptimizer_sub_le hS]
  · have ht := suzukiArchDualOptimizer_monotone hS
    rw [abs_of_nonneg (sub_nonneg.mpr ht), abs_of_nonneg (sub_nonneg.mpr hS)]
    exact suzukiArchDualOptimizer_sub_le hS

theorem continuous_suzukiArchDualOptimizer :
    Continuous suzukiArchDualOptimizer :=
  suzukiArchDualOptimizer_lipschitz.continuous

/-- Secant slopes of the dual lie between the two optimizing locations. -/
theorem suzukiArchDual_secant_bounds
    {S₁ S₂ : ℝ} (hS : S₁ ≤ S₂) :
    (S₂ - S₁) * suzukiArchDualOptimizer S₁ ≤
        suzukiArchDual S₂ - suzukiArchDual S₁ ∧
      suzukiArchDual S₂ - suzukiArchDual S₁ ≤
        (S₂ - S₁) * suzukiArchDualOptimizer S₂ := by
  have h₁ := suzukiArchDualOptimizer_isMaxOn S₁
    (suzukiArchDualOptimizer_mem_Ici S₂)
  have h₂ := suzukiArchDualOptimizer_isMaxOn S₂
    (suzukiArchDualOptimizer_mem_Ici S₁)
  change suzukiArchCellObjective S₁ (suzukiArchDualOptimizer S₂) ≤
    suzukiArchCellObjective S₁ (suzukiArchDualOptimizer S₁) at h₁
  change suzukiArchCellObjective S₂ (suzukiArchDualOptimizer S₁) ≤
    suzukiArchCellObjective S₂ (suzukiArchDualOptimizer S₂) at h₂
  rw [suzukiArchDual_eq_optimizer, suzukiArchDual_eq_optimizer]
  unfold suzukiArchCellObjective at h₁ h₂
  constructor <;> nlinarith

private theorem suzukiArchDual_slope_between
    (S y : ℝ) (hy : y ≠ S) :
    min (suzukiArchDualOptimizer S) (suzukiArchDualOptimizer y) ≤
        slope suzukiArchDual S y ∧
      slope suzukiArchDual S y ≤
        max (suzukiArchDualOptimizer S) (suzukiArchDualOptimizer y) := by
  rcases lt_or_gt_of_ne hy with hyS | hSy
  · have hb := suzukiArchDual_secant_bounds hyS.le
    have hpos : 0 < S - y := sub_pos.mpr hyS
    have hslope : slope suzukiArchDual S y =
        (suzukiArchDual S - suzukiArchDual y) / (S - y) := by
      rw [slope_def_field]
      field_simp
      ring
    have hmono := suzukiArchDualOptimizer_monotone hyS.le
    rw [min_eq_right hmono, max_eq_left hmono, hslope]
    constructor
    · exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hb.1)
    · exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hb.2)
  · have hb := suzukiArchDual_secant_bounds hSy.le
    have hpos : 0 < y - S := sub_pos.mpr hSy
    have hmono := suzukiArchDualOptimizer_monotone hSy.le
    rw [min_eq_left hmono, max_eq_right hmono, slope_def_field]
    constructor
    · exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hb.1)
    · exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hb.2)

/-- The envelope theorem for this specialized half-line Legendre dual. -/
theorem hasDerivAt_suzukiArchDual (S : ℝ) :
    HasDerivAt suzukiArchDual (suzukiArchDualOptimizer S) S := by
  rw [hasDerivAt_iff_tendsto_slope]
  have htend : Tendsto suzukiArchDualOptimizer (𝓝[≠] S)
      (𝓝 (suzukiArchDualOptimizer S)) :=
    continuous_suzukiArchDualOptimizer.continuousAt.mono_left inf_le_left
  have hlo : Tendsto
      (fun y => min (suzukiArchDualOptimizer S) (suzukiArchDualOptimizer y))
      (𝓝[≠] S) (𝓝 (suzukiArchDualOptimizer S)) := by
    have hc : Tendsto (fun _ : ℝ => suzukiArchDualOptimizer S) (𝓝[≠] S)
        (𝓝 (suzukiArchDualOptimizer S)) := tendsto_const_nhds
    simpa using hc.min htend
  have hhi : Tendsto
      (fun y => max (suzukiArchDualOptimizer S) (suzukiArchDualOptimizer y))
      (𝓝[≠] S) (𝓝 (suzukiArchDualOptimizer S)) := by
    have hc : Tendsto (fun _ : ℝ => suzukiArchDualOptimizer S) (𝓝[≠] S)
        (𝓝 (suzukiArchDualOptimizer S)) := tendsto_const_nhds
    simpa using hc.max htend
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (suzukiArchDual_slope_between S y hy).1
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (suzukiArchDual_slope_between S y hy).2

theorem deriv_suzukiArchDual (S : ℝ) :
    deriv suzukiArchDual S = suzukiArchDualOptimizer S :=
  (hasDerivAt_suzukiArchDual S).deriv

/-- The dual increment is the exact area under its optimizer curve. -/
theorem suzukiArchDual_sub_eq_integral_optimizer
    {S lambda : ℝ} (hlambda : 0 ≤ lambda) :
    suzukiArchDual (S + lambda) - suzukiArchDual S =
      ∫ s in S..S + lambda, suzukiArchDualOptimizer s := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith : S ≤ S + lambda)
  · intro s hs
    exact (hasDerivAt_suzukiArchDual s).continuousAt.continuousWithinAt
  · intro s hs
    exact hasDerivAt_suzukiArchDual s
  · exact continuous_suzukiArchDualOptimizer.intervalIntegrable _ _

/-! ## Mangoldt event area dynamics -/

theorem suzukiMangoldtEventWeight_nonneg (q : ℕ) :
    0 ≤ suzukiMangoldtEventWeight q := by
  unfold suzukiMangoldtEventWeight
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- The exact event-margin update as signed area between the event location
and the dual optimizer curve. -/
theorem globalDualMargin_event_update_integral (n : ℕ) :
    suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n =
      ∫ s in suzukiMangoldtSlope n..
          suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1),
        (Real.log (n + 1) - suzukiArchDualOptimizer s) := by
  let S := suzukiMangoldtSlope n
  let lambda := suzukiMangoldtEventWeight (n + 1)
  have hlambda : 0 ≤ lambda := suzukiMangoldtEventWeight_nonneg _
  rw [globalDualMargin_event_update]
  rw [suzukiArchDual_sub_eq_integral_optimizer hlambda]
  have hconst :
      (∫ _s in S..S + lambda, Real.log (n + 1)) =
        lambda * Real.log (n + 1) := by
    simp [hlambda]
  have hintConst : IntervalIntegrable (fun _s : ℝ => Real.log (n + 1))
      MeasureTheory.volume S (S + lambda) := continuous_const.intervalIntegrable _ _
  have hintOpt : IntervalIntegrable suzukiArchDualOptimizer
      MeasureTheory.volume S (S + lambda) :=
    continuous_suzukiArchDualOptimizer.intervalIntegrable _ _
  dsimp [S, lambda] at hconst hintConst hintOpt ⊢
  rw [intervalIntegral.integral_sub hintConst hintOpt, hconst]

/-- Monotonicity of `tStar` sandwiches every event increment between its
pre- and post-event endpoint rectangles. -/
theorem globalDualMargin_event_update_bounds (n : ℕ) :
    suzukiMangoldtEventWeight (n + 1) *
        (Real.log (n + 1) -
          suzukiArchDualOptimizer
            (suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1))) ≤
      suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n ∧
    suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n ≤
      suzukiMangoldtEventWeight (n + 1) *
        (Real.log (n + 1) -
          suzukiArchDualOptimizer (suzukiMangoldtSlope n)) := by
  have hlambda := suzukiMangoldtEventWeight_nonneg (n + 1)
  have hb := suzukiArchDual_secant_bounds (S₁ := suzukiMangoldtSlope n)
    (S₂ := suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1))
    (by linarith)
  rw [globalDualMargin_event_update]
  constructor <;> nlinarith

/-- A purely local lower event certificate obtained from the one-Lipschitz
optimizer estimate. -/
theorem globalDualMargin_event_update_lower (n : ℕ) :
    suzukiMangoldtEventWeight (n + 1) *
          (Real.log (n + 1) -
            suzukiArchDualOptimizer (suzukiMangoldtSlope n)) -
        suzukiMangoldtEventWeight (n + 1) ^ 2 ≤
      suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n := by
  have hlambda := suzukiMangoldtEventWeight_nonneg (n + 1)
  have hlip := suzukiArchDualOptimizer_sub_le
    (S₁ := suzukiMangoldtSlope n)
    (S₂ := suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1))
    (by linarith)
  have hb := (globalDualMargin_event_update_bounds n).1
  nlinarith [mul_nonneg hlambda (sub_nonneg.mpr hlip)]

/-- Integrating the one-Lipschitz optimizer estimate improves the local
event certificate from a full square loss to the sharp triangular
`lambda^2/2` loss. -/
theorem globalDualMargin_event_update_lower_half (n : ℕ) :
    suzukiMangoldtEventWeight (n + 1) *
          (Real.log (n + 1) -
            suzukiArchDualOptimizer (suzukiMangoldtSlope n)) -
        suzukiMangoldtEventWeight (n + 1) ^ 2 / 2 ≤
      suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n := by
  let S := suzukiMangoldtSlope n
  let lambda := suzukiMangoldtEventWeight (n + 1)
  have hlambda : 0 ≤ lambda := suzukiMangoldtEventWeight_nonneg _
  have hmonoInt :
      (∫ s in S..S + lambda, suzukiArchDualOptimizer s) ≤
        ∫ s in S..S + lambda,
          (suzukiArchDualOptimizer S + (s - S)) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (continuous_suzukiArchDualOptimizer.intervalIntegrable _ _)
      ((continuous_const.add (continuous_id.sub continuous_const)).intervalIntegrable _ _)
    intro s hs
    have hlip := suzukiArchDualOptimizer_lipschitz.dist_le_mul s S
    rw [Real.dist_eq, Real.dist_eq] at hlip
    norm_num at hlip
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)] at hlip
    calc
      suzukiArchDualOptimizer s ≤ suzukiArchDualOptimizer S +
          |suzukiArchDualOptimizer s - suzukiArchDualOptimizer S| := by
        linarith [le_abs_self
          (suzukiArchDualOptimizer s - suzukiArchDualOptimizer S)]
      _ ≤ suzukiArchDualOptimizer S + (s - S) := by linarith
  have hupdate := globalDualMargin_event_update n
  rw [suzukiArchDual_sub_eq_integral_optimizer hlambda] at hupdate
  have haffine :
      (∫ s in S..S + lambda,
          (suzukiArchDualOptimizer S + (s - S))) =
        lambda * suzukiArchDualOptimizer S + lambda ^ 2 / 2 := by
    have hconst : Continuous (fun _s : ℝ => suzukiArchDualOptimizer S) :=
      continuous_const
    have hlinear : Continuous (fun s : ℝ => s - S) :=
      continuous_id.sub continuous_const
    have hid : Continuous (fun s : ℝ => s) := continuous_id
    have hSconst : Continuous (fun _s : ℝ => S) := continuous_const
    have hadd :
        (∫ s in S..S + lambda,
            (suzukiArchDualOptimizer S + (s - S))) =
          (∫ _s in S..S + lambda, suzukiArchDualOptimizer S) +
            ∫ s in S..S + lambda, (s - S) := by
      simpa only [Pi.add_apply] using intervalIntegral.integral_add
        (μ := MeasureTheory.volume) (hconst.intervalIntegrable _ _)
        (hlinear.intervalIntegrable _ _)
    have hsub :
        (∫ s in S..S + lambda, (s - S)) =
          (∫ s in S..S + lambda, s) -
            ∫ _s in S..S + lambda, S := by
      simpa only [Pi.sub_apply] using intervalIntegral.integral_sub
        (μ := MeasureTheory.volume) (hid.intervalIntegrable _ _)
        (hSconst.intervalIntegrable _ _)
    rw [hadd, hsub]
    simp only [intervalIntegral.integral_const, integral_id]
    ring
  rw [haffine] at hmonoInt
  dsimp [S, lambda] at hupdate hmonoInt ⊢
  nlinarith

/-! ## Event slope deficits -/

/-- Post-event archimedean slope surplus at the event location. -/
noncomputable def suzukiEventSlopeDeficit (q : ℕ) : ℝ :=
  deriv suzukiPsiArchimedean (Real.log q) - suzukiMangoldtSlope q

theorem suzukiArchDualOptimizer_deriv_archimedean
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiArchDualOptimizer (deriv suzukiPsiArchimedean t) = t := by
  have hmax : IsMaxOn
      (suzukiArchCellObjective (deriv suzukiPsiArchimedean t))
      (Ici (Real.log 2)) t := by
    intro y hy
    change suzukiArchCellObjective (deriv suzukiPsiArchimedean t) y ≤
      suzukiArchCellObjective (deriv suzukiPsiArchimedean t) t
    have hA := suzukiArchimedean_strong_tangent_lower ht hy
    unfold suzukiArchCellObjective
    nlinarith [sq_nonneg (y - t)]
  exact (suzukiArchDualOptimizer_unique ht hmax).symm

/-- Nonnegative event deficit is exactly the condition that the dual
optimizer lies no later than the event. -/
theorem suzukiEventSlopeDeficit_nonneg_iff
    {q : ℕ} (hq : 2 ≤ q) :
    0 ≤ suzukiEventSlopeDeficit q ↔
      suzukiArchDualOptimizer (suzukiMangoldtSlope q) ≤ Real.log q := by
  have hlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  constructor
  · intro hd
    unfold suzukiEventSlopeDeficit at hd
    have hm := suzukiArchDualOptimizer_monotone
      (show suzukiMangoldtSlope q ≤
        deriv suzukiPsiArchimedean (Real.log q) by linarith)
    rw [suzukiArchDualOptimizer_deriv_archimedean hlog] at hm
    exact hm
  · intro hopt
    unfold suzukiEventSlopeDeficit
    have hmem : Real.log 2 ≤ suzukiArchDualOptimizer (suzukiMangoldtSlope q) :=
      suzukiArchDualOptimizer_mem_Ici _
    rcases hmem.eq_or_lt with heq | hlt
    · have hthreshold := le_archDeriv_log_two_of_optimizer_eq heq.symm
      by_cases h2q : (2 : ℕ) = q
      · subst q
        simpa using hthreshold
      · have hloglt : Real.log 2 < Real.log q := by
          apply Real.log_lt_log (by norm_num)
          exact_mod_cast (lt_of_le_of_ne hq h2q)
        linarith [deriv_suzukiPsiArchimedean_strictMonoOn
          (Set.mem_Ici.mpr le_rfl) hlog hloglt]
    · have hslope := deriv_archimedean_at_dualOptimizer_of_lt
        (S := suzukiMangoldtSlope q) hlt
      have hmono := deriv_suzukiPsiArchimedean_strictMonoOn.monotoneOn
        (suzukiArchDualOptimizer_mem_Ici _) hlog hopt
      linarith

theorem mangoldtSlope_right_event
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtSlope r =
      suzukiMangoldtSlope q + suzukiMangoldtEventWeight r := by
  have hrpos : 0 < r := h.right_pos
  have hpred : q ≤ r - 1 := Nat.le_sub_one_of_lt h.left_lt
  have hpredlt : r - 1 < r := Nat.sub_lt hrpos (by omega)
  have hstate := mangoldtSlope_eq_on_block h hpred hpredlt
  have hsucc := suzukiMangoldtSlope_succ (r - 1)
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrpos)
  rw [Nat.sub_add_cancel hr1] at hsucc
  have hcast : (((r - 1 : ℕ) : ℝ) + 1) = (r : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hr1
  rw [hcast] at hsucc
  rw [hsucc, hstate]
  unfold suzukiMangoldtEventWeight
  rfl

/-- Between consecutive events the deficit receives smooth archimedean
drift and then the next Mangoldt impulse. -/
theorem suzukiEventSlopeDeficit_next
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiEventSlopeDeficit r = suzukiEventSlopeDeficit q +
      (deriv suzukiPsiArchimedean (Real.log r) -
        deriv suzukiPsiArchimedean (Real.log q)) -
      suzukiMangoldtEventWeight r := by
  unfold suzukiEventSlopeDeficit
  rw [mangoldtSlope_right_event h]
  ring

/-! ## Active blocks and drawdown geometry -/

/-- A constant-state block is active when the unrestricted optimizer lies
between its two event locations.  The definition uses the equivalent slope
crossing inequalities. -/
def IsActiveMangoldtBlock (q r : ℕ) : Prop :=
  IsMangoldtBlock q r ∧
    deriv suzukiPsiArchimedean (Real.log q) < suzukiMangoldtSlope q ∧
    suzukiMangoldtSlope q < deriv suzukiPsiArchimedean (Real.log r)

theorem IsActiveMangoldtBlock.optimizer_mem_Ioo
    {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiArchDualOptimizer (suzukiMangoldtSlope q) ∈
      Ioo (Real.log q) (Real.log r) := by
  have hblock := h.1
  have hqlog : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hblock.left_event.two_le)
  have hrlog : Real.log 2 ≤ Real.log r := hqlog.trans
    (Real.log_le_log (by exact_mod_cast hblock.left_pos)
      (by exact_mod_cast hblock.left_lt.le))
  have hbase : deriv suzukiPsiArchimedean (Real.log 2) <
      suzukiMangoldtSlope q := by
    have hmono := deriv_suzukiPsiArchimedean_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr le_rfl) hqlog hqlog
    linarith [h.2.1]
  have hslope := deriv_archimedean_at_dualOptimizer hbase
  have hoptmem := suzukiArchDualOptimizer_mem_Ici (suzukiMangoldtSlope q)
  constructor
  · by_contra hn
    have hle : suzukiArchDualOptimizer (suzukiMangoldtSlope q) ≤ Real.log q :=
      le_of_not_gt hn
    have hdle := deriv_suzukiPsiArchimedean_strictMonoOn.monotoneOn
      hoptmem hqlog hle
    linarith [h.2.1]
  · by_contra hn
    have hle : Real.log r ≤ suzukiArchDualOptimizer (suzukiMangoldtSlope q) :=
      le_of_not_gt hn
    have hdle := deriv_suzukiPsiArchimedean_strictMonoOn.monotoneOn
      hrlog hoptmem hle
    linarith [h.2.2]

theorem isActiveMangoldtBlock_iff_optimizer_mem
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsActiveMangoldtBlock q r ↔
      suzukiArchDualOptimizer (suzukiMangoldtSlope q) ∈
        Ioo (Real.log q) (Real.log r) := by
  constructor
  · exact IsActiveMangoldtBlock.optimizer_mem_Ioo
  · intro hopt
    have hqlog : Real.log 2 ≤ Real.log q :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le)
    have hoptmem : Real.log 2 ≤
        suzukiArchDualOptimizer (suzukiMangoldtSlope q) :=
      suzukiArchDualOptimizer_mem_Ici (suzukiMangoldtSlope q)
    have hslope := deriv_archimedean_at_dualOptimizer_of_lt
      (lt_of_le_of_lt hqlog hopt.1)
    refine ⟨h, ?_, ?_⟩
    · have hlt := deriv_suzukiPsiArchimedean_strictMonoOn
        hqlog hoptmem hopt.1
      linarith
    · have hrlog : Real.log 2 ≤ Real.log r := le_trans hqlog
        (Real.log_le_log (by exact_mod_cast h.left_pos)
          (by exact_mod_cast h.left_lt.le))
      have hlt := deriv_suzukiPsiArchimedean_strictMonoOn
        hoptmem hrlog hopt.2
      linarith

/-- On an active block the restricted dual is exactly the unrestricted
dual, rather than merely bounded by it. -/
theorem suzukiMangoldtBlockDual_eq_archDual_of_active
    {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiMangoldtBlockDual q r (suzukiMangoldtSlope q) =
      suzukiArchDual (suzukiMangoldtSlope q) := by
  have hblock := h.1
  apply le_antisymm
  · exact suzukiMangoldtBlockDual_le_archDual hblock
      (bddAbove_suzukiArchCellObjective_Ici _)
  · rw [suzukiArchDual_eq_optimizer]
    unfold suzukiMangoldtBlockDual
    have hopt := IsActiveMangoldtBlock.optimizer_mem_Ioo h
    exact le_suzukiArchIntervalDual
      (Real.log_pos (by exact_mod_cast hblock.left_event.two_le))
      (Real.log_le_log (by exact_mod_cast hblock.left_pos)
        (by exact_mod_cast hblock.left_lt.le))
      ⟨hopt.1.le, hopt.2.le⟩

theorem suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active
    {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiMangoldtBlockMargin q r = suzukiGlobalDualMargin q := by
  unfold suzukiMangoldtBlockMargin suzukiGlobalDualMargin
  rw [suzukiMangoldtBlockDual_eq_archDual_of_active h]

/-- Loss from the left event value down to the unique block minimum. -/
noncomputable def suzukiMangoldtBlockDrawdown (q r : ℕ) : ℝ :=
  suzukiPsi (Real.log q) - suzukiMangoldtBlockMargin q r

theorem suzukiMangoldtBlockMargin_eq_psi_optimizer_of_active
    {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiMangoldtBlockMargin q r =
      suzukiPsi (suzukiArchDualOptimizer (suzukiMangoldtSlope q)) := by
  have hopt := IsActiveMangoldtBlock.optimizer_mem_Ioo h
  rw [suzukiMangoldtBlockMargin_eq_globalDualMargin_of_active h]
  unfold suzukiGlobalDualMargin
  rw [suzukiArchDual_eq_optimizer]
  rw [suzukiPsi_eq_mangoldtBlock h.1 hopt.1.le hopt.2.le]
  ring

/-- On an active block the drawdown is the integral of the positive slope
deficit up to the optimizer. -/
theorem suzukiMangoldtBlockDrawdown_eq_integral
    {q r : ℕ} (h : IsActiveMangoldtBlock q r) :
    suzukiMangoldtBlockDrawdown q r =
      ∫ t in Real.log q..
          suzukiArchDualOptimizer (suzukiMangoldtSlope q),
        (suzukiMangoldtSlope q - deriv suzukiPsiArchimedean t) := by
  have hopt := IsActiveMangoldtBlock.optimizer_mem_Ioo h
  have hqpos : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast h.1.left_event.two_le)
  have hcont : ContinuousOn
      (suzukiArchCellObjective (suzukiMangoldtSlope q))
      (Icc (Real.log q) (suzukiArchDualOptimizer (suzukiMangoldtSlope q))) :=
    continuousOn_suzukiArchCellObjective_Icc hqpos
  have hint : IntervalIntegrable
      (fun t => suzukiMangoldtSlope q - deriv suzukiPsiArchimedean t)
      MeasureTheory.volume (Real.log q)
        (suzukiArchDualOptimizer (suzukiMangoldtSlope q)) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hopt.1.le] at ht
    exact (continuousAt_const.sub
      (hasDerivAt_deriv_suzukiPsiArchimedean
        (hqpos.trans_le ht.1)).continuousAt).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hopt.1.le hcont
    (fun t ht => hasDerivAt_suzukiArchCellObjective _
      (hqpos.trans ht.1)) hint
  unfold suzukiMangoldtBlockDrawdown
  rw [suzukiMangoldtBlockMargin_eq_psi_optimizer_of_active h,
    suzukiPsi_eq_mangoldtBlock h.1 le_rfl
      (le_trans hopt.1.le hopt.2.le),
    suzukiPsi_eq_mangoldtBlock h.1 hopt.1.le hopt.2.le]
  unfold suzukiArchCellObjective at hFTC
  linarith

theorem suzukiMangoldtBlockDrawdown_integrand_nonneg
    {q r : ℕ} (h : IsActiveMangoldtBlock q r)
    {t : ℝ} (ht : t ∈ Icc (Real.log q)
      (suzukiArchDualOptimizer (suzukiMangoldtSlope q))) :
    0 ≤ suzukiMangoldtSlope q - deriv suzukiPsiArchimedean t := by
  have hopt := IsActiveMangoldtBlock.optimizer_mem_Ioo h
  have hslope := deriv_archimedean_at_dualOptimizer_of_lt
    ((Real.log_le_log (by norm_num)
      (by exact_mod_cast h.1.left_event.two_le)).trans_lt hopt.1)
  have hmono := deriv_suzukiPsiArchimedean_strictMonoOn.monotoneOn
    ((Real.log_le_log (by norm_num)
      (by exact_mod_cast h.1.left_event.two_le)).trans ht.1)
    (suzukiArchDualOptimizer_mem_Ici _) ht.2
  linarith

/-! ## Inactive endpoint geometry -/

theorem isMinOn_left_of_mangoldtSlope_le_archDeriv
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hs : suzukiMangoldtSlope q ≤
      deriv suzukiPsiArchimedean (Real.log q)) :
    IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) (Real.log q) := by
  intro t ht
  change suzukiPsi (Real.log q) ≤ suzukiPsi t
  rw [suzukiPsi_eq_mangoldtBlock h le_rfl
      (Real.log_le_log (by exact_mod_cast h.left_pos)
        (by exact_mod_cast h.left_lt.le)),
    suzukiPsi_eq_mangoldtBlock h ht.1 ht.2]
  have hq2real : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast h.left_event.two_le
  have hlog2q : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq2real
  have hA := suzukiArchimedean_strong_tangent_lower
    hlog2q (le_trans hlog2q ht.1)
  have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs)
    (sub_nonneg.mpr ht.1)
  ring_nf at hA hprod ⊢
  nlinarith [sq_nonneg (t - Real.log q)]

theorem isMinOn_right_of_archDeriv_le_mangoldtSlope
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hs : deriv suzukiPsiArchimedean (Real.log r) ≤
      suzukiMangoldtSlope q) :
    IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) (Real.log r) := by
  intro t ht
  change suzukiPsi (Real.log r) ≤ suzukiPsi t
  rw [suzukiPsi_eq_mangoldtBlock h
      (Real.log_le_log (by exact_mod_cast h.left_pos)
        (by exact_mod_cast h.left_lt.le)) le_rfl,
    suzukiPsi_eq_mangoldtBlock h ht.1 ht.2]
  have hq2real : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast h.left_event.two_le
  have hlog2q : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq2real
  have hqrreal : (q : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast h.left_lt.le
  have hlogqr : Real.log q ≤ Real.log r :=
    Real.log_le_log (by exact_mod_cast h.left_pos) hqrreal
  have hA := suzukiArchimedean_strong_tangent_lower
    (le_trans hlog2q hlogqr) (le_trans hlog2q ht.1)
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs)
    (sub_nonpos.mpr ht.2)
  ring_nf at hA hprod ⊢
  nlinarith [sq_nonneg (t - Real.log r)]

/-- A Mangoldt impulse makes the slope deficit jump downward by exactly its
event weight. -/
theorem suzukiSlopeDeficit_event_jump
    {q : ℕ} (hq : 1 ≤ q) :
    deriv suzukiPsiArchimedean (Real.log q) - suzukiMangoldtSlope q =
      (deriv suzukiPsiArchimedean (Real.log q) -
        suzukiMangoldtSlope (q - 1)) - suzukiMangoldtEventWeight q := by
  have hsucc := suzukiMangoldtSlope_succ (q - 1)
  rw [Nat.sub_add_cancel hq] at hsucc
  have hcast : (((q - 1 : ℕ) : ℝ) + 1) = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hq
  rw [hcast] at hsucc
  rw [hsucc]
  unfold suzukiMangoldtEventWeight
  ring

end RHGarden
