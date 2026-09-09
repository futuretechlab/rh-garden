import RHGarden.SuzukiCellTwo
import Mathlib.Topology.Order.Compact

noncomputable section

open Set
open scoped BigOperators

namespace RHGarden

/-! ## The two-number Mangoldt state -/

/-- The accumulated coefficient of `t` in Suzuki's finite prime term. -/
noncomputable def suzukiMangoldtSlope (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k

/-- The accumulated constant term in Suzuki's finite prime term. -/
noncomputable def suzukiMangoldtIntercept (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    ArithmeticFunction.vonMangoldt k * Real.log k / Real.sqrt k

/-- The complete arithmetic state controlling Suzuki's function on the
`n`th prime cell. -/
noncomputable def suzukiArithmeticState (n : ℕ) : ℝ × ℝ :=
  (suzukiMangoldtSlope n, suzukiMangoldtIntercept n)

private theorem Icc_one_eq_Ioc_zero (n : ℕ) :
    Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem suzukiMangoldtSlope_nonneg (n : ℕ) :
    0 ≤ suzukiMangoldtSlope n := by
  unfold suzukiMangoldtSlope
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem suzukiMangoldtIntercept_nonneg (n : ℕ) :
    0 ≤ suzukiMangoldtIntercept n := by
  unfold suzukiMangoldtIntercept
  apply Finset.sum_nonneg
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  exact div_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast hk1)))
    (Real.sqrt_nonneg _)

theorem suzukiMangoldtSlope_eq_primeCellSlope (n : ℕ) :
    suzukiMangoldtSlope n = suzukiPrimeCellSlope n := by
  rw [suzukiMangoldtSlope, suzukiPrimeCellSlope, Icc_one_eq_Ioc_zero]

/-- On a half-open prime cell, all arithmetic information in Suzuki's
explicit formula is carried by the two scalars `(S_n,C_n)`. -/
theorem suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_cell
    {n : ℕ} {t : ℝ} (hn : 1 ≤ n)
    (ht0 : Real.log n ≤ t) (ht1 : t < Real.log (n + 1)) :
    suzukiPsi t = suzukiPsiArchimedean t -
      suzukiMangoldtSlope n * t + suzukiMangoldtIntercept n := by
  have ht0' : 0 ≤ t :=
    (Real.log_nonneg (by exact_mod_cast hn)).trans ht0
  have hsum :
      (∑ k ∈ Finset.Ioc 0 n,
          ArithmeticFunction.vonMangoldt k / Real.sqrt k *
            (t - Real.log k)) =
        suzukiMangoldtSlope n * t - suzukiMangoldtIntercept n := by
    rw [suzukiMangoldtSlope, suzukiMangoldtIntercept,
      Icc_one_eq_Ioc_zero]
    calc
      _ = ∑ k ∈ Finset.Ioc 0 n,
          ((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * t -
            ArithmeticFunction.vonMangoldt k * Real.log k /
              Real.sqrt k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (∑ k ∈ Finset.Ioc 0 n,
              ArithmeticFunction.vonMangoldt k / Real.sqrt k) * t -
            ∑ k ∈ Finset.Ioc 0 n,
              ArithmeticFunction.vonMangoldt k * Real.log k /
                Real.sqrt k := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [suzukiPsi_eq_primeSide, suzukiPsiPrimeSide, abs_of_nonneg ht0',
    suzukiPsiPrimeSideNonneg,
    suzukiPsiPrimeContribution_eq_fixed_sum_on_cell (Nat.zero_lt_of_lt hn)
      ⟨ht0, ht1⟩]
  rw [hsum]
  ring

/-- The derivative on a prime cell depends on the primes only through the
single accumulated slope `S_n`. -/
theorem deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_cell
    {n : ℕ} {t : ℝ} (hn : 1 ≤ n)
    (ht0 : Real.log n < t) (ht1 : t < Real.log (n + 1)) :
    deriv suzukiPsi t =
      deriv suzukiPsiArchimedean t - suzukiMangoldtSlope n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  rw [(hasDerivAt_suzukiPsi_on_primeCell hn0 ⟨ht0, ht1⟩).deriv,
    (hasDerivAt_suzukiPsiArchimedean_of_pos
      ((Real.log_nonneg (by exact_mod_cast hn)).trans_lt ht0)).deriv,
    suzukiMangoldtSlope_eq_primeCellSlope]

/-! ## Sparse updates -/

theorem suzukiMangoldtSlope_succ (n : ℕ) :
    suzukiMangoldtSlope (n + 1) = suzukiMangoldtSlope n +
      ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1) := by
  rw [suzukiMangoldtSlope, suzukiMangoldtSlope,
    show n + 1 = n.succ by omega, Finset.sum_Icc_succ_top]
  all_goals simp [Nat.succ_eq_add_one]

theorem suzukiMangoldtIntercept_succ (n : ℕ) :
    suzukiMangoldtIntercept (n + 1) = suzukiMangoldtIntercept n +
      ArithmeticFunction.vonMangoldt (n + 1) * Real.log (n + 1) /
        Real.sqrt (n + 1) := by
  rw [suzukiMangoldtIntercept, suzukiMangoldtIntercept,
    show n + 1 = n.succ by omega, Finset.sum_Icc_succ_top]
  all_goals simp [Nat.succ_eq_add_one]

theorem suzukiArithmeticState_succ (n : ℕ) :
    suzukiArithmeticState (n + 1) =
      (suzukiMangoldtSlope n +
          ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1),
        suzukiMangoldtIntercept n +
          ArithmeticFunction.vonMangoldt (n + 1) * Real.log (n + 1) /
            Real.sqrt (n + 1)) := by
  simp only [suzukiArithmeticState, suzukiMangoldtSlope_succ,
    suzukiMangoldtIntercept_succ]

theorem suzukiArithmeticState_succ_eq_of_vonMangoldt_eq_zero
    {n : ℕ} (h : ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    suzukiArithmeticState (n + 1) = suzukiArithmeticState n := by
  rw [suzukiArithmeticState_succ]
  simp [suzukiArithmeticState, h]

/-! ## Closed cells and the restricted archimedean dual -/

/-- The state formula remains valid at the right endpoint: the new
Mangoldt ramp entering there has length zero, so its slope and intercept
updates cancel exactly. -/
theorem suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
    {n : ℕ} {t : ℝ} (hn : 1 ≤ n)
    (ht0 : Real.log n ≤ t) (ht1 : t ≤ Real.log (n + 1)) :
    suzukiPsi t = suzukiPsiArchimedean t -
      suzukiMangoldtSlope n * t + suzukiMangoldtIntercept n := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · exact suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_cell hn ht0 ht1
  · have hnext : Real.log ((n + 1 : ℕ) : ℝ) <
        Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
      apply Real.log_lt_log
      · positivity
      · exact_mod_cast Nat.lt_succ_self (n + 1)
    have hformula :=
      suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_cell
        (n := n + 1) (t := Real.log ((n + 1 : ℕ) : ℝ))
        (by omega) le_rfl hnext
    norm_num only [Nat.cast_add, Nat.cast_one] at hformula
    rw [suzukiMangoldtSlope_succ, suzukiMangoldtIntercept_succ] at hformula
    calc
      suzukiPsi (Real.log (↑n + 1)) =
          suzukiPsiArchimedean (Real.log (↑n + 1)) -
            (suzukiMangoldtSlope n +
              ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1)) *
                Real.log (n + 1) +
            (suzukiMangoldtIntercept n +
              ArithmeticFunction.vonMangoldt (n + 1) * Real.log (n + 1) /
                Real.sqrt (n + 1)) := hformula
      _ = suzukiPsiArchimedean (Real.log (↑n + 1)) -
            suzukiMangoldtSlope n * Real.log (n + 1) +
              suzukiMangoldtIntercept n := by ring

/-- The affine function whose restricted maximum is the price paid by an
arithmetic slope on one prime cell. -/
noncomputable def suzukiArchCellObjective (s t : ℝ) : ℝ :=
  s * t - suzukiPsiArchimedean t

/-- The restricted convex dual of the archimedean term on the closed
`n`th prime cell. -/
noncomputable def suzukiArchCellDual (n : ℕ) (s : ℝ) : ℝ :=
  sSup (suzukiArchCellObjective s ''
    Icc (Real.log n) (Real.log (n + 1)))

private theorem continuousOn_suzukiArchCellObjective
    {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    ContinuousOn (suzukiArchCellObjective s)
      (Icc (Real.log n) (Real.log (n + 1))) := by
  intro t ht
  have htpos : 0 < t :=
    (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).trans_le ht.1
  exact ((continuousAt_const.mul continuousAt_id).sub
    (differentiableAt_suzukiPsiArchimedean_of_pos htpos).continuousAt).continuousWithinAt

/-- The restricted dual is an attained maximum. -/
theorem exists_suzukiArchCellDual_eq
    {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    ∃ t ∈ Icc (Real.log n) (Real.log (n + 1)),
      suzukiArchCellDual n s = suzukiArchCellObjective s t ∧
        IsMaxOn (suzukiArchCellObjective s)
          (Icc (Real.log n) (Real.log (n + 1))) t := by
  have hlog : Real.log n ≤ Real.log (n + 1) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hlog) (continuousOn_suzukiArchCellObjective hn s)
  refine ⟨t, ht, ?_, hmax⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨t, ht, rfl⟩, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  exact hmax hu

theorem le_suzukiArchCellDual
    {n : ℕ} (hn : 2 ≤ n) {s t : ℝ}
    (ht : t ∈ Icc (Real.log n) (Real.log (n + 1))) :
    suzukiArchCellObjective s t ≤ suzukiArchCellDual n s := by
  obtain ⟨u, hu, hdual, hmax⟩ := exists_suzukiArchCellDual_eq hn s
  rw [hdual]
  exact hmax ht

theorem suzukiArchCellDual_le
    {n : ℕ} (hn : 2 ≤ n) {s b : ℝ}
    (h : ∀ t ∈ Icc (Real.log n) (Real.log (n + 1)),
      suzukiArchCellObjective s t ≤ b) :
    suzukiArchCellDual n s ≤ b := by
  obtain ⟨t, ht, hdual, hmax⟩ := exists_suzukiArchCellDual_eq hn s
  rw [hdual]
  exact h t ht

/-- Positivity on one complete prime cell is exactly one scalar inequality
between the Mangoldt intercept and the restricted archimedean dual. -/
theorem suzukiPsi_nonnegative_on_cell_iff_intercept_ge_dual
    {n : ℕ} (hn : 2 ≤ n) :
    (∀ t, Real.log n ≤ t → t ≤ Real.log (n + 1) → 0 ≤ suzukiPsi t) ↔
      suzukiArchCellDual n (suzukiMangoldtSlope n) ≤
        suzukiMangoldtIntercept n := by
  constructor
  · intro h
    apply suzukiArchCellDual_le hn
    intro t ht
    have hpsi := h t ht.1 ht.2
    rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (le_trans (by norm_num) hn) ht.1 ht.2] at hpsi
    unfold suzukiArchCellObjective
    linarith
  · intro hdual t ht0 ht1
    have hobj := le_suzukiArchCellDual hn
      (s := suzukiMangoldtSlope n) ⟨ht0, ht1⟩
    rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (le_trans (by norm_num) hn) ht0 ht1]
    unfold suzukiArchCellObjective at hobj
    linarith

/-- The scalar safety margin of the `n`th Suzuki prime cell. -/
noncomputable def suzukiCellMargin (n : ℕ) : ℝ :=
  suzukiMangoldtIntercept n -
    suzukiArchCellDual n (suzukiMangoldtSlope n)

theorem suzukiCellMargin_nonneg_iff {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ suzukiCellMargin n ↔
      ∀ t, Real.log n ≤ t → t ≤ Real.log (n + 1) → 0 ≤ suzukiPsi t := by
  change 0 ≤ suzukiMangoldtIntercept n -
      suzukiArchCellDual n (suzukiMangoldtSlope n) ↔ _
  rw [sub_nonneg]
  exact (suzukiPsi_nonnegative_on_cell_iff_intercept_ge_dual hn).symm

theorem suzukiCellMargin_pos_iff {n : ℕ} (hn : 2 ≤ n) :
    0 < suzukiCellMargin n ↔
      ∀ t, Real.log n ≤ t → t ≤ Real.log (n + 1) → 0 < suzukiPsi t := by
  constructor
  · intro hmargin t ht0 ht1
    have hobj := le_suzukiArchCellDual hn
      (s := suzukiMangoldtSlope n) ⟨ht0, ht1⟩
    rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (le_trans (by norm_num) hn) ht0 ht1]
    unfold suzukiCellMargin at hmargin
    unfold suzukiArchCellObjective at hobj
    linarith
  · intro h
    obtain ⟨t, ht, hdual, hmax⟩ :=
      exists_suzukiArchCellDual_eq hn (suzukiMangoldtSlope n)
    have hpsi := h t ht.1 ht.2
    rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (le_trans (by norm_num) hn) ht.1 ht.2] at hpsi
    unfold suzukiCellMargin
    rw [hdual]
    unfold suzukiArchCellObjective
    linarith

/-- Regression: the previously certified second cell has strictly positive
scalar margin, without repeating its analytic certificate. -/
theorem suzukiCellMargin_two_pos : 0 < suzukiCellMargin 2 := by
  rw [suzukiCellMargin_pos_iff (by norm_num)]
  intro t ht2 ht3
  norm_num at ht3
  exact suzukiPsi_pos_cell_two t ht2 ht3

/-! ## The global discrete representation -/

/-- The still-open compact initial interval, separated from all later
prime cells. -/
def SuzukiInitialNonnegative : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ Real.log 2 → 0 ≤ suzukiPsi t

private theorem exists_primeCell_of_log_two_le
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    ∃ n : ℕ, 2 ≤ n ∧
      t ∈ Icc (Real.log n) (Real.log (n + 1)) := by
  let n : ℕ := ⌊Real.exp t⌋₊
  have hexp2 : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hn : 2 ≤ n := by
    dsimp [n]
    exact Nat.le_floor hexp2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hleft : Real.log n ≤ t := by
    rw [Real.log_le_iff_le_exp hnpos]
    exact Nat.floor_le (Real.exp_pos t).le
  have hright : t ≤ Real.log (n + 1) := by
    have he : Real.exp t < (n : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (Real.exp t)
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact (Real.le_log_iff_exp_le hp).mpr he.le
  exact ⟨n, hn, hleft, hright⟩

/-- Global Suzuki positivity is equivalent to the compact initial interval
plus the countable family of scalar cell-margin inequalities. -/
theorem suzukiPsiNonnegative_iff_initial_and_cellMargins :
    SuzukiPsiNonnegative ↔
      SuzukiInitialNonnegative ∧
        ∀ n : ℕ, 2 ≤ n → 0 ≤ suzukiCellMargin n := by
  constructor
  · intro h
    refine ⟨fun t ht0 ht2 => h t, ?_⟩
    intro n hn
    rw [suzukiCellMargin_nonneg_iff hn]
    intro t ht0 ht1
    exact h t
  · rintro ⟨hinitial, hmargins⟩ t
    have hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ suzukiPsi x := by
      intro x hx
      by_cases hx2 : x ≤ Real.log 2
      · exact hinitial x hx hx2
      · obtain ⟨n, hn, hcell⟩ :=
          exists_primeCell_of_log_two_le (le_of_not_ge hx2)
        have hmargin := (suzukiCellMargin_nonneg_iff hn).mp (hmargins n hn)
        exact hmargin x hcell.1 hcell.2
    by_cases ht : 0 ≤ t
    · exact hnonneg t ht
    · have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      rw [← suzukiPsi_neg t]
      exact hnonneg (-t) hneg

/-- RH written as an entirely discrete sequence of Mangoldt-state margin
inequalities, together with the compact initial interval.  This is an
equivalence only; no margin family is asserted here. -/
theorem riemannHypothesis_iff_initial_and_all_cellMargins :
    RiemannHypothesis ↔
      SuzukiInitialNonnegative ∧
        ∀ n : ℕ, 2 ≤ n → 0 ≤ suzukiCellMargin n := by
  rw [riemannHypothesis_iff_shifted_zero_nonnegative]
  simp only [suzukiPsiShifted_zero_parameter]
  exact suzukiPsiNonnegative_iff_initial_and_cellMargins

/-! ## Slope perturbations of the restricted dual -/

/-- Increasing a slope by `d ≥ 0` changes the restricted dual by between
`d log n` and `d log(n+1)`. -/
theorem suzukiArchCellDual_add_slope_bounds
    {n : ℕ} (hn : 2 ≤ n) {s d : ℝ} (hd : 0 ≤ d) :
    d * Real.log n ≤
        suzukiArchCellDual n (s + d) - suzukiArchCellDual n s ∧
      suzukiArchCellDual n (s + d) - suzukiArchCellDual n s ≤
        d * Real.log (n + 1) := by
  obtain ⟨x, hx, hxs, hxmax⟩ := exists_suzukiArchCellDual_eq hn s
  obtain ⟨y, hy, hysd, hymax⟩ := exists_suzukiArchCellDual_eq hn (s + d)
  have hx_at_sd := le_suzukiArchCellDual hn (s := s + d) hx
  have hy_at_s := le_suzukiArchCellDual hn (s := s) hy
  rw [hysd] at hx_at_sd
  rw [hxs] at hy_at_s
  rw [hysd, hxs]
  unfold suzukiArchCellObjective at hx_at_sd hy_at_s ⊢
  constructor
  · have hdx : d * Real.log n ≤ d * x :=
      mul_le_mul_of_nonneg_left hx.1 hd
    linarith
  · have hdy : d * y ≤ d * Real.log (n + 1) :=
      mul_le_mul_of_nonneg_left hy.2 hd
    linarith

/-- A Mangoldt event's intercept gain dominates its same-cell dual cost.
This deliberately does not compare the moving cells `n` and `n+1`. -/
theorem mangoldt_event_intercept_gain_ge_same_cell_dual_cost
    {n : ℕ} (hn : 2 ≤ n) :
    let d := ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1)
    suzukiArchCellDual n (suzukiMangoldtSlope n + d) -
        suzukiArchCellDual n (suzukiMangoldtSlope n) ≤
      d * Real.log (n + 1) := by
  dsimp only
  exact (suzukiArchCellDual_add_slope_bounds hn
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_nonneg _))).2

/-! ## Strict concavity and transition bookkeeping -/

private theorem hasDerivAt_suzukiArchCellObjective
    (s : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (suzukiArchCellObjective s)
      (s - deriv suzukiPsiArchimedean t) t := by
  have h := ((hasDerivAt_id t).const_mul s).sub
    (differentiableAt_suzukiPsiArchimedean_of_pos ht).hasDerivAt
  have heq : suzukiArchCellObjective s =ᶠ[nhds t]
      ((fun y : ℝ => s * id y) - suzukiPsiArchimedean) := by
    filter_upwards [] with x
    rfl
  have h' := h.congr_of_eventuallyEq heq
  simpa only [mul_one] using h'

private theorem secondDeriv_suzukiArchCellObjective
    (s : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (suzukiArchCellObjective s)) t =
      -deriv (deriv suzukiPsiArchimedean) t := by
  have hbase := (hasDerivAt_deriv_suzukiPsiArchimedean ht).const_sub s
  have hderiv : HasDerivAt (deriv (suzukiArchCellObjective s))
      (-suzukiPsiCurvature t) t := by
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact (hasDerivAt_suzukiArchCellObjective s hx).deriv
  rw [hderiv.deriv, secondDeriv_suzukiPsiArchimedean ht]

/-- The restricted dual objective is strictly concave, hence its maximizer
classification (left endpoint, interior, right endpoint) is unambiguous. -/
theorem strictConcaveOn_suzukiArchCellObjective
    {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    StrictConcaveOn ℝ (Icc (Real.log n) (Real.log (n + 1)))
      (suzukiArchCellObjective s) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    (continuousOn_suzukiArchCellObjective hn s)
  intro t ht
  rw [interior_Icc] at ht
  have htpos : 0 < t :=
    (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).trans ht.1
  change deriv (deriv (suzukiArchCellObjective s)) t < 0
  rw [secondDeriv_suzukiArchCellObjective s htpos]
  have hcurv := one_le_secondDeriv_suzukiPsi_on_primeCell hn ht
  rw [secondDeriv_suzukiPsi_eq_archimedean_on_cell
    (lt_of_lt_of_le (by norm_num) hn) ht] at hcurv
  linarith

/-- The maximizing point defining `D_n(s)` is unique. -/
theorem unique_suzukiArchCellDual_maximizer
    {n : ℕ} (hn : 2 ≤ n) {s x y : ℝ}
    (hx : x ∈ Icc (Real.log n) (Real.log (n + 1)))
    (hy : y ∈ Icc (Real.log n) (Real.log (n + 1)))
    (hxmax : IsMaxOn (suzukiArchCellObjective s)
      (Icc (Real.log n) (Real.log (n + 1))) x)
    (hymax : IsMaxOn (suzukiArchCellObjective s)
      (Icc (Real.log n) (Real.log (n + 1))) y) :
    x = y :=
  (strictConcaveOn_suzukiArchCellObjective hn s).eq_of_isMaxOn
    hxmax hymax hx hy

/-- An interior dual maximizer is exactly the unique point where the
archimedean derivative equals the requested slope. -/
theorem deriv_suzukiPsiArchimedean_eq_slope_of_dual_maximizer
    {n : ℕ} (hn : 2 ≤ n) {s t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1)))
    (hmax : IsMaxOn (suzukiArchCellObjective s)
      (Icc (Real.log n) (Real.log (n + 1))) t) :
    deriv suzukiPsiArchimedean t = s := by
  have hnhds : Icc (Real.log n) (Real.log (n + 1)) ∈ nhds t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (Ioo_subset_Icc_self)
  have hzero := (hmax.isLocalMax hnhds).deriv_eq_zero
  have htpos : 0 < t :=
    (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).trans ht.1
  rw [(hasDerivAt_suzukiArchCellObjective s htpos).deriv] at hzero
  linarith

/-- After applying a Mangoldt update but before moving the cell interval,
the scalar margin cannot decrease. -/
theorem same_cell_margin_nondec_of_mangoldt_event
    {n : ℕ} (hn : 2 ≤ n) :
    suzukiMangoldtIntercept (n + 1) -
        suzukiArchCellDual n (suzukiMangoldtSlope (n + 1)) ≥
      suzukiMangoldtIntercept n -
        suzukiArchCellDual n (suzukiMangoldtSlope n) := by
  let d := ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1)
  have hdual := mangoldt_event_intercept_gain_ge_same_cell_dual_cost hn
  rw [suzukiMangoldtSlope_succ, suzukiMangoldtIntercept_succ]
  dsimp [d] at hdual ⊢
  have hintercept :
      ArithmeticFunction.vonMangoldt (n + 1) * Real.log (n + 1) /
          Real.sqrt (n + 1) =
        (ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1)) *
          Real.log (n + 1) := by ring
  rw [hintercept]
  linarith

/-- If there is no Mangoldt event at the next boundary, the entire margin
change is caused by moving the restricted dual to the adjacent interval. -/
theorem suzukiCellMargin_succ_of_vonMangoldt_eq_zero
    {n : ℕ} (h : ArithmeticFunction.vonMangoldt (n + 1) = 0) :
    suzukiCellMargin (n + 1) =
      suzukiMangoldtIntercept n -
        suzukiArchCellDual (n + 1) (suzukiMangoldtSlope n) := by
  unfold suzukiCellMargin
  rw [suzukiMangoldtSlope_succ, suzukiMangoldtIntercept_succ]
  simp [h]

/-! ## Small-state regressions -/

theorem suzukiMangoldtSlope_three :
    suzukiMangoldtSlope 3 =
      Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3 := by
  unfold suzukiMangoldtSlope
  have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hIcc]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]

theorem suzukiMangoldtIntercept_three :
    suzukiMangoldtIntercept 3 =
      (Real.log 2) ^ 2 / Real.sqrt 2 +
        (Real.log 3) ^ 2 / Real.sqrt 3 := by
  unfold suzukiMangoldtIntercept
  have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hIcc]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  ring

end RHGarden
