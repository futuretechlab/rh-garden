import RHGarden.SuzukiMangoldtState

noncomputable section

open Set
open scoped BigOperators

namespace RHGarden

/-! ## Mangoldt events and constant-state blocks -/

/-- An integer at which the Mangoldt state receives a nonzero update. -/
def IsMangoldtEvent (n : ℕ) : Prop :=
  ArithmeticFunction.vonMangoldt n ≠ 0

theorem isMangoldtEvent_iff_primePower {n : ℕ} :
    IsMangoldtEvent n ↔ Nat.IsPrimePow n := by
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff

theorem isMangoldtEvent_iff_pos {n : ℕ} :
    IsMangoldtEvent n ↔ 0 < ArithmeticFunction.vonMangoldt n := by
  rw [IsMangoldtEvent, ArithmeticFunction.vonMangoldt_pos_iff,
    ArithmeticFunction.vonMangoldt_ne_zero_iff]

theorem IsMangoldtEvent.two_le {n : ℕ} (h : IsMangoldtEvent n) : 2 ≤ n := by
  exact (isMangoldtEvent_iff_primePower.mp h).two_le

/-- Consecutive nonzero Mangoldt events.  The arithmetic state is constant
from `q` through `r - 1`; at `r` it receives its next sparse update. -/
def IsMangoldtBlock (q r : ℕ) : Prop :=
  q < r ∧ IsMangoldtEvent q ∧ IsMangoldtEvent r ∧
    ∀ k : ℕ, q < k → k < r → ArithmeticFunction.vonMangoldt k = 0

theorem IsMangoldtBlock.left_lt {q r : ℕ} (h : IsMangoldtBlock q r) : q < r := h.1
theorem IsMangoldtBlock.left_event {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsMangoldtEvent q := h.2.1
theorem IsMangoldtBlock.right_event {q r : ℕ} (h : IsMangoldtBlock q r) :
    IsMangoldtEvent r := h.2.2.1
theorem IsMangoldtBlock.eq_zero_between {q r k : ℕ} (h : IsMangoldtBlock q r)
    (hqk : q < k) (hkr : k < r) :
    ArithmeticFunction.vonMangoldt k = 0 := h.2.2.2 k hqk hkr

/-- The complete two-number state is constant between consecutive Mangoldt
events. -/
theorem suzukiArithmeticState_eq_on_mangoldtBlock
    {q r n : ℕ} (h : IsMangoldtBlock q r) (hqn : q ≤ n) (hnr : n < r) :
    suzukiArithmeticState n = suzukiArithmeticState q := by
  induction n, hqn using Nat.le_induction with
  | base => rfl
  | succ n hqn ih =>
      have hnr' : n < r := lt_of_succ_lt hnr
      rw [suzukiArithmeticState_succ_eq_of_vonMangoldt_eq_zero
        (h.eq_zero_between (lt_succ_iff.mpr hqn) hnr)]
      exact ih hnr'

theorem mangoldtSlope_eq_on_block
    {q r n : ℕ} (h : IsMangoldtBlock q r) (hqn : q ≤ n) (hnr : n < r) :
    suzukiMangoldtSlope n = suzukiMangoldtSlope q := by
  have hs := congrArg Prod.fst
    (suzukiArithmeticState_eq_on_mangoldtBlock h hqn hnr)
  simpa [suzukiArithmeticState] using hs

theorem mangoldtIntercept_eq_on_block
    {q r n : ℕ} (h : IsMangoldtBlock q r) (hqn : q ≤ n) (hnr : n < r) :
    suzukiMangoldtIntercept n = suzukiMangoldtIntercept q := by
  have hs := congrArg Prod.snd
    (suzukiArithmeticState_eq_on_mangoldtBlock h hqn hnr)
  simpa [suzukiArithmeticState] using hs

private theorem exists_primeCell_in_mangoldtBlock
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (htq : Real.log q ≤ t) (htr : t ≤ Real.log r) :
    ∃ n : ℕ, q ≤ n ∧ n < r ∧
      t ∈ Icc (Real.log n) (Real.log (n + 1)) := by
  by_cases hte : t = Real.log r
  · subst t
    refine ⟨r - 1, ?_, Nat.sub_lt (Nat.zero_lt_of_lt h.left_lt) (by omega), ?_, ?_⟩
    · omega
    · exact Real.log_le_log (by exact_mod_cast h.left_event.two_le)
        (by exact_mod_cast (Nat.sub_le r 1))
    · convert le_rfl using 2 <;> omega
  · have htr' : t < Real.log r := lt_of_le_of_ne htr hte
    let n : ℕ := ⌊Real.exp t⌋₊
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h.left_event.two_le)
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h.right_event.two_le)
    have hqexp : (q : ℝ) ≤ Real.exp t := by
      rw [← Real.exp_log hqpos]
      exact Real.exp_le_exp.mpr htq
    have hnq : q ≤ n := by
      dsimp [n]
      exact Nat.le_floor hqexp
    have hexpr : Real.exp t < r := by
      rw [← Real.exp_log hrpos]
      exact Real.exp_lt_exp.mpr htr'
    have hnr : n < r := by
      by_contra hn
      have hcast : (r : ℝ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
      have hnexp : (n : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
      linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hnq)
    have hleft : Real.log n ≤ t := by
      rw [Real.log_le_iff_le_exp hnpos]
      exact Nat.floor_le (Real.exp_pos t).le
    have hright : t ≤ Real.log (n + 1) := by
      have he : Real.exp t < (n : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one (Real.exp t)
      exact (Real.le_log_iff_exp_le (by positivity)).mpr he.le
    exact ⟨n, hnq, hnr, hleft, hright⟩

/-- A consecutive Mangoldt block has one closed formula, including its right
endpoint where the newly arriving ramp has value zero. -/
theorem suzukiPsi_eq_mangoldtBlock
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (htq : Real.log q ≤ t) (htr : t ≤ Real.log r) :
    suzukiPsi t = suzukiPsiArchimedean t -
      suzukiMangoldtSlope q * t + suzukiMangoldtIntercept q := by
  obtain ⟨n, hqn, hnr, ht⟩ := exists_primeCell_in_mangoldtBlock h htq htr
  rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
    (le_trans h.left_event.two_le hqn) ht.1 ht.2,
    mangoldtSlope_eq_on_block h hqn hnr,
    mangoldtIntercept_eq_on_block h hqn hnr]

/-! ## Interval duals and block margins -/

/-- The archimedean convex dual restricted to an arbitrary closed interval. -/
noncomputable def suzukiArchIntervalDual (a b s : ℝ) : ℝ :=
  sSup (suzukiArchCellObjective s '' Icc a b)

theorem continuousOn_suzukiArchCellObjective_Icc
    {a b s : ℝ} (ha : 0 < a) :
    ContinuousOn (suzukiArchCellObjective s) (Icc a b) := by
  intro t ht
  exact ((continuousAt_const.mul continuousAt_id).sub
    (differentiableAt_suzukiPsiArchimedean_of_pos
      (ha.trans_le ht.1)).continuousAt).continuousWithinAt

theorem exists_suzukiArchIntervalDual_eq
    {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ t ∈ Icc a b,
      suzukiArchIntervalDual a b s = suzukiArchCellObjective s t ∧
        IsMaxOn (suzukiArchCellObjective s) (Icc a b) t := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) (continuousOn_suzukiArchCellObjective_Icc ha)
  refine ⟨t, ht, ?_, hmax⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨t, ht, rfl⟩, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  exact hmax hu

theorem le_suzukiArchIntervalDual
    {a b s t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : t ∈ Icc a b) :
    suzukiArchCellObjective s t ≤ suzukiArchIntervalDual a b s := by
  obtain ⟨u, hu, hdual, hmax⟩ := exists_suzukiArchIntervalDual_eq ha hab
  rw [hdual]
  exact hmax ht

theorem suzukiArchIntervalDual_le
    {a b s c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, suzukiArchCellObjective s t ≤ c) :
    suzukiArchIntervalDual a b s ≤ c := by
  obtain ⟨t, ht, hdual, hmax⟩ := exists_suzukiArchIntervalDual_eq ha hab
  rw [hdual]
  exact h t ht

/-- The restricted archimedean dual for a consecutive Mangoldt block. -/
noncomputable def suzukiMangoldtBlockDual (q r : ℕ) (s : ℝ) : ℝ :=
  suzukiArchIntervalDual (Real.log q) (Real.log r) s

/-- The minimum safety margin across a complete constant-state block. -/
noncomputable def suzukiMangoldtBlockMargin (q r : ℕ) : ℝ :=
  suzukiMangoldtIntercept q -
    suzukiMangoldtBlockDual q r (suzukiMangoldtSlope q)

theorem mangoldtBlockMargin_nonneg_iff
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    0 ≤ suzukiMangoldtBlockMargin q r ↔
      ∀ t, Real.log q ≤ t → t ≤ Real.log r → 0 ≤ suzukiPsi t := by
  have hqlog : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by positivity) (by exact_mod_cast h.left_lt.le)
  constructor
  · intro hm t htq htr
    have hobj := le_suzukiArchIntervalDual hqlog hlog
      (s := suzukiMangoldtSlope q) ⟨htq, htr⟩
    rw [suzukiPsi_eq_mangoldtBlock h htq htr]
    unfold suzukiMangoldtBlockMargin suzukiMangoldtBlockDual at hm
    unfold suzukiArchCellObjective at hobj
    linarith
  · intro hpsi
    unfold suzukiMangoldtBlockMargin suzukiMangoldtBlockDual
    rw [sub_nonneg]
    apply suzukiArchIntervalDual_le hqlog hlog
    intro t ht
    have hp := hpsi t ht.1 ht.2
    rw [suzukiPsi_eq_mangoldtBlock h ht.1 ht.2] at hp
    unfold suzukiArchCellObjective
    linarith

theorem mangoldtBlockMargin_eq_minimum
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    ∃ t ∈ Icc (Real.log q) (Real.log r),
      suzukiMangoldtBlockMargin q r = suzukiPsi t ∧
        IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) t := by
  have hqlog : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by positivity) (by exact_mod_cast h.left_lt.le)
  obtain ⟨t, ht, hdual, hmax⟩ := exists_suzukiArchIntervalDual_eq
    (s := suzukiMangoldtSlope q) hqlog hlog
  refine ⟨t, ht, ?_, ?_⟩
  · rw [suzukiPsi_eq_mangoldtBlock h ht.1 ht.2]
    unfold suzukiMangoldtBlockMargin suzukiMangoldtBlockDual
    rw [hdual]
    unfold suzukiArchCellObjective
    ring
  · intro u hu
    have hm := hmax hu
    rw [suzukiPsi_eq_mangoldtBlock h ht.1 ht.2,
      suzukiPsi_eq_mangoldtBlock h hu.1 hu.2]
    unfold suzukiArchCellObjective at hm
    linarith

/-! ## Strict convexity and the unique block minimum -/

theorem strictConcaveOn_suzukiArchCellObjective_Icc
    {a b s : ℝ} (ha : Real.log 2 ≤ a) (hab : a ≤ b) :
    StrictConcaveOn ℝ (Icc a b) (suzukiArchCellObjective s) := by
  have ha0 : 0 < a := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ha
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    (continuousOn_suzukiArchCellObjective_Icc ha0)
  intro t ht
  rw [interior_Icc] at ht
  change deriv (deriv (suzukiArchCellObjective s)) t < 0
  rw [secondDeriv_suzukiArchCellObjective s (ha0.trans ht.1)]
  have hc := one_le_secondDeriv_suzukiPsiArchimedean_of_log_two_le
    (ha.trans ht.1.le)
  linarith

theorem strictConvexOn_suzukiPsi_mangoldtBlock
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    StrictConvexOn ℝ (Icc (Real.log q) (Real.log r)) suzukiPsi := by
  have hconc := strictConcaveOn_suzukiArchCellObjective_Icc
    (s := suzukiMangoldtSlope q)
    (Real.log_le_log (by norm_num) (by exact_mod_cast h.left_event.two_le))
    (Real.log_le_log (by positivity) (by exact_mod_cast h.left_lt.le))
  have hconv : StrictConvexOn ℝ (Icc (Real.log q) (Real.log r))
      (fun t => -suzukiArchCellObjective (suzukiMangoldtSlope q) t +
        suzukiMangoldtIntercept q) := by
    exact hconc.neg.add_affine (AffineMap.const ℝ ℝ (suzukiMangoldtIntercept q))
  apply hconv.congr
  intro t ht
  rw [suzukiPsi_eq_mangoldtBlock h ht.1 ht.2]
  unfold suzukiArchCellObjective
  ring

/-- Throughout the open block, the first derivative is the archimedean
derivative minus the one constant state slope. -/
theorem deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_mangoldtBlock
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (ht : t ∈ Ioo (Real.log q) (Real.log r)) :
    deriv suzukiPsi t =
      deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q := by
  let F : ℝ → ℝ := fun x => suzukiPsiArchimedean x -
    suzukiMangoldtSlope q * x + suzukiMangoldtIntercept q
  have heq : suzukiPsi =ᶠ[nhds t] F := by
    filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with x hxq hxr
    exact suzukiPsi_eq_mangoldtBlock h hxq.le hxr.le
  have htpos : 0 < t := (Real.log_pos (by
    exact_mod_cast h.left_event.two_le)).trans ht.1
  have hF : HasDerivAt F
      (deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q) t := by
    dsimp [F]
    convert ((differentiableAt_suzukiPsiArchimedean_of_pos htpos).hasDerivAt.sub
      (((hasDerivAt_id t).const_mul (suzukiMangoldtSlope q)).const_add
        (suzukiMangoldtIntercept q))) using 1 <;> ring
  rw [heq.deriv_eq, hF.deriv]

/-- The slope deficit `A'(t)-S_q` is strictly increasing across the entire
constant-state block.  Hence it crosses zero at most once. -/
theorem strictMonoOn_archDeriv_sub_mangoldtSlope_block
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    StrictMonoOn
      (fun t => deriv suzukiPsiArchimedean t - suzukiMangoldtSlope q)
      (Icc (Real.log q) (Real.log r)) := by
  have hq2 := h.left_event.two_le
  have hlog2q : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
  have hcont : ContinuousOn (deriv suzukiPsiArchimedean)
      (Icc (Real.log q) (Real.log r)) := by
    intro t ht
    have htpos : 0 < t := (Real.log_pos (by
      exact_mod_cast hq2)).trans_le ht.1
    exact (hasDerivAt_deriv_suzukiPsiArchimedean htpos).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (deriv suzukiPsiArchimedean)
      (Icc (Real.log q) (Real.log r)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro t ht
    rw [interior_Icc] at ht
    exact lt_of_lt_of_le zero_lt_one
      (one_le_secondDeriv_suzukiPsiArchimedean_of_log_two_le
        (hlog2q.trans ht.1.le))
  intro x hx y hy hxy
  have := hmono hx hy hxy
  linarith

/-- Zero-event block geometry is unimodal: the derivative of `Psi` is
strictly increasing across the whole open block, so `Psi` decreases before
its (possible) slope crossing and increases afterward. -/
theorem mangoldtBlock_margin_unimodal_geometry
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    StrictMonoOn (deriv suzukiPsi)
      (Ioo (Real.log q) (Real.log r)) := by
  intro x hx y hy hxy
  rw [deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_mangoldtBlock h hx,
    deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_mangoldtBlock h hy]
  exact strictMonoOn_archDeriv_sub_mangoldtSlope_block h
    ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy

theorem exists_unique_suzukiPsi_mangoldtBlock_minimizer
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    ∃ t ∈ Icc (Real.log q) (Real.log r),
      IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) t ∧
        ∀ u ∈ Icc (Real.log q) (Real.log r),
          IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) u → u = t := by
  obtain ⟨t, ht, hmargin, hmin⟩ := mangoldtBlockMargin_eq_minimum h
  refine ⟨t, ht, hmin, ?_⟩
  intro u hu humin
  exact (strictConvexOn_suzukiPsi_mangoldtBlock h).eq_of_isMinOn
    humin hmin hu ht

/-- An interior block minimizer is the unique solution of the state-slope
equation `A'(t)=S_q`.  Endpoint minimizers are the two remaining cases. -/
theorem deriv_suzukiPsiArchimedean_eq_mangoldtSlope_of_block_minimizer
    {q r : ℕ} (h : IsMangoldtBlock q r) {t : ℝ}
    (ht : t ∈ Ioo (Real.log q) (Real.log r))
    (hmin : IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) t) :
    deriv suzukiPsiArchimedean t = suzukiMangoldtSlope q := by
  have hnhds : Icc (Real.log q) (Real.log r) ∈ nhds t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
  have hzero := (hmin.isLocalMin hnhds).deriv_eq_zero
  rw [deriv_suzukiPsi_eq_arch_deriv_sub_slope_on_mangoldtBlock h ht] at hzero
  linarith

/-- The unique block minimizer has exactly one of the three Explorer
classifications: left endpoint, the unique interior slope solution, or
right endpoint. -/
theorem exists_unique_mangoldtBlock_minimizer_classification
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    ∃ t ∈ Icc (Real.log q) (Real.log r),
      IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) t ∧
      ((t = Real.log q) ∨
        (t ∈ Ioo (Real.log q) (Real.log r) ∧
          deriv suzukiPsiArchimedean t = suzukiMangoldtSlope q) ∨
        (t = Real.log r)) ∧
      ∀ u ∈ Icc (Real.log q) (Real.log r),
        IsMinOn suzukiPsi (Icc (Real.log q) (Real.log r)) u → u = t := by
  obtain ⟨t, ht, hmin, hunique⟩ :=
    exists_unique_suzukiPsi_mangoldtBlock_minimizer h
  refine ⟨t, ht, hmin, ?_, hunique⟩
  rcases ht.1.eq_or_lt with hleft | hleft
  · exact Or.inl hleft.symm
  · rcases ht.2.eq_or_lt with hright | hright
    · exact Or.inr (Or.inr hright)
    · exact Or.inr (Or.inl ⟨⟨hleft, hright⟩,
        deriv_suzukiPsiArchimedean_eq_mangoldtSlope_of_block_minimizer
          h ⟨hleft, hright⟩ hmin⟩)

/-! ## Collapse of constituent integer-cell margins -/

private theorem blockMargin_le_cellMargin
    {q r n : ℕ} (h : IsMangoldtBlock q r) (hqn : q ≤ n) (hnr : n < r) :
    suzukiMangoldtBlockMargin q r ≤ suzukiCellMargin n := by
  have hqlog : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by positivity) (by exact_mod_cast h.left_lt.le)
  have hn2 : 2 ≤ n := h.left_event.two_le.trans hqn
  obtain ⟨t, ht, hdual, hmax⟩ :=
    exists_suzukiArchCellDual_eq hn2 (suzukiMangoldtSlope n)
  have htblock : t ∈ Icc (Real.log q) (Real.log r) := by
    constructor
    · exact (Real.log_le_log (by positivity) (by exact_mod_cast hqn)).trans ht.1
    · exact ht.2.trans (Real.log_le_log (by positivity) (by exact_mod_cast (show n + 1 ≤ r by omega)))
  have hobj := le_suzukiArchIntervalDual hqlog hlog
    (s := suzukiMangoldtSlope q) htblock
  rw [mangoldtSlope_eq_on_block h hqn hnr,
    mangoldtIntercept_eq_on_block h hqn hnr]
  unfold suzukiMangoldtBlockMargin suzukiMangoldtBlockDual suzukiCellMargin
  rw [hdual]
  exact sub_le_sub_left hobj _

theorem exists_cellMargin_eq_mangoldtBlockMargin
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    ∃ n ∈ Finset.Ico q r,
      suzukiCellMargin n = suzukiMangoldtBlockMargin q r := by
  obtain ⟨t, ht, hmargin, hmin⟩ := mangoldtBlockMargin_eq_minimum h
  obtain ⟨n, hqn, hnr, htcell⟩ :=
    exists_primeCell_in_mangoldtBlock h ht.1 ht.2
  have hn2 : 2 ≤ n := h.left_event.two_le.trans hqn
  refine ⟨n, Finset.mem_Ico.mpr ⟨hqn, hnr⟩, le_antisymm ?_ ?_⟩
  · obtain ⟨u, hu, hdual, hmax⟩ :=
      exists_suzukiArchCellDual_eq hn2 (suzukiMangoldtSlope n)
    have hcellmin : suzukiCellMargin n = suzukiPsi u := by
      rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
        (le_trans (by norm_num) hn2) hu.1 hu.2]
      unfold suzukiCellMargin
      rw [hdual]
      unfold suzukiArchCellObjective
      ring
    have htu : suzukiArchCellObjective (suzukiMangoldtSlope n) t ≤
        suzukiArchCellObjective (suzukiMangoldtSlope n) u := hmax htcell
    rw [hcellmin, ← hmargin]
    rw [suzukiPsi_eq_arch_sub_slope_mul_add_intercept_on_closed_cell
      (le_trans (by norm_num) hn2) htcell.1 htcell.2]
    unfold suzukiArchCellObjective at htu
    linarith
  · exact blockMargin_le_cellMargin h hqn hnr

/-- A block margin is exactly the finite minimum of all integer-cell margins
carrying its constant arithmetic state. -/
theorem mangoldtBlockMargin_eq_finset_min_cellMargins
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiMangoldtBlockMargin q r =
      ((Finset.Ico q r).image suzukiCellMargin).min'
        ((Finset.image_nonempty).mpr ⟨q, Finset.mem_Ico.mpr ⟨le_rfl, h.left_lt⟩⟩) := by
  let F := (Finset.Ico q r).image suzukiCellMargin
  have hF : F.Nonempty :=
    (Finset.image_nonempty).mpr ⟨q, Finset.mem_Ico.mpr ⟨le_rfl, h.left_lt⟩⟩
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    exact blockMargin_le_cellMargin h (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2
  · obtain ⟨n, hn, heq⟩ := exists_cellMargin_eq_mangoldtBlockMargin h
    exact heq ▸ Finset.min'_le F _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)

/-! ## Sparse event updates -/

/-- The weight of one Mangoldt event in the two-number arithmetic state. -/
noncomputable def suzukiMangoldtEventWeight (q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q / Real.sqrt q

theorem suzukiArithmeticState_event_update (n : ℕ) :
    suzukiArithmeticState (n + 1) =
      (suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1),
        suzukiMangoldtIntercept n +
          suzukiMangoldtEventWeight (n + 1) * Real.log (n + 1)) := by
  rw [suzukiArithmeticState_succ]
  unfold suzukiMangoldtEventWeight
  congr 1
  ring

/-! ## Consecutive-event coverage and the sparse global criterion -/

theorem exists_mangoldtBlock_containing_nat (n : ℕ) (hn : 2 ≤ n) :
    ∃ q r, IsMangoldtBlock q r ∧ q ≤ n ∧ n < r := by
  classical
  let q := Nat.findGreatest IsMangoldtEvent n
  have htwo : IsMangoldtEvent 2 := by
    rw [isMangoldtEvent_iff_primePower]
    exact Nat.prime_two.isPrimePow
  have hqevent : IsMangoldtEvent q := by
    dsimp [q]
    exact Nat.findGreatest_spec hn htwo
  have hqn : q ≤ n := Nat.findGreatest_le n
  have hex : ∃ r : ℕ, n < r ∧ IsMangoldtEvent r := by
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    refine ⟨p, lt_of_lt_of_le (Nat.lt_succ_self n) hnp, ?_⟩
    rw [isMangoldtEvent_iff_primePower]
    exact hp.isPrimePow
  let r := Nat.find hex
  have hrspec : n < r ∧ IsMangoldtEvent r := Nat.find_spec hex
  refine ⟨q, r, ⟨hqn.trans_lt hrspec.1, hqevent, hrspec.2, ?_⟩, hqn, hrspec.1⟩
  intro k hqk hkr
  by_contra hk
  have hkevent : IsMangoldtEvent k := hk
  by_cases hkn : k ≤ n
  · have hkq : k ≤ q := Nat.le_findGreatest hkn hkevent
    omega
  · have hpred : n < k ∧ IsMangoldtEvent k := ⟨lt_of_not_ge hkn, hkevent⟩
    have hrk : r ≤ k := Nat.find_min' hex hpred
    omega

/-- Global Suzuki positivity can be indexed sparsely by consecutive
Mangoldt-event blocks rather than by every integer cell. -/
theorem suzukiPsiNonnegative_iff_initial_and_mangoldtBlockMargins :
    SuzukiPsiNonnegative ↔
      SuzukiInitialNonnegative ∧
        ∀ q r : ℕ, IsMangoldtBlock q r →
          0 ≤ suzukiMangoldtBlockMargin q r := by
  constructor
  · intro hpsi
    refine ⟨fun t ht0 ht2 => hpsi t, ?_⟩
    intro q r h
    rw [mangoldtBlockMargin_nonneg_iff h]
    intro t htq htr
    exact hpsi t
  · rintro ⟨hinit, hblocks⟩
    rw [suzukiPsiNonnegative_iff_initial_and_cellMargins]
    refine ⟨hinit, ?_⟩
    intro n hn
    obtain ⟨q, r, hblock, hqn, hnr⟩ := exists_mangoldtBlock_containing_nat n hn
    rw [suzukiCellMargin_nonneg_iff hn]
    have hpos := (mangoldtBlockMargin_nonneg_iff hblock).mp
      (hblocks q r hblock)
    intro t htn htn1
    apply hpos t
    · exact (Real.log_le_log (by positivity) (by exact_mod_cast hqn)).trans htn
    · exact htn1.trans (Real.log_le_log (by positivity)
        (by exact_mod_cast (show n + 1 ≤ r by omega)))

/-- RH as the compact initial condition plus one scalar inequality per
consecutive pair of Mangoldt events.  This is an equivalence only. -/
theorem riemannHypothesis_iff_initial_and_all_mangoldtBlockMargins :
    RiemannHypothesis ↔
      SuzukiInitialNonnegative ∧
        ∀ q r : ℕ, IsMangoldtBlock q r →
          0 ≤ suzukiMangoldtBlockMargin q r := by
  rw [riemannHypothesis_iff_shifted_zero_nonnegative]
  simp only [suzukiPsiShifted_zero_parameter]
  exact suzukiPsiNonnegative_iff_initial_and_mangoldtBlockMargins

/-! ## The unrestricted archimedean dual and event increments -/

/-- The half-line Legendre dual of the archimedean term.  Its analytic
finiteness/attainment theory is deliberately separated from this exact
order-theoretic definition. -/
noncomputable def suzukiArchDual (s : ℝ) : ℝ :=
  sSup (suzukiArchCellObjective s '' Ici (Real.log 2))

/-- A stronger, unrestricted-dual margin attached to an arithmetic state. -/
noncomputable def suzukiGlobalDualMargin (n : ℕ) : ℝ :=
  suzukiMangoldtIntercept n - suzukiArchDual (suzukiMangoldtSlope n)

theorem suzukiMangoldtBlockDual_le_archDual
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hbdd : BddAbove
      (suzukiArchCellObjective (suzukiMangoldtSlope q) '' Ici (Real.log 2))) :
    suzukiMangoldtBlockDual q r (suzukiMangoldtSlope q) ≤
      suzukiArchDual (suzukiMangoldtSlope q) := by
  have hqlog : 0 < Real.log q := Real.log_pos (by
    exact_mod_cast h.left_event.two_le)
  have hlog : Real.log q ≤ Real.log r :=
    Real.log_le_log (by positivity) (by exact_mod_cast h.left_lt.le)
  obtain ⟨t, ht, hdual, hmax⟩ := exists_suzukiArchIntervalDual_eq
    (s := suzukiMangoldtSlope q) hqlog hlog
  unfold suzukiMangoldtBlockDual
  rw [hdual]
  apply le_csSup hbdd
  refine ⟨t, ?_, rfl⟩
  exact (Real.log_le_log (by norm_num)
    (by exact_mod_cast h.left_event.two_le)).trans ht.1

/-- A nonnegative unrestricted margin is a sufficient certificate for every
finite block beginning at that event, provided the half-line dual is known
bounded above. -/
theorem globalDualMargin_nonneg_implies_blockMargin_nonneg
    {q r : ℕ} (h : IsMangoldtBlock q r)
    (hbdd : BddAbove
      (suzukiArchCellObjective (suzukiMangoldtSlope q) '' Ici (Real.log 2)))
    (hm : 0 ≤ suzukiGlobalDualMargin q) :
    0 ≤ suzukiMangoldtBlockMargin q r := by
  have hdual := suzukiMangoldtBlockDual_le_archDual h hbdd
  unfold suzukiGlobalDualMargin at hm
  unfold suzukiMangoldtBlockMargin
  linarith

/-- Exact finite-difference update of the global dual margin at the next
integer.  At a Mangoldt event this is the signed gain
`lambda*log(q) - (A*(S+lambda)-A*(S))`. -/
theorem globalDualMargin_event_update (n : ℕ) :
    suzukiGlobalDualMargin (n + 1) - suzukiGlobalDualMargin n =
      suzukiMangoldtEventWeight (n + 1) * Real.log (n + 1) -
        (suzukiArchDual
            (suzukiMangoldtSlope n + suzukiMangoldtEventWeight (n + 1)) -
          suzukiArchDual (suzukiMangoldtSlope n)) := by
  unfold suzukiGlobalDualMargin suzukiMangoldtEventWeight
  rw [suzukiMangoldtSlope_succ, suzukiMangoldtIntercept_succ]
  ring

end RHGarden
