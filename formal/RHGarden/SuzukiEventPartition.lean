import RHGarden.SuzukiFiniteEventCertificates

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

Finite event partitions with arbitrary integer anchors and terminal points.
The density is right continuous; its value at the right endpoint of an
integration cell may differ from the continuous service envelope there.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology Interval
namespace RHGarden

theorem IsSuzukiEventFreeCell.contained_in_block {q r : ℕ}
    (h : IsSuzukiEventFreeCell q r) (hq : 2 ≤ q) :
    ∃ p s, IsMangoldtBlock p s ∧ p ≤ q ∧ r ≤ s := by
  obtain ⟨p, s, hb, hpq, hqs⟩ := exists_mangoldtBlock_containing_nat q hq
  refine ⟨p, s, hb, hpq, ?_⟩
  by_contra hrs
  exact hb.right_event (h.2 s hqs (lt_of_not_ge hrs))

/-- A non-event terminal endpoint contributes zero arrival. The state at
the left endpoint already includes that endpoint's jump. -/
theorem signedRootState_nonEvent_terminal {m q r : ℕ}
    (hm : 1 ≤ m) (hmq : m ≤ q) (h : IsSuzukiEventFreeCell q r)
    (hr : ¬ IsMangoldtEvent r) :
    suzukiSignedRootState m (Real.sqrt r) =
      suzukiSignedRootState m (Real.sqrt q) - suzukiRootService (Real.sqrt q) (Real.sqrt r) := by
  have hz : ArithmeticFunction.vonMangoldt r = 0 := by
    simpa only [IsMangoldtEvent, not_not] using hr
  rw [signedRootState_eventFree_right hm hmq h, hz]
  simp

theorem neg_discrepancy_eq_serviceDecay_on_eventFree
    {q r : ℕ} (hq : 1 ≤ q) (h : IsSuzukiEventFreeCell q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    -suzukiRootSlopeDiscrepancy u = -suzukiRootSlopeDiscrepancy (Real.sqrt q) -
      suzukiRootService (Real.sqrt q) u := by
  have hs := suzukiSignedRootState_eq_neg_discrepancy hq hqu
  rw [suzukiSignedRootState,
    signedExcess_eq_eventValue_sub_service_on_eventFreeCell le_rfl h hqu hur] at hs
  have he : suzukiArrivalServiceExcess q q = 0 := by
    simp [suzukiArrivalServiceExcess, suzukiWeightedMangoldtInterval, suzukiRootService]
  rw [he] at hs
  linarith

theorem backlog_eq_serviceDecay_on_eventFree
    {q r : ℕ} (hq : 1 ≤ q) (h : IsSuzukiEventFreeCell q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiRootSlopeBacklog u = suzukiServiceDecayEnvelope (Real.sqrt q)
      (-suzukiRootSlopeDiscrepancy (Real.sqrt q)) u := by
  unfold suzukiRootSlopeBacklog suzukiServiceDecayEnvelope
  rw [neg_discrepancy_eq_serviceDecay_on_eventFree hq h hqu hur]

theorem intervalIntegrable_weighted_backlog_eventFree
    {q r : ℕ} (hq : 2 ≤ q) (h : IsSuzukiEventFreeCell q r) :
    IntervalIntegrable (fun u => 2 / u * suzukiRootSlopeBacklog u)
      volume (Real.sqrt q) (Real.sqrt r) := by
  have hint := intervalIntegrable_weighted_serviceDecayEnvelope
    (r := Real.sqrt q) (s := Real.sqrt r)
    (K := -suzukiRootSlopeDiscrepancy (Real.sqrt q))
    (Real.sqrt_le_sqrt (by exact_mod_cast hq))
    (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))
  apply hint.congr_uIoo
  intro u hu
  rw [uIoo_of_le (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))] at hu
  dsimp only
  rw [backlog_eq_serviceDecay_on_eventFree (by omega) h hu.1.le hu.2]

/-- Actual downward variation on one cell equals the service envelope at
the exact signed event state. No sign hypothesis at the anchor is needed. -/
theorem integral_weighted_backlog_eventFree_eq_cost
    {q r : ℕ} (hq : 2 ≤ q) (h : IsSuzukiEventFreeCell q r) :
    (∫ u in Real.sqrt q..Real.sqrt r, 2 / u * suzukiRootSlopeBacklog u) =
      suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt r)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt q)) := by
  rw [← integral_serviceDecayEnvelope_eq_exactCellCost
    (Real.sqrt_le_sqrt (by exact_mod_cast hq))
    (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))]
  apply intervalIntegral.integral_congr_uIoo
  intro u hu
  rw [uIoo_of_le (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))] at hu
  dsimp only
  rw [backlog_eq_serviceDecay_on_eventFree (by omega) h hu.1.le hu.2]

/-- Net loss is at most downward variation, including when a cell recovers
and the signed state becomes negative. -/
theorem psiRoot_loss_le_integral_backlog_eventFree
    {q r : ℕ} (hq : 2 ≤ q) (h : IsSuzukiEventFreeCell q r)
    {u : ℝ} (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u ≤
      ∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeBacklog v := by
  obtain ⟨p, s, hb, hpq, hrs⟩ := h.contained_in_block hq
  have hps := Real.sqrt_le_sqrt (show (p : ℝ) ≤ q by exact_mod_cast hpq)
  have hus : u ≤ Real.sqrt s := hur.trans (Real.sqrt_le_sqrt (by exact_mod_cast hrs))
  have harea := suzukiPsiRoot_sub_eq_integral_discrepancy_on_block hb hps hqu hus
  have hInt := (intervalIntegrable_weighted_backlog_eventFree hq h).mono_set
    (by rw [uIcc_of_le hqu,
            uIcc_of_le (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))]
        exact Icc_subset_Icc le_rfl hur)
  have hIntD : IntervalIntegrable (fun v => -(2 / v * suzukiRootSlopeDiscrepancy v))
      volume (Real.sqrt q) u := by
    have hcont : ContinuousOn
        (fun v => -(2 / v * (suzukiRootArchSlope v - suzukiMangoldtSlope p)))
        (Icc (Real.sqrt q) u) := by
      intro v hv
      have hvroot := (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ q by exact_mod_cast hq)).trans hv.1
      have hvpos : 0 < v := (Real.sqrt_pos.2 (by norm_num)).trans_le hvroot
      exact (((continuousAt_const.div continuousAt_id hvpos.ne').mul
        ((hasDerivAt_suzukiRootArchSlope hvroot).continuousAt.sub
          continuousAt_const)).neg).continuousWithinAt
    apply (hcont.intervalIntegrable_of_Icc hqu).congr_uIoo
    intro v hv
    rw [uIoo_of_le hqu] at hv
    dsimp only
    rw [suzukiRootSlopeDiscrepancy_eq_on_block hb (hps.trans hv.1.le)
      (hv.2.trans_le hus)]
  rw [← neg_sub, harea, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_mono_on hqu hIntD hInt
  intro v hv
  have hv0 : 0 ≤ 2 / v := div_nonneg (by norm_num) ((Real.sqrt_nonneg q).trans hv.1)
  calc
    -(2 / v * suzukiRootSlopeDiscrepancy v) = 2 / v * (-suzukiRootSlopeDiscrepancy v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hv0

theorem exactServiceCellCost_mono_state {a b K L : ℝ}
    (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) (hKL : K ≤ L) :
    suzukiExactServiceCellCost a b K ≤ suzukiExactServiceCellCost a b L := by
  rw [← integral_serviceDecayEnvelope_eq_exactCellCost ha hab,
    ← integral_serviceDecayEnvelope_eq_exactCellCost ha hab]
  apply intervalIntegral.integral_mono_on hab
    (intervalIntegrable_weighted_serviceDecayEnvelope ha hab)
    (intervalIntegrable_weighted_serviceDecayEnvelope ha hab)
  intro u hu
  exact mul_le_mul_of_nonneg_left (max_le_max_right 0 (sub_le_sub_right hKL _))
    (div_nonneg (by norm_num) ((Real.sqrt_nonneg 2).trans (ha.trans hu.1)))

theorem weighted_backlog_eventFree_le_eventCost
    {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q) (h : IsSuzukiEventFreeCell q r)
    {e : ℝ} (he : suzukiArrivalServiceExcess m q ≤ e) :
    (∫ u in Real.sqrt q..Real.sqrt r, 2 / u * suzukiRootSlopeBacklog u) ≤
      suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt r)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt m) + e) := by
  rw [integral_weighted_backlog_eventFree_eq_cost (hm.trans hmq) h]
  apply exactServiceCellCost_mono_state
    (Real.sqrt_le_sqrt (by exact_mod_cast hm.trans hmq))
    (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))
  have hs := rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess (by omega : 1 ≤ m) hmq
  linarith

/-- Finite ordered cells, with zero arrivals between adjacent points.
Endpoints need not be Mangoldt events, and the empty interval is allowed. -/
inductive SuzukiEventChain : ℕ → ℕ → Type
  | nil (q : ℕ) : SuzukiEventChain q q
  | cons {q r s : ℕ} (cell : IsSuzukiEventFreeCell q r)
      (tail : SuzukiEventChain r s) : SuzukiEventChain q s

namespace SuzukiEventChain

def points {q r : ℕ} : SuzukiEventChain q r → Finset ℕ
  | .nil q => {q}
  | @cons q _ _ _ tail => insert q tail.points

theorem ordered {q r : ℕ} (chain : SuzukiEventChain q r) : q ≤ r := by
  induction chain with
  | nil => rfl
  | cons h _ ih => exact h.1.le.trans ih

theorem left_mem {q r : ℕ} (chain : SuzukiEventChain q r) : q ∈ chain.points := by
  cases chain <;> simp [points]

theorem right_mem {q r : ℕ} (chain : SuzukiEventChain q r) : r ∈ chain.points := by
  induction chain with
  | nil => simp [points]
  | cons h tail ih => exact Finset.mem_insert_of_mem ih

theorem mem_bounds {q r k : ℕ} (chain : SuzukiEventChain q r) (hk : k ∈ chain.points) :
    q ≤ k ∧ k ≤ r := by
  induction chain with
  | nil q =>
      simp only [points, Finset.mem_singleton] at hk
      subst k
      exact ⟨le_rfl, le_rfl⟩
  | @cons q p r h tail ih =>
      simp only [points, Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact ⟨le_rfl, h.1.le.trans tail.ordered⟩
      · have hh := ih hk
        exact ⟨h.1.le.trans hh.1, hh.2⟩

/-- Completeness is checked against von Mangoldt, hence includes every
prime power, independently of any external sieve. -/
theorem event_mem {q r k : ℕ} (chain : SuzukiEventChain q r)
    (hqk : q ≤ k) (hkr : k ≤ r) (hk : IsMangoldtEvent k) : k ∈ chain.points := by
  induction chain with
  | nil q =>
      have : k = q := by omega
      subst k
      simp [points]
  | @cons q p r h tail ih =>
      by_cases heq : k = q
      · subst k; exact chain_left h tail
      · have hpk : p ≤ k := by
          by_contra hn
          exact hk (h.2 k (by omega) (by omega))
        exact Finset.mem_insert_of_mem (ih hpk hkr)
where
  chain_left {q p r : ℕ} (h : IsSuzukiEventFreeCell q p) (t : SuzukiEventChain p r) :
      q ∈ (SuzukiEventChain.cons h t).points := by simp [points]

theorem exists_sparse (m n : ℕ) (hmn : m ≤ n) :
    ∃ chain : SuzukiEventChain m n,
      ∀ k ∈ chain.points, k = m ∨ k = n ∨ IsMangoldtEvent k := by
  classical
  generalize hd : n - m = d
  induction d using Nat.strong_induction_on generalizing m with
  | h d ih =>
      by_cases hmn' : m = n
      · subst m
        refine ⟨.nil n, ?_⟩
        intro k hk
        simp only [points, Finset.mem_singleton] at hk
        exact Or.inl hk
      · have hex : ∃ p : ℕ, m < p ∧ p ≤ n ∧ (p = n ∨ IsMangoldtEvent p) :=
          ⟨n, by omega, le_rfl, Or.inl rfl⟩
        let p := Nat.find hex
        have hp : m < p ∧ p ≤ n ∧ (p = n ∨ IsMangoldtEvent p) := Nat.find_spec hex
        have hcell : IsSuzukiEventFreeCell m p := by
          refine ⟨hp.1, ?_⟩
          intro k hmk hkp
          by_contra hk
          have hpk : p ≤ k := Nat.find_min' hex ⟨hmk, hkp.le.trans hp.2.1, Or.inr hk⟩
          omega
        obtain ⟨tail, ht⟩ := ih (n - p) (by omega) p hp.2.1 rfl
        refine ⟨.cons hcell tail, ?_⟩
        intro k hk
        simp only [points, Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact Or.inl rfl
        · rcases ht k hk with rfl | hn | he
          · exact Or.inr hp.2.2
          · exact Or.inr (Or.inl hn)
          · exact Or.inr (Or.inr he)

/-- An ordered realization of exactly the canonical event partition. The
least-next-event construction is justified internally using `Nat.find`. -/
theorem exists_canonical (m n : ℕ) (hmn : m ≤ n) :
    ∃ chain : SuzukiEventChain m n, chain.points = suzukiMangoldtEventPartition m n := by
  obtain ⟨chain, hc⟩ := exists_sparse m n hmn
  refine ⟨chain, ?_⟩
  ext k
  rw [mem_suzukiMangoldtEventPartition_iff]
  constructor
  · intro hk
    exact ⟨(chain.mem_bounds hk).1, (chain.mem_bounds hk).2, hc k hk⟩
  · rintro ⟨hmk, hkn, rfl | rfl | he⟩
    · exact chain.left_mem
    · exact chain.right_mem
    · exact chain.event_mem hmk hkn he

def canonical (m n : ℕ) (hmn : m ≤ n) : SuzukiEventChain m n :=
  Classical.choose (exists_canonical m n hmn)

theorem canonical_points (m n : ℕ) (hmn : m ≤ n) :
    (canonical m n hmn).points = suzukiMangoldtEventPartition m n :=
  Classical.choose_spec (exists_canonical m n hmn)

def eventBounds {q r : ℕ} (m : ℕ) (e : ℕ → ℝ) : SuzukiEventChain q r → Prop
  | .nil _ => True
  | @cons q _ _ _ tail => suzukiArrivalServiceExcess m q ≤ e q ∧ tail.eventBounds m e

def exactCost {q r : ℕ} (m : ℕ) (e : ℕ → ℝ) : SuzukiEventChain q r → ℝ
  | .nil _ => 0
  | @cons q p _ _ tail => suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt p)
      (-suzukiRootSlopeDiscrepancy (Real.sqrt m) + e q) + tail.exactCost m e

def costBounds {q r : ℕ} (m : ℕ) (e : ℕ → ℝ) (c : ℕ → ℕ → ℝ) :
    SuzukiEventChain q r → Prop
  | .nil _ => True
  | @cons q p _ _ tail => suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt p)
      (-suzukiRootSlopeDiscrepancy (Real.sqrt m) + e q) ≤ c q p ∧ tail.costBounds m e c

def sumCosts {q r : ℕ} (c : ℕ → ℕ → ℝ) : SuzukiEventChain q r → ℝ
  | .nil _ => 0
  | @cons q p _ _ tail => c q p + tail.sumCosts c

theorem exactCost_le_sumCosts {q r m : ℕ} (chain : SuzukiEventChain q r)
    {e : ℕ → ℝ} {c : ℕ → ℕ → ℝ} (hc : chain.costBounds m e c) :
    chain.exactCost m e ≤ chain.sumCosts c := by
  induction chain with
  | nil => exact le_rfl
  | cons h tail ih => exact add_le_add hc.1 (ih hc.2)

theorem backlog_integrable {q r : ℕ} (chain : SuzukiEventChain q r) (hq : 2 ≤ q) :
    IntervalIntegrable (fun u => 2 / u * suzukiRootSlopeBacklog u)
      volume (Real.sqrt q) (Real.sqrt r) := by
  induction chain with
  | nil => exact IntervalIntegrable.refl
  | cons h tail ih =>
      exact (intervalIntegrable_weighted_backlog_eventFree hq h).trans
        (ih (hq.trans h.1.le))

theorem backlog_integral_le_exactCost {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q)
    (chain : SuzukiEventChain q r) {e : ℕ → ℝ} (he : chain.eventBounds m e) :
    (∫ u in Real.sqrt q..Real.sqrt r, 2 / u * suzukiRootSlopeBacklog u) ≤
      chain.exactCost m e := by
  induction chain with
  | nil => simp [exactCost]
  | cons h tail ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_weighted_backlog_eventFree (hm.trans hmq) h)
        (tail.backlog_integrable (hm.trans (hmq.trans h.1.le)))]
      exact add_le_add (weighted_backlog_eventFree_le_eventCost hm hmq h he.1)
        (ih (hmq.trans h.1.le) he.2)

theorem loss_le_backlog_integral {q r : ℕ} (chain : SuzukiEventChain q r) (hq : 2 ≤ q)
    {u : ℝ} (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u ≤
      ∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeBacklog v := by
  induction chain generalizing u with
  | nil q =>
      have : u = Real.sqrt q := le_antisymm hur hqu
      subst u
      simp
  | @cons q p r h tail ih =>
      have hqp := Real.sqrt_le_sqrt (show (q : ℝ) ≤ p by exact_mod_cast h.1.le)
      by_cases hup : u ≤ Real.sqrt p
      · exact psiRoot_loss_le_integral_backlog_eventFree hq h hqu hup
      · have hpu := le_of_not_ge hup
        have hint := (tail.backlog_integrable (hq.trans h.1.le)).mono_set (by
          rw [uIcc_of_le hpu, uIcc_of_le (Real.sqrt_le_sqrt (by exact_mod_cast tail.ordered))]
          exact Icc_subset_Icc le_rfl hur)
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_weighted_backlog_eventFree hq h) hint]
        have hl := psiRoot_loss_le_integral_backlog_eventFree hq h hqp le_rfl
        have ht := ih (hq.trans h.1.le) hpu hur
        linarith

/-- All prefixes are controlled by the one total finite cost because the
backlog density is nonnegative. -/
theorem loss_le_exactCost {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q)
    (chain : SuzukiEventChain q r) {e : ℕ → ℝ} (he : chain.eventBounds m e)
    {u : ℝ} (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u ≤ chain.exactCost m e := by
  have hp : (∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeBacklog v) ≤
      ∫ v in Real.sqrt q..Real.sqrt r, 2 / v * suzukiRootSlopeBacklog v := by
    apply intervalIntegral.integral_mono_interval le_rfl hqu hur
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      exact mul_nonneg (div_nonneg (by norm_num) ((Real.sqrt_nonneg q).trans hv.1.le))
        (le_max_right _ _)
    · exact chain.backlog_integrable (hm.trans hmq)
  exact (chain.loss_le_backlog_integral (hm.trans hmq) hqu hur).trans
    (hp.trans (chain.backlog_integral_le_exactCost hm hmq he))

end SuzukiEventChain

/-- Finite data for arbitrary integer endpoints. Analytic gluing,
measurability, integrability, and all-prefix loss control are consequences,
never input fields. -/
structure SuzukiFinitePartitionCertificate where
  anchor : ℕ
  terminal : ℕ
  anchor_ge_two : 2 ≤ anchor
  chain : SuzukiEventChain anchor terminal
  eventUpper : ℕ → ℝ
  cellCostUpper : ℕ → ℕ → ℝ
  reserve : ℝ
  event_bounds : chain.eventBounds anchor eventUpper
  cost_bounds : chain.costBounds anchor eventUpper cellCostUpper
  reserve_bound : reserve ≤ suzukiPsiRoot (Real.sqrt anchor)
  total_safe : chain.sumCosts cellCostUpper ≤ reserve

theorem SuzukiFinitePartitionCertificate.nonnegative
    (c : SuzukiFinitePartitionCertificate) {u : ℝ}
    (hu : u ∈ Icc (Real.sqrt c.anchor) (Real.sqrt c.terminal)) :
    0 ≤ suzukiPsiRoot u := by
  have h := c.chain.loss_le_exactCost c.anchor_ge_two le_rfl c.event_bounds hu.1 hu.2
  linarith [c.reserve_bound, c.total_safe, c.chain.exactCost_le_sumCosts c.cost_bounds]

def SuzukiFinitePartitionCertificate.toBusyPeriodCertificate
    (c : SuzukiFinitePartitionCertificate) : SuzukiBusyPeriodCertificate where
  startRoot := Real.sqrt c.anchor
  endRoot := Real.sqrt c.terminal
  reserveLower := c.reserve
  lossUpper := c.chain.exactCost c.anchor c.eventUpper
  roots_ordered := Real.sqrt_le_sqrt (by exact_mod_cast c.chain.ordered)
  reserve_bound := c.reserve_bound
  loss_bound := fun _ hu => c.chain.loss_le_exactCost c.anchor_ge_two le_rfl
    c.event_bounds hu.1 hu.2
  safe := (c.chain.exactCost_le_sumCosts c.cost_bounds).trans c.total_safe

theorem SuzukiEventChain.backlog_aestronglyMeasurable {m n : ℕ}
    (chain : SuzukiEventChain m n) (hm : 2 ≤ m) :
    AEStronglyMeasurable (fun u => 2 / u * suzukiRootSlopeBacklog u)
      (volume.restrict (Icc (Real.sqrt m) (Real.sqrt n))) := by
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
    (Real.sqrt_le_sqrt (by exact_mod_cast chain.ordered))).mp
      (chain.backlog_integrable hm)).aestronglyMeasurable

end RHGarden
