import RHGarden.SuzukiChebyshevProfiles

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

namespace RHGarden

/-! ## Canonical finite Mangoldt-event partitions -/

/-- The finite set consisting of both endpoints and every Mangoldt event in
`[m,n]`.  Its ambient order is the natural-number order. -/
noncomputable def suzukiMangoldtEventPartition (m n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc m n).filter fun q => q = m ∨ q = n ∨ IsMangoldtEvent q

theorem mem_suzukiMangoldtEventPartition_iff {m n q : ℕ} :
    q ∈ suzukiMangoldtEventPartition m n ↔
      m ≤ q ∧ q ≤ n ∧ (q = m ∨ q = n ∨ IsMangoldtEvent q) := by
  classical
  simp [suzukiMangoldtEventPartition, and_assoc]

theorem left_mem_suzukiMangoldtEventPartition {m n : ℕ} (hmn : m ≤ n) :
    m ∈ suzukiMangoldtEventPartition m n := by
  rw [mem_suzukiMangoldtEventPartition_iff]
  exact ⟨le_rfl, hmn, Or.inl rfl⟩

theorem right_mem_suzukiMangoldtEventPartition {m n : ℕ} (hmn : m ≤ n) :
    n ∈ suzukiMangoldtEventPartition m n := by
  rw [mem_suzukiMangoldtEventPartition_iff]
  exact ⟨hmn, le_rfl, Or.inr (Or.inl rfl)⟩

theorem event_mem_suzukiMangoldtEventPartition
    {m n q : ℕ} (hmq : m ≤ q) (hqn : q ≤ n) (hq : IsMangoldtEvent q) :
    q ∈ suzukiMangoldtEventPartition m n := by
  rw [mem_suzukiMangoldtEventPartition_iff]
  exact ⟨hmq, hqn, Or.inr (Or.inr hq)⟩

/-- Consecutive points of the canonical partition. -/
def IsConsecutiveSuzukiEventPoint (m n q r : ℕ) : Prop :=
  q ∈ suzukiMangoldtEventPartition m n ∧
    r ∈ suzukiMangoldtEventPartition m n ∧ q < r ∧
      ∀ k ∈ suzukiMangoldtEventPartition m n, q < k → r ≤ k

/-- A generalized event-free cell.  Unlike `IsMangoldtBlock`, the right
endpoint may be a non-event terminal point. -/
def IsSuzukiEventFreeCell (q r : ℕ) : Prop :=
  q < r ∧ ∀ k : ℕ, q < k → k < r → ArithmeticFunction.vonMangoldt k = 0

theorem IsConsecutiveSuzukiEventPoint.eventFree
    {m n q r : ℕ} (h : IsConsecutiveSuzukiEventPoint m n q r) :
    IsSuzukiEventFreeCell q r := by
  refine ⟨h.2.2.1, ?_⟩
  intro k hqk hkr
  by_contra hk
  have hqmem := (mem_suzukiMangoldtEventPartition_iff.mp h.1)
  have hrmem := (mem_suzukiMangoldtEventPartition_iff.mp h.2.1)
  have hkmem : k ∈ suzukiMangoldtEventPartition m n :=
    event_mem_suzukiMangoldtEventPartition
      (hqmem.1.trans hqk.le) (hkr.le.trans hrmem.2.1) hk
  exact (not_le_of_gt hkr) (h.2.2.2 k hkmem hqk)

theorem isSuzukiEventFreeCell_of_mangoldtBlock
    {q r : ℕ} (h : IsMangoldtBlock q r) : IsSuzukiEventFreeCell q r :=
  ⟨h.left_lt, fun k hqk hkr => h.eq_zero_between hqk hkr⟩

/-! ## Signed event dynamics -/

/-- Arrival minus service from the root anchor `sqrt m` to `u`. -/
noncomputable def suzukiSignedArrivalServiceExcess (m : ℕ) (u : ℝ) : ℝ :=
  suzukiWeightedMangoldtInterval m ⌊u ^ 2⌋₊ -
    suzukiRootService (Real.sqrt m) u

/-- The signed post-anchor state.  It is `-D(u)` exactly, without assuming
that the anchor lies in a negative excursion. -/
noncomputable def suzukiSignedRootState (m : ℕ) (u : ℝ) : ℝ :=
  -suzukiRootSlopeDiscrepancy (Real.sqrt m) +
    suzukiSignedArrivalServiceExcess m u

theorem suzukiSignedRootState_eq_neg_discrepancy
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    suzukiSignedRootState m u = -suzukiRootSlopeDiscrepancy u := by
  have h := rootSlopeDiscrepancy_sub_sqrt_eq_service_sub_arrival hm hmu
  unfold suzukiSignedRootState suzukiSignedArrivalServiceExcess
  linarith

theorem suzukiRootSlopeBacklog_eq_max_signedRootState
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    suzukiRootSlopeBacklog u = max (suzukiSignedRootState m u) 0 := by
  rw [suzukiRootSlopeBacklog, suzukiSignedRootState_eq_neg_discrepancy hm hmu]

private theorem floor_sq_lt_of_lt_sqrt
    {u : ℝ} {r : ℕ} (hu0 : 0 ≤ u) (hur : u < Real.sqrt r) :
    ⌊u ^ 2⌋₊ < r := by
  apply (Nat.floor_lt (sq_nonneg u)).2
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg r)]

private theorem nat_le_floor_sq_of_sqrt_le'
    {q : ℕ} {u : ℝ} (hqu : Real.sqrt q ≤ u) :
    q ≤ ⌊u ^ 2⌋₊ := by
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg q).trans hqu
  apply Nat.le_floor
  nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg q) hqu,
    Real.sq_sqrt (Nat.cast_nonneg q)]

theorem weightedMangoldtInterval_eq_zero_of_eventFree
    {q r p : ℕ} (h : IsSuzukiEventFreeCell q r)
    (hqp : q ≤ p) (hpr : p < r) :
    suzukiWeightedMangoldtInterval q p = 0 := by
  classical
  unfold suzukiWeightedMangoldtInterval
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_Ioc.mp hk
  rw [h.2 k hk'.1 (hk'.2.trans_lt hpr)]
  simp

theorem weightedMangoldtInterval_eventFree_right
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) :
    suzukiWeightedMangoldtInterval q r =
      ArithmeticFunction.vonMangoldt r / Real.sqrt r := by
  classical
  unfold suzukiWeightedMangoldtInterval
  rw [show Finset.Ioc q r = insert r (Finset.Ioo q r) by
    have hqr := h.1
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ioo]
    omega]
  rw [Finset.sum_insert (by simp)]
  have hsum : ∑ k ∈ Finset.Ioo q r,
      ArithmeticFunction.vonMangoldt k / Real.sqrt k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [h.2 k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2]
    simp
  rw [hsum, add_zero]

theorem signedExcess_eq_eventValue_sub_service_on_eventFreeCell
    {m q r : ℕ} (hmq : m ≤ q) (h : IsSuzukiEventFreeCell q r)
    {u : ℝ} (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiSignedArrivalServiceExcess m u =
      suzukiArrivalServiceExcess m q - suzukiRootService (Real.sqrt q) u := by
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg q).trans hqu
  have hfloorQ : q ≤ ⌊u ^ 2⌋₊ := nat_le_floor_sq_of_sqrt_le' hqu
  have hfloorR : ⌊u ^ 2⌋₊ < r := floor_sq_lt_of_lt_sqrt hu0 hur
  have hzero := weightedMangoldtInterval_eq_zero_of_eventFree h hfloorQ hfloorR
  have harrival := suzukiWeightedMangoldtInterval_add hmq hfloorQ
  rw [hzero, add_zero] at harrival
  rw [suzukiSignedArrivalServiceExcess, suzukiArrivalServiceExcess,
    harrival, suzukiRootService_add]
  ring

/-- Exact signed kick recurrence, including a zero-weight non-event terminal. -/
theorem signedRootState_eventFree_right
    {m q r : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q)
    (h : IsSuzukiEventFreeCell q r) :
    suzukiSignedRootState m (Real.sqrt r) =
      suzukiSignedRootState m (Real.sqrt q) -
        suzukiRootService (Real.sqrt q) (Real.sqrt r) +
          ArithmeticFunction.vonMangoldt r / Real.sqrt r := by
  have hmr : m ≤ r := hmq.trans h.1.le
  have hstateQ := suzukiSignedRootState_eq_neg_discrepancy
    (m := m) (u := Real.sqrt q) hm
    (Real.sqrt_le_sqrt (show (m : ℝ) ≤ q by exact_mod_cast hmq))
  have hstateR := suzukiSignedRootState_eq_neg_discrepancy
    (m := m) (u := Real.sqrt r) hm
    (Real.sqrt_le_sqrt (show (m : ℝ) ≤ r by exact_mod_cast hmr))
  have hbalance := rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess
    (hm.trans hmq) h.1.le
  rw [suzukiArrivalServiceExcess,
    weightedMangoldtInterval_eventFree_right h] at hbalance
  rw [hstateQ, hstateR]
  linarith

/-- A finite event bound controls every point of the following event-free
cell.  The signed anchor state is retained even when it is negative. -/
theorem backlog_le_eventBound_sub_service
    {m q r : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q)
    (h : IsSuzukiEventFreeCell q r) {e u : ℝ}
    (he : suzukiArrivalServiceExcess m q ≤ e)
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiRootSlopeBacklog u ≤
      max (-suzukiRootSlopeDiscrepancy (Real.sqrt m) + e -
        suzukiRootService (Real.sqrt q) u) 0 := by
  have hmu : Real.sqrt m ≤ u :=
    (Real.sqrt_le_sqrt (by exact_mod_cast hmq)).trans hqu
  rw [suzukiRootSlopeBacklog_eq_max_signedRootState hm hmu]
  unfold suzukiSignedRootState
  rw [signedExcess_eq_eventValue_sub_service_on_eventFreeCell hmq h hqu hur]
  exact max_le_max_right 0 (by linarith)

/-! ## Exact service-decay cell costs -/

theorem strictMonoOn_suzukiRootArchSlope :
    StrictMonoOn suzukiRootArchSlope (Ici (Real.sqrt 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (Real.sqrt 2))
  · intro u hu
    exact (hasDerivAt_suzukiRootArchSlope hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    have hfive := five_thirds_le_deriv_suzukiRootArchSlope hu.le
    linarith

theorem suzukiRootService_strictMono_right
    {r : ℝ} (hr : Real.sqrt 2 ≤ r) :
    StrictMonoOn (suzukiRootService r) (Ici r) := by
  intro x hx y hy hxy
  unfold suzukiRootService
  exact sub_lt_sub_right
    (strictMonoOn_suzukiRootArchSlope (hr.trans hx) (hr.trans hy) hxy) _

theorem suzukiRootService_mono_right
    {r : ℝ} (hr : Real.sqrt 2 ≤ r) :
    MonotoneOn (suzukiRootService r) (Ici r) :=
  (suzukiRootService_strictMono_right hr).monotoneOn

theorem suzukiRootService_nonneg_real
    {r u : ℝ} (hr : Real.sqrt 2 ≤ r) (hru : r ≤ u) :
    0 ≤ suzukiRootService r u := by
  have hmono := suzukiRootService_mono_right hr
    (by simp) (by simpa using hru) hru
  simpa [suzukiRootService] using hmono

/-- The cell envelope obtained from an event-prefix excess bound. -/
noncomputable def suzukiServiceDecayEnvelope (r K u : ℝ) : ℝ :=
  max (K - suzukiRootService r u) 0

/-- A cutoff records exactly where smooth service exhausts a nonnegative
event bound.  The endpoint cases avoid inventing a transcendental root. -/
def IsSuzukiServiceCutoff (r s K h : ℝ) : Prop :=
  h ∈ Icc r s ∧
    ((K ≤ 0 ∧ h = r) ∨
      (0 < K ∧ suzukiRootService r s ≤ K ∧ h = s) ∨
      (0 < K ∧ K < suzukiRootService r s ∧
        suzukiRootService r h = K))

private theorem continuousOn_suzukiRootService
    {r s : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    ContinuousOn (suzukiRootService r) (Icc r s) := by
  intro u hu
  unfold suzukiRootService
  exact ((hasDerivAt_suzukiRootArchSlope (hr.trans hu.1)).continuousAt.sub
    continuousAt_const).continuousWithinAt

theorem exists_suzukiServiceCutoff
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    ∃ h, IsSuzukiServiceCutoff r s K h := by
  by_cases hK : K ≤ 0
  · exact ⟨r, ⟨le_rfl, hrs⟩, Or.inl ⟨hK, rfl⟩⟩
  by_cases hsK : suzukiRootService r s ≤ K
  · exact ⟨s, ⟨hrs, le_rfl⟩, Or.inr (Or.inl ⟨lt_of_not_ge hK, hsK, rfl⟩)⟩
  · have hK0 : 0 ≤ K := (lt_of_not_ge hK).le
    have hKs : K ≤ suzukiRootService r s := (lt_of_not_ge hsK).le
    have hmem : K ∈ Icc (suzukiRootService r r) (suzukiRootService r s) := by
      simpa [suzukiRootService] using And.intro hK0 hKs
    rcases intermediate_value_Icc hrs (continuousOn_suzukiRootService hr hrs) hmem with
      ⟨h, hh, hvalue⟩
    exact ⟨h, hh, Or.inr (Or.inr
      ⟨lt_of_not_ge hK, lt_of_not_ge hsK, hvalue⟩)⟩

noncomputable def suzukiServiceCutoff (r s K : ℝ) : ℝ :=
  if h : Real.sqrt 2 ≤ r ∧ r ≤ s then
    Classical.choose (exists_suzukiServiceCutoff (r := r) (s := s) (K := K) h.1 h.2)
  else r

theorem suzukiServiceCutoff_spec
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    IsSuzukiServiceCutoff r s K (suzukiServiceCutoff r s K) := by
  rw [suzukiServiceCutoff, dif_pos ⟨hr, hrs⟩]
  exact Classical.choose_spec (exists_suzukiServiceCutoff hr hrs)

theorem suzukiServiceCutoff_unique
    {r s K h₁ h₂ : ℝ} (hr : Real.sqrt 2 ≤ r)
    (h₁spec : IsSuzukiServiceCutoff r s K h₁)
    (h₂spec : IsSuzukiServiceCutoff r s K h₂) : h₁ = h₂ := by
  rcases h₁spec.2 with h₁left | h₁rest
  · rcases h₂spec.2 with h₂left | h₂rest
    · exact h₁left.2.trans h₂left.2.symm
    · rcases h₂rest with h₂right | h₂inside <;> linarith
  · rcases h₂spec.2 with h₂left | h₂rest
    · rcases h₁rest with h₁right | h₁inside <;> linarith
    · rcases h₁rest with h₁right | h₁inside
      · rcases h₂rest with h₂right | h₂inside
        · exact h₁right.2.2.trans h₂right.2.2.symm
        · exfalso
          linarith [h₁right.2.1, h₂inside.2.1]
      · rcases h₂rest with h₂right | h₂inside
        · exfalso
          linarith [h₂right.2.1, h₁inside.2.1]
        · by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hs := (suzukiRootService_strictMono_right hr)
              h₁spec.1.1 h₂spec.1.1 hlt
            rw [h₁inside.2.2, h₂inside.2.2] at hs
            exact (lt_irrefl K hs)
          · have hs := (suzukiRootService_strictMono_right hr)
              h₂spec.1.1 h₁spec.1.1 hgt
            rw [h₁inside.2.2, h₂inside.2.2] at hs
            exact (lt_irrefl K hs)

/-- Chain rule in root coordinates for the archimedean primitive. -/
theorem hasDerivAt_suzukiArchimedean_root
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    HasDerivAt (fun v => suzukiPsiArchimedean (2 * Real.log v))
      (2 / u * suzukiRootArchSlope u) u := by
  have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le hu
  have htpos : 0 < 2 * Real.log u := by
    have hu1 : 1 < u := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    exact mul_pos (by norm_num) (Real.log_pos hu1)
  have houter := hasDerivAt_suzukiPsiArchimedean_of_pos htpos
  have houter' : HasDerivAt suzukiPsiArchimedean
      (suzukiRootArchSlope u) (2 * Real.log u) := by
    rw [suzukiRootArchSlope]
    exact houter.congr_deriv houter.deriv.symm
  have hinner : HasDerivAt (fun v : ℝ => 2 * Real.log v) (2 / u) u := by
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hu0.ne').const_mul 2
  simpa only [Function.comp_def, mul_comm] using houter'.comp u hinner

theorem integral_serviceDecay_untruncated
    {r h K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrh : r ≤ h) :
    (∫ u in r..h, 2 / u * (K - suzukiRootService r u)) =
      2 * (K + suzukiRootArchSlope r) * Real.log (h / r) -
        suzukiPsiArchimedean (2 * Real.log h) +
        suzukiPsiArchimedean (2 * Real.log r) := by
  let primitive : ℝ → ℝ := fun u =>
    2 * (K + suzukiRootArchSlope r) * Real.log u -
      suzukiPsiArchimedean (2 * Real.log u)
  have hcont : ContinuousOn primitive (Icc r h) := by
    intro u hu
    have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le (hr.trans hu.1)
    exact ((continuousAt_const.mul (Real.continuousAt_log hu0.ne')).sub
      (hasDerivAt_suzukiArchimedean_root (hr.trans hu.1)).continuousAt).continuousWithinAt
  have hderiv : ∀ u ∈ Ioo r h, HasDerivAt primitive
      (2 / u * (K - suzukiRootService r u)) u := by
    intro u hu
    have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le
      (hr.trans hu.1.le)
    have hlog := (Real.hasDerivAt_log hu0.ne').const_mul
      (2 * (K + suzukiRootArchSlope r))
    have harch := hasDerivAt_suzukiArchimedean_root (hr.trans hu.1.le)
    have hsub := hlog.sub harch
    apply hsub.congr_deriv
    unfold suzukiRootService
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun u => 2 / u * (K - suzukiRootService r u)) volume r h := by
    apply ContinuousOn.intervalIntegrable_of_Icc hrh
    intro u hu
    have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le
      (hr.trans hu.1)
    exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
      (continuousAt_const.sub
        ((hasDerivAt_suzukiRootArchSlope (hr.trans hu.1)).continuousAt.sub
          continuousAt_const))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrh hcont hderiv hint]
  dsimp [primitive]
  have hr0 : r ≠ 0 := ne_of_gt ((Real.sqrt_pos.2 (by norm_num)).trans_le hr)
  have hh0 : h ≠ 0 := ne_of_gt ((Real.sqrt_pos.2 (by norm_num)).trans_le (hr.trans hrh))
  rw [Real.log_div hh0 hr0]
  ring

private theorem intervalIntegrable_weighted_serviceDecayEnvelope
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    IntervalIntegrable
      (fun u => 2 / u * suzukiServiceDecayEnvelope r K u) volume r s := by
  apply ContinuousOn.intervalIntegrable_of_Icc hrs
  intro u hu
  have hu0 : 0 < u :=
    (Real.sqrt_pos.2 (by norm_num)).trans_le (hr.trans hu.1)
  have hservice : ContinuousAt (suzukiRootService r) u := by
    unfold suzukiRootService
    exact (hasDerivAt_suzukiRootArchSlope (hr.trans hu.1)).continuousAt.sub
      continuousAt_const
  exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
    ((continuousAt_const.sub hservice).max continuousAt_const)).continuousWithinAt

private theorem serviceDecayEnvelope_eq_untruncated
    {r K u : ℝ} (hle : suzukiRootService r u ≤ K) :
    suzukiServiceDecayEnvelope r K u = K - suzukiRootService r u := by
  rw [suzukiServiceDecayEnvelope, max_eq_left]
  linarith

private theorem serviceDecayEnvelope_eq_zero
    {r K u : ℝ} (hle : K ≤ suzukiRootService r u) :
    suzukiServiceDecayEnvelope r K u = 0 := by
  rw [suzukiServiceDecayEnvelope, max_eq_right]
  linarith

/-- Exact cost of a service-decay envelope.  The cutoff is characterized by
the strictly increasing archimedean service, so no floating-point root enters
the statement. -/
theorem integral_serviceDecayEnvelope_eq_cutoffCost
    {r s K h : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s)
    (hcut : IsSuzukiServiceCutoff r s K h) :
    (∫ u in r..s, 2 / u * suzukiServiceDecayEnvelope r K u) =
      2 * (K + suzukiRootArchSlope r) * Real.log (h / r) -
        suzukiPsiArchimedean (2 * Real.log h) +
        suzukiPsiArchimedean (2 * Real.log r) := by
  rcases hcut.2 with hleft | hrest
  · have hzero : ∀ u ∈ Icc r s, suzukiServiceDecayEnvelope r K u = 0 := by
      intro u hu
      apply serviceDecayEnvelope_eq_zero
      exact hleft.1.trans (suzukiRootService_nonneg_real hr hu.1)
    have hint : (∫ u in r..s, 2 / u * suzukiServiceDecayEnvelope r K u) = 0 := by
      calc
        (∫ u in r..s, 2 / u * suzukiServiceDecayEnvelope r K u) =
            ∫ _u in r..s, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro u hu
              rw [uIcc_of_le hrs] at hu
              simp [hzero u hu]
        _ = 0 := by simp
    rw [hint, hleft.2]
    simp
  · rcases hrest with hright | hinside
    · have henvelope : ∀ u ∈ Icc r s,
          suzukiServiceDecayEnvelope r K u = K - suzukiRootService r u := by
        intro u hu
        apply serviceDecayEnvelope_eq_untruncated
        exact (suzukiRootService_mono_right hr (show u ∈ Ici r from hu.1)
          (show s ∈ Ici r from hrs) hu.2).trans hright.2.1
      rw [hright.2.2]
      calc
        (∫ u in r..s, 2 / u * suzukiServiceDecayEnvelope r K u) =
            ∫ u in r..s, 2 / u * (K - suzukiRootService r u) := by
              apply intervalIntegral.integral_congr
              intro u hu
              rw [uIcc_of_le hrs] at hu
              change 2 / u * suzukiServiceDecayEnvelope r K u =
                2 / u * (K - suzukiRootService r u)
              rw [henvelope u hu]
        _ = _ := integral_serviceDecay_untruncated hr hrs
    · have hrh := hcut.1.1
      have hhs := hcut.1.2
      have henvelopeLeft : ∀ u ∈ Icc r h,
          suzukiServiceDecayEnvelope r K u = K - suzukiRootService r u := by
        intro u hu
        apply serviceDecayEnvelope_eq_untruncated
        have hmono := suzukiRootService_mono_right hr (show u ∈ Ici r from hu.1)
          (show h ∈ Ici r from hrh) hu.2
        simpa [hinside.2.2] using hmono
      have henvelopeRight : ∀ u ∈ Icc h s,
          suzukiServiceDecayEnvelope r K u = 0 := by
        intro u hu
        apply serviceDecayEnvelope_eq_zero
        have hmono := suzukiRootService_mono_right hr
          (show h ∈ Ici r from hrh) (show u ∈ Ici r from hrh.trans hu.1) hu.1
        simpa [hinside.2.2] using hmono
      have hfullInt := intervalIntegrable_weighted_serviceDecayEnvelope
        (K := K) hr hrs
      have hleftSubset : uIcc r h ⊆ uIcc r s := by
        rw [uIcc_of_le hrh, uIcc_of_le hrs]
        exact Icc_subset_Icc le_rfl hhs
      have hrightSubset : uIcc h s ⊆ uIcc r s := by
        rw [uIcc_of_le hhs, uIcc_of_le hrs]
        exact Icc_subset_Icc hrh le_rfl
      have hleftInt := hfullInt.mono_set hleftSubset
      have hrightInt := hfullInt.mono_set hrightSubset
      rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
      have hleftEq :
          (∫ u in r..h, 2 / u * suzukiServiceDecayEnvelope r K u) =
            ∫ u in r..h, 2 / u * (K - suzukiRootService r u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hrh] at hu
        change 2 / u * suzukiServiceDecayEnvelope r K u =
          2 / u * (K - suzukiRootService r u)
        rw [henvelopeLeft u hu]
      have hrightEq :
          (∫ u in h..s, 2 / u * suzukiServiceDecayEnvelope r K u) = 0 := by
        calc
          (∫ u in h..s, 2 / u * suzukiServiceDecayEnvelope r K u) =
              ∫ _u in h..s, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro u hu
                rw [uIcc_of_le hhs] at hu
                simp [henvelopeRight u hu]
          _ = 0 := by simp
      rw [hleftEq, hrightEq, add_zero]
      exact integral_serviceDecay_untruncated hr hrh

/-- Exact finite cell cost, with its implicit cutoff certified by monotone
service rather than by a numerical root finder. -/
noncomputable def suzukiExactServiceCellCost (r s K : ℝ) : ℝ :=
  let h := suzukiServiceCutoff r s K
  2 * (K + suzukiRootArchSlope r) * Real.log (h / r) -
    suzukiPsiArchimedean (2 * Real.log h) +
    suzukiPsiArchimedean (2 * Real.log r)

theorem integral_serviceDecayEnvelope_eq_exactCellCost
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    (∫ u in r..s, 2 / u * suzukiServiceDecayEnvelope r K u) =
      suzukiExactServiceCellCost r s K := by
  exact integral_serviceDecayEnvelope_eq_cutoffCost hr hrs
    (suzukiServiceCutoff_spec hr hrs)

theorem five_thirds_mul_sub_le_rootService
    {r u : ℝ} (hr : Real.sqrt 2 ≤ r) (hru : r ≤ u) :
    (5 / 3 : ℝ) * (u - r) ≤ suzukiRootService r u := by
  rcases hru.eq_or_lt with rfl | hlt
  · simp [suzukiRootService]
  · exact (suzukiRootService_bounds hr hlt).1

/-- Explicit conservative envelope obtained by replacing the true service
with its checked lower drift `(5/3)(u-r)`. -/
noncomputable def suzukiLinearServiceEnvelope (r K u : ℝ) : ℝ :=
  max (K - (5 / 3 : ℝ) * (u - r)) 0

theorem serviceDecayEnvelope_le_linear
    {r K u : ℝ} (hr : Real.sqrt 2 ≤ r) (hru : r ≤ u) :
    suzukiServiceDecayEnvelope r K u ≤ suzukiLinearServiceEnvelope r K u := by
  unfold suzukiServiceDecayEnvelope suzukiLinearServiceEnvelope
  apply max_le_max_right
  linarith [five_thirds_mul_sub_le_rootService hr hru]

/-- Explicit cutoff for the linear `(5/3)` service envelope. -/
noncomputable def suzukiLinearServiceCutoff (r s K : ℝ) : ℝ :=
  if K ≤ 0 then r else min s (r + 3 * K / 5)

/-- Closed-form conservative cell cost. -/
noncomputable def suzukiLinearServiceCellCost (r s K : ℝ) : ℝ :=
  let h := suzukiLinearServiceCutoff r s K
  2 * (K + (5 / 3 : ℝ) * r) * Real.log (h / r) -
    (10 / 3 : ℝ) * (h - r)

private theorem integral_linearService_untruncated
    {r h K : ℝ} (hr : 0 < r) (hrh : r ≤ h) :
    (∫ u in r..h, 2 / u * (K - (5 / 3 : ℝ) * (u - r))) =
      2 * (K + (5 / 3 : ℝ) * r) * Real.log (h / r) -
        (10 / 3 : ℝ) * (h - r) := by
  let primitive : ℝ → ℝ := fun u =>
    2 * (K + (5 / 3 : ℝ) * r) * Real.log u - (10 / 3 : ℝ) * u
  have hcont : ContinuousOn primitive (Icc r h) := by
    intro u hu
    have hu0 : 0 < u := hr.trans_le hu.1
    exact ((continuousAt_const.mul (Real.continuousAt_log hu0.ne')).sub
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hderiv : ∀ u ∈ Ioo r h, HasDerivAt primitive
      (2 / u * (K - (5 / 3 : ℝ) * (u - r))) u := by
    intro u hu
    have hu0 : 0 < u := hr.trans_le hu.1.le
    have hlog := (Real.hasDerivAt_log hu0.ne').const_mul
      (2 * (K + (5 / 3 : ℝ) * r))
    have hlin := (hasDerivAt_id u).const_mul (10 / 3 : ℝ)
    have hp := hlog.sub hlin
    change HasDerivAt primitive _ u
    apply hp.congr_deriv
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun u => 2 / u * (K - (5 / 3 : ℝ) * (u - r))) volume r h := by
    apply ContinuousOn.intervalIntegrable_of_Icc hrh
    intro u hu
    have hu0 : 0 < u := hr.trans_le hu.1
    exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
      (continuousAt_const.sub
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrh hcont hderiv hint]
  dsimp [primitive]
  have hh0 : h ≠ 0 := ne_of_gt (hr.trans_le hrh)
  rw [Real.log_div hh0 hr.ne']
  ring

/-- The conservative linear envelope is still integrated with the exact
`2/u` weight; it is not a worst-case rectangle. -/
theorem integral_linearServiceEnvelope_eq_cellCost
    {r s K : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    (∫ u in r..s, 2 / u * suzukiLinearServiceEnvelope r K u) =
      suzukiLinearServiceCellCost r s K := by
  by_cases hK : K ≤ 0
  · have hzero : ∀ u ∈ Icc r s, suzukiLinearServiceEnvelope r K u = 0 := by
      intro u hu
      unfold suzukiLinearServiceEnvelope
      rw [max_eq_right]
      norm_num [div_eq_mul_inv] at *
      nlinarith
    have hint : (∫ u in r..s, 2 / u * suzukiLinearServiceEnvelope r K u) = 0 := by
      calc
        (∫ u in r..s, 2 / u * suzukiLinearServiceEnvelope r K u) =
            ∫ _u in r..s, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro u hu
              rw [uIcc_of_le hrs] at hu
              simp [hzero u hu]
        _ = 0 := by simp
    rw [hint]
    simp [suzukiLinearServiceCellCost, suzukiLinearServiceCutoff, hK]
  · have hKpos : 0 < K := lt_of_not_ge hK
    by_cases hcut : r + 3 * K / 5 ≤ s
    · let h := r + 3 * K / 5
      have hrh : r ≤ h := by dsimp [h]; linarith
      have hhs : h ≤ s := hcut
      have hleft : ∀ u ∈ Icc r h,
          suzukiLinearServiceEnvelope r K u =
            K - (5 / 3 : ℝ) * (u - r) := by
        intro u hu
        unfold suzukiLinearServiceEnvelope
        rw [max_eq_left]
        dsimp [h] at hu
        norm_num [div_eq_mul_inv] at *
        nlinarith
      have hright : ∀ u ∈ Icc h s,
          suzukiLinearServiceEnvelope r K u = 0 := by
        intro u hu
        unfold suzukiLinearServiceEnvelope
        rw [max_eq_right]
        dsimp [h] at hu
        norm_num [div_eq_mul_inv] at *
        nlinarith
      have hInt : IntervalIntegrable
          (fun u => 2 / u * suzukiLinearServiceEnvelope r K u) volume r s := by
        apply ContinuousOn.intervalIntegrable_of_Icc hrs
        intro u hu
        have hu0 : 0 < u := hr.trans_le hu.1
        exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
          ((continuousAt_const.sub
            (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))).max
              continuousAt_const)).continuousWithinAt
      have hleftInt := hInt.mono_set (by
        rw [uIcc_of_le hrh, uIcc_of_le hrs]
        exact Icc_subset_Icc le_rfl hhs)
      have hrightInt := hInt.mono_set (by
        rw [uIcc_of_le hhs, uIcc_of_le hrs]
        exact Icc_subset_Icc hrh le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
      have hleftEq :
          (∫ u in r..h, 2 / u * suzukiLinearServiceEnvelope r K u) =
            ∫ u in r..h, 2 / u * (K - (5 / 3 : ℝ) * (u - r)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hrh] at hu
        change 2 / u * suzukiLinearServiceEnvelope r K u = _
        rw [hleft u hu]
      have hrightEq :
          (∫ u in h..s, 2 / u * suzukiLinearServiceEnvelope r K u) = 0 := by
        calc
          (∫ u in h..s, 2 / u * suzukiLinearServiceEnvelope r K u) =
              ∫ _u in h..s, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro u hu
                rw [uIcc_of_le hhs] at hu
                simp [hright u hu]
          _ = 0 := by simp
      rw [hleftEq, hrightEq, add_zero,
        integral_linearService_untruncated hr hrh]
      dsimp [h]
      simp [suzukiLinearServiceCellCost, suzukiLinearServiceCutoff, hK,
        min_eq_right hcut]
    · have hscut : s < r + 3 * K / 5 := lt_of_not_ge hcut
      have hall : ∀ u ∈ Icc r s,
          suzukiLinearServiceEnvelope r K u =
            K - (5 / 3 : ℝ) * (u - r) := by
        intro u hu
        unfold suzukiLinearServiceEnvelope
        rw [max_eq_left]
        norm_num [div_eq_mul_inv] at *
        nlinarith
      calc
        (∫ u in r..s, 2 / u * suzukiLinearServiceEnvelope r K u) =
            ∫ u in r..s, 2 / u * (K - (5 / 3 : ℝ) * (u - r)) := by
              apply intervalIntegral.integral_congr
              intro u hu
              rw [uIcc_of_le hrs] at hu
              change 2 / u * suzukiLinearServiceEnvelope r K u = _
              rw [hall u hu]
        _ = _ := by
          rw [integral_linearService_untruncated hr hrs]
          simp [suzukiLinearServiceCellCost, suzukiLinearServiceCutoff, hK,
            min_eq_left hscut.le]

theorem exactServiceCellCost_le_linearCellCost
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    suzukiExactServiceCellCost r s K ≤ suzukiLinearServiceCellCost r s K := by
  rw [← integral_serviceDecayEnvelope_eq_exactCellCost hr hrs,
    ← integral_linearServiceEnvelope_eq_cellCost
      ((Real.sqrt_pos.2 (by norm_num)).trans_le hr) hrs]
  apply intervalIntegral.integral_mono_on hrs
    (intervalIntegrable_weighted_serviceDecayEnvelope (K := K) hr hrs)
  · apply ContinuousOn.intervalIntegrable_of_Icc hrs
    intro u hu
    have hu0 : 0 < u := (Real.sqrt_pos.2 (by norm_num)).trans_le (hr.trans hu.1)
    exact ((continuousAt_const.div continuousAt_id hu0.ne').mul
      ((continuousAt_const.sub
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))).max
          continuousAt_const)).continuousWithinAt
  · intro u hu
    exact mul_le_mul_of_nonneg_left
      (serviceDecayEnvelope_le_linear hr hu.1)
      (div_nonneg (by norm_num) ((Real.sqrt_nonneg 2).trans (hr.trans hu.1)))

theorem exactServiceCellCost_at_eventState_eq_cutoffLoss
    {q r : ℕ} (h : IsMangoldtBlock q r) :
    suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt r)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt q)) =
      suzukiPsiRoot (Real.sqrt q) -
        suzukiPsiRoot (suzukiServiceCutoff (Real.sqrt q) (Real.sqrt r)
          (-suzukiRootSlopeDiscrepancy (Real.sqrt q))) := by
  let a := Real.sqrt q
  let b := Real.sqrt r
  let K := -suzukiRootSlopeDiscrepancy a
  let c := suzukiServiceCutoff a b K
  have hq2 := h.left_event.two_le
  have ha0 : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)
  have hb0 : 0 < b := Real.sqrt_pos.2 (by exact_mod_cast h.right_pos)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast h.left_lt.le)
  have hacb : c ∈ Icc a b :=
    (suzukiServiceCutoff_spec
      (Real.sqrt_le_sqrt (by exact_mod_cast hq2)) hab).1
  have hloga : 2 * Real.log a = Real.log q := by
    dsimp [a]
    rw [Real.log_sqrt (Nat.cast_nonneg q)]
    ring
  have hlogb : 2 * Real.log b = Real.log r := by
    dsimp [b]
    rw [Real.log_sqrt (Nat.cast_nonneg r)]
    ring
  have hc0 : 0 < c := ha0.trans_le hacb.1
  have htq : Real.log q ≤ 2 * Real.log c := by
    rw [← hloga]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log ha0 hacb.1) (by norm_num)
  have htr : 2 * Real.log c ≤ Real.log r := by
    rw [← hlogb]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hc0 hacb.2) (by norm_num)
  have hpsiA : suzukiPsiRoot a =
      suzukiPsiArchimedean (2 * Real.log a) -
        suzukiMangoldtSlope q * (2 * Real.log a) +
          suzukiMangoldtIntercept q := by
    unfold suzukiPsiRoot
    have hlogqr : Real.log (q : ℝ) ≤ Real.log (r : ℝ) :=
      Real.log_le_log (by exact_mod_cast h.left_pos)
        (by exact_mod_cast h.left_lt.le)
    rw [suzukiPsi_eq_mangoldtBlock h hloga.ge (hloga.le.trans hlogqr)]
  have hpsiC : suzukiPsiRoot c =
      suzukiPsiArchimedean (2 * Real.log c) -
        suzukiMangoldtSlope q * (2 * Real.log c) +
          suzukiMangoldtIntercept q := by
    unfold suzukiPsiRoot
    rw [suzukiPsi_eq_mangoldtBlock h htq htr]
  have hdq := suzukiRootSlopeDiscrepancy_eq_on_block h
    (u := a) le_rfl (Real.sqrt_lt_sqrt (Nat.cast_nonneg q)
      (by exact_mod_cast h.left_lt))
  change suzukiExactServiceCellCost a b K = suzukiPsiRoot a - suzukiPsiRoot c
  rw [hpsiA, hpsiC]
  unfold suzukiExactServiceCellCost
  change 2 * (K + suzukiRootArchSlope a) * Real.log (c / a) -
      suzukiPsiArchimedean (2 * Real.log c) +
        suzukiPsiArchimedean (2 * Real.log a) = _
  have hK : K + suzukiRootArchSlope a = suzukiMangoldtSlope q := by
    dsimp [K]
    rw [hdq]
    ring
  rw [hK, Real.log_div hc0.ne' ha0.ne']
  ring

theorem suzukiExactServiceCellCost_nonneg
    {r s K : ℝ} (hr : Real.sqrt 2 ≤ r) (hrs : r ≤ s) :
    0 ≤ suzukiExactServiceCellCost r s K := by
  rw [← integral_serviceDecayEnvelope_eq_exactCellCost hr hrs]
  apply intervalIntegral.integral_nonneg hrs
  intro u hu
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg 2).trans (hr.trans hu.1)
  exact mul_nonneg (div_nonneg (by norm_num) hu0)
    (le_max_right _ _)

/-- On one complete event block, a single event-prefix bound charges the
actual `2/u`-weighted loss by the exact service-decay cell cost.  No
negative-excursion hypothesis is needed: this is a net-loss inequality, not
an equality with downward variation. -/
theorem psiRoot_loss_le_exactServiceCellCost
    {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q)
    (h : IsMangoldtBlock q r) {e u : ℝ}
    (he : suzukiArrivalServiceExcess m q ≤ e)
    (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u ≤
      suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt r)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt m) + e) := by
  let K := -suzukiRootSlopeDiscrepancy (Real.sqrt m) + e
  have hq2 : 2 ≤ q := hm.trans hmq
  have hroot : Real.sqrt 2 ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast hq2)
  have hsqr : Real.sqrt q ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt (by exact_mod_cast h.left_lt.le)
  have harea := suzukiPsiRoot_sub_eq_integral_discrepancy_on_block h
    (a := Real.sqrt q) (b := u) le_rfl hqu hur
  have hblockIntegral :
      suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u =
        ∫ v in Real.sqrt q..u,
          2 / v * (suzukiMangoldtSlope q - suzukiRootArchSlope v) := by
    have hreplace :
        (∫ v in Real.sqrt q..u, 2 / v * suzukiRootSlopeDiscrepancy v) =
          ∫ v in Real.sqrt q..u,
            2 / v * (suzukiRootArchSlope v - suzukiMangoldtSlope q) := by
      apply intervalIntegral.integral_congr_uIoo
      intro v hv
      rw [uIoo_of_le hqu] at hv
      change 2 / v * suzukiRootSlopeDiscrepancy v =
        2 / v * (suzukiRootArchSlope v - suzukiMangoldtSlope q)
      rw [suzukiRootSlopeDiscrepancy_eq_on_block h hv.1.le
        (hv.2.trans_le hur)]
    rw [hreplace] at harea
    rw [← neg_sub, harea, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro v _
    change -(2 / v * (suzukiRootArchSlope v - suzukiMangoldtSlope q)) =
      2 / v * (suzukiMangoldtSlope q - suzukiRootArchSlope v)
    ring
  have hstateQ : -suzukiRootSlopeDiscrepancy (Real.sqrt q) ≤ K := by
    have hmroot : Real.sqrt m ≤ Real.sqrt q :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmq)
    have hsigned := suzukiSignedRootState_eq_neg_discrepancy
      (m := m) (u := Real.sqrt q) (hm.trans' (by norm_num)) hmroot
    rw [← hsigned]
    unfold suzukiSignedRootState suzukiSignedArrivalServiceExcess
    rw [Real.sq_sqrt (Nat.cast_nonneg q), Nat.floor_natCast]
    change -suzukiRootSlopeDiscrepancy (Real.sqrt m) +
      suzukiArrivalServiceExcess m q ≤ K
    dsimp [K]
    linarith
  have hdq := suzukiRootSlopeDiscrepancy_eq_on_block h
    (u := Real.sqrt q) le_rfl
    (Real.sqrt_lt_sqrt (Nat.cast_nonneg q) (by exact_mod_cast h.left_lt))
  have hlowerInt : IntervalIntegrable
      (fun v => 2 / v * (suzukiMangoldtSlope q - suzukiRootArchSlope v))
      volume (Real.sqrt q) u := by
    apply ContinuousOn.intervalIntegrable_of_Icc hqu
    intro v hv
    have hv0 : 0 < v := (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos)).trans_le hv.1
    exact ((continuousAt_const.div continuousAt_id hv0.ne').mul
      (continuousAt_const.sub
        (hasDerivAt_suzukiRootArchSlope (hroot.trans hv.1)).continuousAt)).continuousWithinAt
  have hupperFull := intervalIntegrable_weighted_serviceDecayEnvelope
    (K := K) hroot hsqr
  have hsubset : uIcc (Real.sqrt q) u ⊆
      uIcc (Real.sqrt q) (Real.sqrt r) := by
    rw [uIcc_of_le hqu, uIcc_of_le hsqr]
    exact Icc_subset_Icc le_rfl hur
  have hupperInt := hupperFull.mono_set hsubset
  have hintegral :
      (∫ v in Real.sqrt q..u,
        2 / v * (suzukiMangoldtSlope q - suzukiRootArchSlope v)) ≤
      ∫ v in Real.sqrt q..u,
        2 / v * suzukiServiceDecayEnvelope (Real.sqrt q) K v := by
    apply intervalIntegral.integral_mono_on hqu hlowerInt hupperInt
    intro v hv
    have hv0 : 0 ≤ v := (Real.sqrt_nonneg q).trans hv.1
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hv0)
    have hidentity : suzukiMangoldtSlope q - suzukiRootArchSlope v =
        -suzukiRootSlopeDiscrepancy (Real.sqrt q) -
          suzukiRootService (Real.sqrt q) v := by
      rw [hdq]
      unfold suzukiRootService
      ring
    rw [hidentity]
    exact le_trans (sub_le_sub_right hstateQ _)
      (le_max_left _ _)
  have hpartialNonneg : ∀ v ∈ Icc (Real.sqrt q) (Real.sqrt r),
      0 ≤ 2 / v * suzukiServiceDecayEnvelope (Real.sqrt q) K v := by
    intro v hv
    exact mul_nonneg (div_nonneg (by norm_num) ((Real.sqrt_nonneg q).trans hv.1))
      (le_max_right _ _)
  have hpartial :
      (∫ v in Real.sqrt q..u,
        2 / v * suzukiServiceDecayEnvelope (Real.sqrt q) K v) ≤
      ∫ v in Real.sqrt q..Real.sqrt r,
        2 / v * suzukiServiceDecayEnvelope (Real.sqrt q) K v := by
    apply intervalIntegral.integral_mono_interval le_rfl hqu hur
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      exact hpartialNonneg v ⟨hv.1.le, hv.2⟩
    · exact hupperFull
  rw [hblockIntegral]
  refine hintegral.trans (hpartial.trans ?_)
  exact le_of_eq (integral_serviceDecayEnvelope_eq_exactCellCost hroot hsqr)

/-! ## Genuinely finite event-profile certificates -/

/-- A finite chain of consecutive Mangoldt blocks.  The constructors encode
event completeness: a chain cannot skip a prime-power event. -/
inductive SuzukiMangoldtBlockChain : ℕ → ℕ → Type
  | single {q r : ℕ} (block : IsMangoldtBlock q r) :
      SuzukiMangoldtBlockChain q r
  | cons {q r s : ℕ} (block : IsMangoldtBlock q r)
      (tail : SuzukiMangoldtBlockChain r s) :
      SuzukiMangoldtBlockChain q s

namespace SuzukiMangoldtBlockChain

def eventBounds {q r : ℕ} (anchor : ℕ) (e : ℕ → ℝ) :
    SuzukiMangoldtBlockChain q r → Prop
  | .single block => suzukiArrivalServiceExcess anchor q ≤ e q
  | .cons block tail =>
      suzukiArrivalServiceExcess anchor q ≤ e q ∧ tail.eventBounds anchor e

noncomputable def exactCost {q r : ℕ} (anchor : ℕ) (e : ℕ → ℝ) :
    SuzukiMangoldtBlockChain q r → ℝ
  | .single block =>
      suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt r)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt anchor) + e q)
  | @SuzukiMangoldtBlockChain.cons q p r block tail =>
      suzukiExactServiceCellCost (Real.sqrt q) (Real.sqrt p)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt anchor) + e q) +
          tail.exactCost anchor e

theorem left_le_right {q r : ℕ} (chain : SuzukiMangoldtBlockChain q r) : q < r := by
  induction chain with
  | single block => exact block.left_lt
  | cons block tail ih => exact block.left_lt.trans ih

theorem exactCost_nonneg {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q)
    (e : ℕ → ℝ) (chain : SuzukiMangoldtBlockChain q r) :
    0 ≤ chain.exactCost m e := by
  induction chain with
  | single block =>
      exact suzukiExactServiceCellCost_nonneg
        (Real.sqrt_le_sqrt (by exact_mod_cast hm.trans hmq))
        (Real.sqrt_le_sqrt (by exact_mod_cast block.left_lt.le))
  | @cons q p r block tail ih =>
      apply add_nonneg
      · exact suzukiExactServiceCellCost_nonneg
          (Real.sqrt_le_sqrt (by exact_mod_cast hm.trans hmq))
          (Real.sqrt_le_sqrt (by exact_mod_cast block.left_lt.le))
      · exact ih (hmq.trans block.left_lt.le)

theorem loss_le_exactCost {m q r : ℕ} (hm : 2 ≤ m) (hmq : m ≤ q)
    {e : ℕ → ℝ} (chain : SuzukiMangoldtBlockChain q r)
    (hbounds : chain.eventBounds m e) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u ≤ Real.sqrt r) :
    suzukiPsiRoot (Real.sqrt q) - suzukiPsiRoot u ≤ chain.exactCost m e := by
  induction chain generalizing u with
  | single block =>
      exact psiRoot_loss_le_exactServiceCellCost hm hmq block hbounds hqu hur
  | @cons q p r block tail ih =>
      rcases hbounds with ⟨hqbound, htailBounds⟩
      have hqp : Real.sqrt q ≤ Real.sqrt p :=
        Real.sqrt_le_sqrt (by exact_mod_cast block.left_lt.le)
      rcases le_total u (Real.sqrt p) with hup | hpu
      · have hlocal := psiRoot_loss_le_exactServiceCellCost hm hmq block hqbound hqu hup
        exact hlocal.trans (le_add_of_nonneg_right
          (tail.exactCost_nonneg hm (hmq.trans block.left_lt.le) e))
      · have hlocal := psiRoot_loss_le_exactServiceCellCost hm hmq block hqbound
          hqp le_rfl
        have htail := ih (hmq.trans block.left_lt.le) htailBounds hpu hur
        have hadd := add_le_add hlocal htail
        simpa [exactCost] using hadd

end SuzukiMangoldtBlockChain

/-- A finite event-indexed certificate.  Arithmetic inequalities are needed
only at the finitely many left-event roots represented by `chain`; the
between-event interpolation, integrability, and weighted costs are theorems,
not structure fields. -/
structure SuzukiFiniteEventProfileCertificate where
  startEvent : ℕ
  endEvent : ℕ
  terminalRoot : ℝ
  profileBound : ℕ → ℝ
  reserveLower : ℝ
  start_ge_two : 2 ≤ startEvent
  chain : SuzukiMangoldtBlockChain startEvent endEvent
  terminal_mem : terminalRoot ∈ Icc (Real.sqrt startEvent) (Real.sqrt endEvent)
  event_bounds : chain.eventBounds startEvent profileBound
  reserve_bound : reserveLower ≤ suzukiPsiRoot (Real.sqrt startEvent)
  total_cost_safe : chain.exactCost startEvent profileBound ≤ reserveLower

theorem SuzukiFiniteEventProfileCertificate.psiRoot_nonnegative
    (certificate : SuzukiFiniteEventProfileCertificate) :
    ∀ u ∈ Icc (Real.sqrt certificate.startEvent) certificate.terminalRoot,
      0 ≤ suzukiPsiRoot u := by
  intro u hu
  have hur : u ≤ Real.sqrt certificate.endEvent :=
    hu.2.trans certificate.terminal_mem.2
  have hloss := certificate.chain.loss_le_exactCost certificate.start_ge_two le_rfl
    certificate.event_bounds hu.1 hur
  linarith [certificate.total_cost_safe, certificate.reserve_bound]

/-- Compatibility with the earlier generic busy-period interface.  The
continuum loss field of that interface is discharged here by the finite
chain theorem rather than assumed as certificate input. -/
noncomputable def SuzukiFiniteEventProfileCertificate.toBusyPeriodCertificate
    (certificate : SuzukiFiniteEventProfileCertificate) :
    SuzukiBusyPeriodCertificate where
  startRoot := Real.sqrt certificate.startEvent
  endRoot := certificate.terminalRoot
  reserveLower := certificate.reserveLower
  lossUpper := certificate.chain.exactCost certificate.startEvent
    certificate.profileBound
  roots_ordered := certificate.terminal_mem.1
  reserve_bound := certificate.reserve_bound
  loss_bound := by
    intro u hu
    exact certificate.chain.loss_le_exactCost certificate.start_ge_two le_rfl
      certificate.event_bounds hu.1 (hu.2.trans certificate.terminal_mem.2)
  safe := certificate.total_cost_safe

theorem SuzukiFiniteEventProfileCertificate.compatible_busyPeriod_nonnegative
    (certificate : SuzukiFiniteEventProfileCertificate) :
    ∀ u ∈ Icc (Real.sqrt certificate.startEvent) certificate.terminalRoot,
      0 ≤ suzukiPsiRoot u :=
  certificate.toBusyPeriodCertificate.psiRoot_nonnegative

theorem isMangoldtBlock_two_three : IsMangoldtBlock 2 3 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [isMangoldtEvent_iff_primePower]
    exact Nat.prime_two.isPrimePow
  · rw [isMangoldtEvent_iff_primePower]
    exact Nat.prime_three.isPrimePow
  · intro k hk2 hk3
    omega

private theorem cellTwo_exactCost_lt_startReserve :
    suzukiExactServiceCellCost (Real.sqrt 2) (Real.sqrt 3)
        (-suzukiRootSlopeDiscrepancy (Real.sqrt 2)) <
      suzukiPsiRoot (Real.sqrt 2) := by
  let c := suzukiServiceCutoff (Real.sqrt 2) (Real.sqrt 3)
    (-suzukiRootSlopeDiscrepancy (Real.sqrt 2))
  have hc := (suzukiServiceCutoff_spec
    (K := -suzukiRootSlopeDiscrepancy (Real.sqrt 2))
    (show Real.sqrt 2 ≤ Real.sqrt 2 from le_rfl)
    (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 3))).1
  have hc0 : 0 < c := (Real.sqrt_pos.2 (by norm_num)).trans_le hc.1
  have hlog2 : Real.log 2 ≤ 2 * Real.log c := by
    rw [← show 2 * Real.log (Real.sqrt 2) = Real.log 2 by
      rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (Real.sqrt_pos.2 (by norm_num)) hc.1) (by norm_num)
  have hlog3 : 2 * Real.log c ≤ Real.log 3 := by
    rw [← show 2 * Real.log (Real.sqrt 3) = Real.log 3 by
      rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hc0 hc.2) (by norm_num)
  have hpos : 0 < suzukiPsiRoot c := by
    exact suzukiPsi_pos_cell_two (2 * Real.log c) hlog2 hlog3
  have hcost := exactServiceCellCost_at_eventState_eq_cutoffLoss
    (q := 2) (r := 3) isMangoldtBlock_two_three
  norm_num at hcost
  rw [hcost]
  change suzukiPsiRoot (Real.sqrt 2) - suzukiPsiRoot c <
    suzukiPsiRoot (Real.sqrt 2)
  linarith

/-- First concrete inhabitant of the finite-event interface.  It re-certifies
the already checked second prime cell, now using a finite event table and the
new gluing/cost theorem.  It is finite evidence only and is not a tail
certificate. -/
noncomputable def suzukiFiniteEventCertificate_cellTwo :
    SuzukiFiniteEventProfileCertificate where
  startEvent := 2
  endEvent := 3
  terminalRoot := Real.sqrt 3
  profileBound := fun _ => 0
  reserveLower := suzukiExactServiceCellCost (Real.sqrt 2) (Real.sqrt 3)
    (-suzukiRootSlopeDiscrepancy (Real.sqrt 2))
  start_ge_two := le_rfl
  chain := .single isMangoldtBlock_two_three
  terminal_mem := ⟨Real.sqrt_le_sqrt (by norm_num), le_rfl⟩
  event_bounds := by
    change suzukiArrivalServiceExcess 2 2 ≤ 0
    simp [suzukiArrivalServiceExcess, suzukiWeightedMangoldtInterval,
      suzukiRootService]
  reserve_bound := cellTwo_exactCost_lt_startReserve.le
  total_cost_safe := by
    simp [SuzukiMangoldtBlockChain.exactCost]

theorem suzukiFiniteEventCertificate_cellTwo_nonnegative :
    ∀ u ∈ Icc (Real.sqrt 2) (Real.sqrt 3), 0 ≤ suzukiPsiRoot u :=
  by simpa [suzukiFiniteEventCertificate_cellTwo] using
    suzukiFiniteEventCertificate_cellTwo.psiRoot_nonnegative

/-! ## Jump-aware arithmetic envelopes -/

theorem suzukiChebyshevPsi_eq_left_of_eventFree
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) {x : ℝ}
    (hqx : (q : ℝ) ≤ x) (hxr : x < r) :
    suzukiChebyshevPsi x = suzukiChebyshevPsi q := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg q).trans hqx
  have hqfloor : q ≤ ⌊x⌋₊ := Nat.le_floor hqx
  have hfloorR : ⌊x⌋₊ < r := (Nat.floor_lt hx0).2 hxr
  unfold suzukiChebyshevPsi
  rw [Nat.floor_natCast]
  symm
  apply Finset.sum_subset
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨hk'.1, hk'.2.trans hqfloor⟩
  · intro k hkBig hkSmall
    have hk' := Finset.mem_Ioc.mp hkBig
    have hqk : q < k := lt_of_not_ge fun hkq =>
      hkSmall (Finset.mem_Ioc.mpr ⟨hk'.1, hkq⟩)
    exact h.2 k hqk (hk'.2.trans_lt hfloorR)

/-- Between consecutive Mangoldt events the Chebyshev function is constant.
Consequently a proved one-sided sample bound gives an affine envelope of
slope `-1` on the full half-open arithmetic cell. -/
theorem suzukiChebyshevError_le_jumpAwareEnvelope
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) {rho x : ℝ}
    (hsample : suzukiChebyshevError q ≤ rho)
    (hqx : (q : ℝ) ≤ x) (hxr : x < r) :
    suzukiChebyshevError x ≤ q + rho - x := by
  have hpsi := suzukiChebyshevPsi_eq_left_of_eventFree h hqx hxr
  unfold suzukiChebyshevError at hsample ⊢
  rw [hpsi]
  norm_num at hsample ⊢
  linarith

/-- The exact event sample itself produces equality on an event-free cell.
This is a structural identity; evaluating the sample numerically remains
`NumericalEvidence` until its bound is proved in Lean. -/
theorem suzukiChebyshevError_eq_jumpAwareSample
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) {x : ℝ}
    (hqx : (q : ℝ) ≤ x) (hxr : x < r) :
    suzukiChebyshevError x =
      q + suzukiChebyshevError q - x := by
  have hpsi := suzukiChebyshevPsi_eq_left_of_eventFree h hqx hxr
  unfold suzukiChebyshevError
  rw [hpsi]
  norm_num

/-- A genuinely conservative local coarsening: an exact event sample may be
raised by any proved nonnegative allowance without smearing the slope `-1`
between jumps. -/
theorem suzukiChebyshevError_le_jumpAwareCoarsening
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) {allowance x : ℝ}
    (hallowance : 0 ≤ allowance)
    (hqx : (q : ℝ) ≤ x) (hxr : x < r) :
    suzukiChebyshevError x ≤
      q + (suzukiChebyshevError q + allowance) - x := by
  rw [suzukiChebyshevError_eq_jumpAwareSample h hqx hxr]
  linarith

/-- Elementary transformed-profile cost of one affine jump-aware envelope.
This is the exact `1/u²` integral, not a numerical quadrature. -/
theorem integral_jumpAwareChebyshevCell
    {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, C / u ^ 2 - 1) =
      C * (1 / a - 1 / b) - (b - a) := by
  let primitive : ℝ → ℝ := fun u => -C * u⁻¹ - u
  have hcont : ContinuousOn primitive (Icc a b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
    exact ((continuousAt_const.mul (continuousAt_inv₀ hu0)).sub
      continuousAt_id).continuousWithinAt
  have hderiv : ∀ u ∈ Ioo a b, HasDerivAt primitive (C / u ^ 2 - 1) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1.le)
    have hp := ((hasDerivAt_inv hu0).const_mul (-C)).sub (hasDerivAt_id u)
    apply hp.congr_deriv
    field_simp
  have hint : IntervalIntegrable (fun u => C / u ^ 2 - 1) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
    exact ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hu0)).sub
      continuousAt_const).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint]
  dsimp [primitive]
  field_simp [ne_of_gt ha, ne_of_gt (ha.trans_le hab)]
  ring

theorem integral_jumpAwareChebyshevEventCell
    {q r : ℕ} (hq : 0 < q) (hqr : q ≤ r) (rho : ℝ) :
    (∫ u in Real.sqrt q..Real.sqrt r,
      ((q : ℝ) + rho) / u ^ 2 - 1) =
      ((q : ℝ) + rho) *
          (1 / Real.sqrt q - 1 / Real.sqrt r) -
        (Real.sqrt r - Real.sqrt q) := by
  exact integral_jumpAwareChebyshevCell (Real.sqrt_pos.2 (by exact_mod_cast hq))
    (Real.sqrt_le_sqrt (by exact_mod_cast hqr))

/-- A concrete proved conservative jump-aware envelope.  It keeps the exact
event sample at `2` and adds the rational allowance `1/1000`; unlike the
Explorer's rounded samples, this statement has no floating-point premise. -/
theorem suzukiChebyshevError_le_jumpAware_two_three {x : ℝ}
    (h2x : (2 : ℝ) ≤ x) (hx3 : x < 3) :
    suzukiChebyshevError x ≤
      2 + (suzukiChebyshevError 2 + (1 / 1000 : ℝ)) - x := by
  exact suzukiChebyshevError_le_jumpAwareCoarsening
    (isSuzukiEventFreeCell_of_mangoldtBlock isMangoldtBlock_two_three)
    (by norm_num) h2x hx3

theorem integral_jumpAwareChebyshev_two_three :
    (∫ u in Real.sqrt 2..Real.sqrt 3,
      ((2 : ℝ) + (suzukiChebyshevError 2 + (1 / 1000 : ℝ))) / u ^ 2 - 1) =
      ((2 : ℝ) + (suzukiChebyshevError 2 + (1 / 1000 : ℝ))) *
          (1 / Real.sqrt 2 - 1 / Real.sqrt 3) -
        (Real.sqrt 3 - Real.sqrt 2) := by
  exact integral_jumpAwareChebyshevEventCell (by norm_num) (by norm_num) _

end RHGarden
