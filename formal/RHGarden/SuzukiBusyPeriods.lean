import RHGarden.SuzukiRootDiscrepancy

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

namespace RHGarden

/-! ## Cumulative weighted Mangoldt arrivals -/

/-- Weighted Mangoldt mass arriving at integer events in `(m,n]`. -/
noncomputable def suzukiWeightedMangoldtInterval (m n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc m n,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k

theorem suzukiWeightedMangoldtInterval_nonneg (m n : ℕ) :
    0 ≤ suzukiWeightedMangoldtInterval m n := by
  unfold suzukiWeightedMangoldtInterval
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)

/-- Arrival mass is finitely additive over adjacent integer intervals. -/
theorem suzukiWeightedMangoldtInterval_add
    {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    suzukiWeightedMangoldtInterval m p =
      suzukiWeightedMangoldtInterval m n +
        suzukiWeightedMangoldtInterval n p := by
  unfold suzukiWeightedMangoldtInterval
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
    Finset.Ioc_union_Ioc_eq_Ioc hmn hnp]

theorem suzukiWeightedMangoldtInterval_eq_prefix_sub
    {m n : ℕ} (hmn : m ≤ n) :
    suzukiWeightedMangoldtInterval m n =
      suzukiWeightedMangoldtInterval 0 n -
        suzukiWeightedMangoldtInterval 0 m := by
  have h := suzukiWeightedMangoldtInterval_add (m := 0) (n := m) (p := n)
    (Nat.zero_le m) hmn
  linarith

/-- Exact interval Abel summation.  It is the difference of the two exact
Chebyshev-prefix formulae and assumes no asymptotic estimate. -/
theorem weightedMangoldtInterval_eq_chebyshevPartialSummation
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiWeightedMangoldtInterval m n =
      ((n : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi n +
          2⁻¹ * ∫ t : ℝ in Set.Ioc 1 (n : ℝ),
            t ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi t) -
        ((m : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi m +
          2⁻¹ * ∫ t : ℝ in Set.Ioc 1 (m : ℝ),
            t ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi t) := by
  rw [suzukiWeightedMangoldtInterval_eq_prefix_sub hmn]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simpa [suzukiWeightedMangoldtInterval, Nat.floor_natCast] using
    congrArg₂ (· - ·)
      (sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi hn)
      (sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi hm')

/-- A completely local elementary arrival bound.  It is intentionally crude;
the quantitative audit records that existing global estimates do not control
the short-interval cancellation needed by long busy periods. -/
theorem weightedMangoldtInterval_le_checkedElementary
    {m n : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) :
    suzukiWeightedMangoldtInterval m n ≤ n * Real.log n := by
  unfold suzukiWeightedMangoldtInterval
  calc
    ∑ k ∈ Finset.Ioc m n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k
        ≤ ∑ _k ∈ Finset.Ioc m n, Real.log n := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkI : m < k ∧ k ≤ n := Finset.mem_Ioc.mp hk
          have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hkI.1
          have hk1 : 1 ≤ k := hkpos
          have hsqrt1 : (1 : ℝ) ≤ Real.sqrt k :=
            Real.one_le_sqrt.mpr (by exact_mod_cast hk1)
          calc
            ArithmeticFunction.vonMangoldt k / Real.sqrt k
                ≤ ArithmeticFunction.vonMangoldt k :=
              div_le_self ArithmeticFunction.vonMangoldt_nonneg hsqrt1
            _ ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
            _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast hkpos)
              (by exact_mod_cast hkI.2)
    _ = ((n - m : ℕ) : ℝ) * Real.log n := by simp
    _ ≤ n * Real.log n := by
      have hcard : ((n - m : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n m
      exact mul_le_mul_of_nonneg_right hcard (Real.log_nonneg (by exact_mod_cast hn))

/-! ## Cumulative smooth service and excess -/

/-- Smooth discrepancy recovery supplied on a root interval. -/
noncomputable def suzukiRootService (a b : ℝ) : ℝ :=
  suzukiRootArchSlope b - suzukiRootArchSlope a

theorem suzukiRootService_add (a b c : ℝ) :
    suzukiRootService a c = suzukiRootService a b + suzukiRootService b c := by
  unfold suzukiRootService
  ring

theorem suzukiRootService_eq_integral
    {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) :
    suzukiRootService a b =
      ∫ u in a..b, 2 * suzukiCurvatureFactor u := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      (ha.trans hu.1)).continuousAt.continuousWithinAt
  · intro u hu
    exact hasDerivAt_suzukiRootArchSlope (ha.trans hu.1.le)
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    exact (continuousAt_const.mul (continuousAt_suzukiCurvatureFactor
      (ha.trans hu.1))).continuousWithinAt

theorem suzukiRootService_bounds
    {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a < b) :
    (5 / 3 : ℝ) * (b - a) ≤ suzukiRootService a b ∧
      suzukiRootService a b < 2 * (b - a) := by
  have hcont : ContinuousOn suzukiRootArchSlope (Icc a b) := by
    intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      (ha.trans hu.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ suzukiRootArchSlope (Ioo a b) := by
    intro u hu
    exact (hasDerivAt_suzukiRootArchSlope
      (ha.trans hu.1.le)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope suzukiRootArchSlope hab hcont hdiff
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hservice : suzukiRootService a b =
      deriv suzukiRootArchSlope c * (b - a) := by
    unfold suzukiRootService
    exact ((eq_div_iff hgap.ne').mp hslope).symm
  rw [hservice]
  constructor
  · have hc5 := five_thirds_le_deriv_suzukiRootArchSlope (ha.trans hc.1.le)
    nlinarith
  · have hc2 := deriv_suzukiRootArchSlope_lt_two (ha.trans hc.1.le)
    nlinarith

/-- Arithmetic arrivals minus smooth service between two integer root
endpoints. -/
noncomputable def suzukiArrivalServiceExcess (m n : ℕ) : ℝ :=
  suzukiWeightedMangoldtInterval m n -
    suzukiRootService (Real.sqrt m) (Real.sqrt n)

/-- Error left by applying the checked global prefix estimate to a local
arrival/service comparison.  The Explorer measures how much larger this is
than the exact busy-period scale. -/
noncomputable def suzukiCheckedArrivalServiceError (m n : ℕ) : ℝ :=
  n * Real.log n -
    suzukiRootService (Real.sqrt m) (Real.sqrt n)

theorem weightedMangoldt_arrival_le_service_add_error
    {m n : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n) :
    suzukiWeightedMangoldtInterval m n ≤
      suzukiRootService (Real.sqrt m) (Real.sqrt n) +
        suzukiCheckedArrivalServiceError m n := by
  have h := weightedMangoldtInterval_le_checkedElementary hmn hn
  unfold suzukiCheckedArrivalServiceError
  linarith

theorem suzukiArrivalServiceExcess_add
    {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    suzukiArrivalServiceExcess m p =
      suzukiArrivalServiceExcess m n + suzukiArrivalServiceExcess n p := by
  rw [suzukiArrivalServiceExcess, suzukiArrivalServiceExcess,
    suzukiArrivalServiceExcess, suzukiWeightedMangoldtInterval_add hmn hnp,
    suzukiRootService_add]
  ring

private theorem suzukiRootMangoldtSlope_sqrt_nat (n : ℕ) :
    suzukiRootMangoldtSlope (Real.sqrt n) = suzukiMangoldtSlope n := by
  unfold suzukiRootMangoldtSlope
  rw [Real.sq_sqrt (Nat.cast_nonneg n), Nat.floor_natCast]

theorem suzukiMangoldtSlope_sub_eq_weightedInterval
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiMangoldtSlope n - suzukiMangoldtSlope m =
      suzukiWeightedMangoldtInterval m n := by
  unfold suzukiMangoldtSlope
  rw [show Finset.Icc 1 n = Finset.Ioc 0 n from
      Finset.Icc_succ_left_eq_Ioc _ _,
    show Finset.Icc 1 m = Finset.Ioc 0 m from
      Finset.Icc_succ_left_eq_Ioc _ _]
  exact (suzukiWeightedMangoldtInterval_eq_prefix_sub hmn).symm

/-- Exact multi-event discrepancy balance at arbitrary integer root endpoints. -/
theorem rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiRootSlopeDiscrepancy (Real.sqrt n) -
        suzukiRootSlopeDiscrepancy (Real.sqrt m) =
      -suzukiArrivalServiceExcess m n := by
  have hslope := suzukiMangoldtSlope_sub_eq_weightedInterval hm hmn
  rw [suzukiRootSlopeDiscrepancy, suzukiRootSlopeDiscrepancy,
    suzukiRootMangoldtSlope_sqrt_nat, suzukiRootMangoldtSlope_sqrt_nat,
    suzukiArrivalServiceExcess]
  unfold suzukiRootService
  linarith

/-- Conservation law for a completed busy period: service equals arrivals
plus the recovered discrepancy. -/
theorem suzukiBusyPeriodBalance
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiRootService (Real.sqrt m) (Real.sqrt n) =
      suzukiWeightedMangoldtInterval m n +
        (suzukiRootSlopeDiscrepancy (Real.sqrt n) -
          suzukiRootSlopeDiscrepancy (Real.sqrt m)) := by
  have h := rootSlopeDiscrepancy_sqrt_sub_eq_neg_excess hm hmn
  unfold suzukiArrivalServiceExcess at h
  linarith

/-! ## Loss envelopes and certificates -/

/-- Removing the root weight costs at most `2/a` on a positive interval. -/
theorem weightedBacklogIntegral_le_unweighted
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hback : IntervalIntegrable suzukiRootSlopeBacklog volume a b)
    (hweighted : IntervalIntegrable
      (fun u => 2 / u * suzukiRootSlopeBacklog u) volume a b) :
    (∫ u in a..b, 2 / u * suzukiRootSlopeBacklog u) ≤
      2 / a * ∫ u in a..b, suzukiRootSlopeBacklog u := by
  rw [← intervalIntegral.integral_const_mul]
  have hright : IntervalIntegrable
      (fun u => 2 / a * suzukiRootSlopeBacklog u) volume a b :=
    hback.const_mul _
  apply intervalIntegral.integral_mono_on hab hweighted hright
  intro u huI
  have hu : 0 < u := ha.trans_le huI.1
  have hcoeff : 2 / u ≤ 2 / a := by
    apply (div_le_div_iff₀ hu ha).2
    nlinarith [huI.1]
  exact mul_le_mul_of_nonneg_right hcoeff (by
    exact le_max_right _ _)

/-- A finite, auditable certificate for a multi-event root excursion.  The
numerical Explorer may propose its fields, but only proofs of the bounds can
construct this structure. -/
structure SuzukiBusyPeriodCertificate where
  startRoot : ℝ
  endRoot : ℝ
  reserveLower : ℝ
  lossUpper : ℝ
  roots_ordered : startRoot ≤ endRoot
  reserve_bound : reserveLower ≤ suzukiPsiRoot startRoot
  loss_bound : ∀ u ∈ Icc startRoot endRoot,
    suzukiPsiRoot startRoot - suzukiPsiRoot u ≤ lossUpper
  safe : lossUpper ≤ reserveLower

theorem SuzukiBusyPeriodCertificate.psiRoot_nonnegative
    (certificate : SuzukiBusyPeriodCertificate) :
    ∀ u ∈ Icc certificate.startRoot certificate.endRoot,
      0 ≤ suzukiPsiRoot u := by
  intro u hu
  have hloss := certificate.loss_bound u hu
  linarith [certificate.reserve_bound, certificate.safe]

/-- Exact-prefix-plus-tail architecture.  The prefix is finite evidence only
until `prefix_safe` is proved; the tail field must be an independent theorem. -/
structure SuzukiExactPrefixPlusTailCertificate where
  cutoff : ℝ
  cutoff_nonneg : 0 ≤ cutoff
  prefix_safe : ∀ t, 0 ≤ t → t ≤ cutoff → 0 ≤ suzukiPsi t
  tail_safe : ∀ t, cutoff ≤ t → 0 ≤ suzukiPsi t

theorem SuzukiExactPrefixPlusTailCertificate.global_nonnegative
    (certificate : SuzukiExactPrefixPlusTailCertificate) :
    ∀ t, 0 ≤ t → 0 ≤ suzukiPsi t := by
  intro t ht
  rcases le_total t certificate.cutoff with h | h
  · exact certificate.prefix_safe t ht h
  · exact certificate.tail_safe t h

end RHGarden
