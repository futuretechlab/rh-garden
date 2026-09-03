import RHGarden.LiXiQuotient
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Log.Summable

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace RHGarden

set_option maxHeartbeats 400000

private theorem posLog_norm_primaryFactorOne_le_four_mul_three_halves (w : ℂ) :
    Real.posLog ‖primaryFactorOne w‖ ≤ 4 * ‖w‖ ^ (3 / 2 : ℝ) := by
  let x : ℝ := ‖w‖
  have hx : 0 ≤ x := norm_nonneg w
  by_cases hsmall : x ≤ 1 / 2
  · have hnorm : ‖primaryFactorOne w‖ ≤ 1 + 4 * x ^ 2 := by
      calc
        ‖primaryFactorOne w‖ ≤ ‖primaryFactorOne w - 1‖ + ‖(1 : ℂ)‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ 4 * x ^ 2 + 1 := by
          exact add_le_add
            (by simpa [x] using norm_primaryFactorOne_sub_one_le (w := w) hsmall)
            (by norm_num)
        _ = 1 + 4 * x ^ 2 := by ring
    have hposLog : Real.posLog ‖primaryFactorOne w‖ ≤ 4 * x ^ 2 := by
      calc
        Real.posLog ‖primaryFactorOne w‖ ≤ Real.posLog (1 + 4 * x ^ 2) :=
          Real.posLog_le_posLog (norm_nonneg _) hnorm
        _ = Real.log (1 + 4 * x ^ 2) := by
          rw [Real.posLog_eq_log]
          rw [abs_of_nonneg]
          · nlinarith [sq_nonneg x]
          · nlinarith [sq_nonneg x]
        _ ≤ 4 * x ^ 2 := by
          have := Real.log_le_sub_one_of_pos
            (show 0 < 1 + 4 * x ^ 2 by nlinarith [sq_nonneg x])
          linarith
    have hxone : x ≤ 1 := hsmall.trans (by norm_num)
    have hrpow : x ^ 2 ≤ x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hx hxone (by norm_num : (0 : ℝ) ≤ 3 / 2)
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
    simpa [x] using hposLog.trans (mul_le_mul_of_nonneg_left hrpow (by norm_num))
  · have hlarge : 1 / 2 < x := lt_of_not_ge hsmall
    have hnorm : ‖primaryFactorOne w‖ ≤ Real.exp (2 * x) := by
      calc
        ‖primaryFactorOne w‖ = ‖1 - w‖ * ‖Complex.exp w‖ := by
          simp [primaryFactorOne]
        _ ≤ (1 + x) * Real.exp x := by
          gcongr
          · simpa [x] using norm_sub_le (1 : ℂ) w
          · exact Complex.norm_exp_le_exp_norm w
        _ ≤ Real.exp x * Real.exp x := by
          gcongr
          simpa [add_comm] using Real.add_one_le_exp x
        _ = Real.exp (2 * x) := by rw [← Real.exp_add]; congr 1; ring
    have hposLog : Real.posLog ‖primaryFactorOne w‖ ≤ 2 * x := by
      calc
        Real.posLog ‖primaryFactorOne w‖ ≤ Real.posLog (Real.exp (2 * x)) :=
          Real.posLog_le_posLog (norm_nonneg _) hnorm
        _ = 2 * x := by simp [Real.posLog_apply, hx]
    have hx_rpow : 2 * x ≤ 4 * x ^ (3 / 2 : ℝ) := by
      by_cases hxone : x ≤ 1
      · have hsquare : x ^ 2 ≤ x ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_ge' hx hxone
            (by norm_num : (0 : ℝ) ≤ 3 / 2)
            (by norm_num : (3 / 2 : ℝ) ≤ 2)
        nlinarith [mul_nonneg hx (sub_nonneg.mpr hlarge.le)]
      · have hone : 1 ≤ x := le_of_not_ge hxone
        have hlinear : x ≤ x ^ (3 / 2 : ℝ) := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hone (by norm_num : (1 : ℝ) ≤ 3 / 2)
        nlinarith [Real.rpow_nonneg hx (3 / 2 : ℝ)]
    simpa [x] using hposLog.trans hx_rpow

/-- The genus-one primary factor has a global positive-log bound of order `3 / 2`.
The quadratic cancellation at the origin is used on the half-unit disk; outside
that disk the elementary product formula gives a linear bound. -/
theorem posLog_norm_primaryFactorOne_le_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ,
      Real.posLog ‖primaryFactorOne w‖ ≤ C * ‖w‖ ^ (3 / 2 : ℝ) :=
  ⟨4, by norm_num, posLog_norm_primaryFactorOne_le_four_mul_three_halves⟩

/-- The intrinsic occurrence-indexed canonical product has global order at most
`3 / 2`.  The passage from finite products to the `tprod` uses multipliability
of both the canonical factors and the exponential positive-log majorant. -/
theorem xiCanonicalProductOccurrences_growth_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖xiCanonicalProductOccurrences s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  let reciprocal : XiZeroOccurrence → ℝ := fun a ↦
    1 / ‖a.value‖ ^ (3 / 2 : ℝ)
  let S : ℝ := ∑' a : XiZeroOccurrence, reciprocal a
  let C : ℝ := max 1 (4 * S)
  have hSnonneg : 0 ≤ S := by
    exact tsum_nonneg fun _ ↦ by positivity
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro s
  let q : XiZeroOccurrence → ℝ := fun a ↦
    Real.posLog ‖xiOccurrencePrimaryFactor a s‖
  let K : ℝ := 4 * ‖s‖ ^ (3 / 2 : ℝ)
  have hq_bound : ∀ a : XiZeroOccurrence, q a ≤ K * reciprocal a := by
    intro a
    have hprimary := posLog_norm_primaryFactorOne_le_four_mul_three_halves
      (s / a.value)
    calc
      q a = Real.posLog ‖primaryFactorOne (s / a.value)‖ := by
        rfl
      _ ≤ 4 * ‖s / a.value‖ ^ (3 / 2 : ℝ) := by
        simpa using hprimary
      _ = K * reciprocal a := by
        rw [norm_div, Real.div_rpow (norm_nonneg s) (norm_nonneg a.value)]
        simp only [K, reciprocal, div_eq_mul_inv]
        ring
  have hreciprocal : Summable reciprocal := by
    simpa [reciprocal] using xiOccurrence_reciprocal_three_halves_summable
  have hmajorant : Summable (fun a ↦ K * reciprocal a) :=
    hreciprocal.mul_left K
  have hq : Summable q :=
    hmajorant.of_nonneg_of_le (fun _ ↦ Real.posLog_nonneg) hq_bound
  have hf_multipliable :
      Multipliable (fun a : XiZeroOccurrence ↦ xiOccurrencePrimaryFactor a s) :=
    xiOccurrencePrimaryFactors_multipliableLocallyUniformly.multipliable (Set.mem_univ s)
  have hfactor_le : ∀ a : XiZeroOccurrence,
      ‖xiOccurrencePrimaryFactor a s‖ ≤ Real.exp (q a) := by
    intro a
    dsimp only [q]
    rw [Real.posLog_eq_log_max_one (norm_nonneg _), Real.exp_log]
    · exact le_max_right _ _
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have htsum_q : ∑' a, q a ≤ K * S := by
    calc
      ∑' a, q a ≤ ∑' a, K * reciprocal a :=
        hq.tsum_le_tsum hq_bound hmajorant
      _ = K * S := hreciprocal.tsum_mul_left K
  have hKS : K * S ≤ C * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
    have hpow : ‖s‖ ^ (3 / 2 : ℝ) ≤ (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (norm_nonneg s) (by linarith [norm_nonneg s]) (by norm_num)
    have h4S : 4 * S ≤ C := le_max_right _ _
    dsimp only [K]
    have hleft :
        (4 * S) * ‖s‖ ^ (3 / 2 : ℝ) ≤
          C * ‖s‖ ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right h4S (Real.rpow_nonneg (norm_nonneg s) _)
    have hright :
        C * ‖s‖ ^ (3 / 2 : ℝ) ≤
          C * (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hCpos.le
    nlinarith
  have htprod_le :
      (∏' a : XiZeroOccurrence, ‖xiOccurrencePrimaryFactor a s‖) ≤
        Real.exp (∑' a : XiZeroOccurrence, q a) := by
    apply hf_multipliable.norm.tprod_le_of_prod_le
    intro F
    calc
      ∏ a ∈ F, ‖xiOccurrencePrimaryFactor a s‖ ≤
          ∏ a ∈ F, Real.exp (q a) := by
        exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun a _ ↦ hfactor_le a)
      _ = Real.exp (∑ a ∈ F, q a) := (Real.exp_sum F q).symm
      _ ≤ Real.exp (∑' a : XiZeroOccurrence, q a) := by
        apply Real.exp_le_exp.mpr
        exact hq.sum_le_tsum F (fun _ _ ↦ Real.posLog_nonneg)
  calc
    ‖xiCanonicalProductOccurrences s‖ =
        ∏' a : XiZeroOccurrence, ‖xiOccurrencePrimaryFactor a s‖ := by
      exact hf_multipliable.norm_tprod
    _ ≤ Real.exp (∑' a : XiZeroOccurrence, q a) := htprod_le
    _ ≤ Real.exp (K * S) := Real.exp_le_exp.mpr htsum_q
    _ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr hKS

/-- An entire function has no pole-counting contribution to its characteristic. -/
theorem logCounting_top_eq_zero_of_differentiable
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ValueDistribution.logCounting f ⊤ = 0 := by
  rw [ValueDistribution.logCounting_top]
  have hana : AnalyticOnNhd ℂ f Set.univ :=
    (differentiableOn_univ.mpr hf).analyticOnNhd isOpen_univ
  rw [negPart_eq_zero.mpr
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana)]
  simp

/-- A pointwise exponential growth bound for an entire function bounds its
Nevanlinna characteristic by the same radial exponent. -/
theorem characteristic_top_le_of_entire_exp_growth
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    {τ C : ℝ}
    (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ,
      ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
    ∀ r : ℝ, 0 ≤ r →
      ValueDistribution.characteristic f ⊤ r ≤ C * (1 + r) ^ τ := by
  have hana : AnalyticOnNhd ℂ f Set.univ :=
    (differentiableOn_univ.mpr hf).analyticOnNhd isOpen_univ
  have hmer : Meromorphic f := fun z ↦ hana.meromorphicOn z (Set.mem_univ z)
  have hlogCounting : ValueDistribution.logCounting f ⊤ = 0 :=
    logCounting_top_eq_zero_of_differentiable hf
  intro r hr
  rw [ValueDistribution.characteristic, hlogCounting]
  simp only [add_zero, ValueDistribution.proximity_top]
  apply Real.circleAverage_mono_on_of_le_circle
  · exact hmer.meromorphicOn.circleIntegrable_posLog_norm
  · intro z hz
    have hzr : ‖z‖ = r := by
      simpa [abs_of_nonneg hr, Complex.dist_eq, norm_neg] using hz
    calc
      Real.posLog ‖f z‖ ≤
          Real.posLog (Real.exp (C * (1 + ‖z‖) ^ τ)) :=
        Real.posLog_le_posLog (norm_nonneg _) (hgrowth z)
      _ = C * (1 + ‖z‖) ^ τ := by
        have hnonneg : 0 ≤ C * (1 + ‖z‖) ^ τ :=
          mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
        simp [Real.posLog_apply, hnonneg]
      _ = C * (1 + r) ^ τ := by rw [hzr]

/-- The coarse xi growth estimate transferred to the Nevanlinna characteristic. -/
theorem riemannXi_characteristic_subquadratic :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
        ValueDistribution.characteristic riemannXi ⊤ r ≤
          C * (1 + r) ^ (xiGrowthOrder + ε) := by
  intro ε hε
  obtain ⟨C, hC, hgrowth⟩ := riemannXi_subquadratic_growth ε hε
  refine ⟨C, hC, ?_⟩
  exact characteristic_top_le_of_entire_exp_growth differentiable_riemannXi hC.le hgrowth

/-- The order-`3 / 2` canonical-product bound transferred to its characteristic. -/
theorem xiCanonicalProductOccurrences_characteristic_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      ValueDistribution.characteristic xiCanonicalProductOccurrences ⊤ r ≤
        C * (1 + r) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hgrowth⟩ := xiCanonicalProductOccurrences_growth_three_halves
  refine ⟨C, hC, ?_⟩
  exact characteristic_top_le_of_entire_exp_growth
    differentiable_xiCanonicalProductOccurrences hC.le hgrowth

/-- The first main theorem gives exact equality of the characteristics of the
canonical product and its inverse away from radius zero, because the product is
analytic and has value one at the origin. -/
theorem characteristic_inv_xiCanonicalProductOccurrences_eq
    {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.characteristic (xiCanonicalProductOccurrences⁻¹) ⊤ r =
      ValueDistribution.characteristic xiCanonicalProductOccurrences ⊤ r := by
  have hmer : Meromorphic xiCanonicalProductOccurrences := fun z ↦
    (differentiable_xiCanonicalProductOccurrences.analyticAt z).meromorphicAt
  have htrail :
      meromorphicTrailingCoeffAt xiCanonicalProductOccurrences 0 = 1 := by
    simpa using
      (differentiable_xiCanonicalProductOccurrences.analyticAt 0
        |>.meromorphicTrailingCoeffAt_of_ne_zero
          (by simp [xiCanonicalProductOccurrences_zero]))
  have hfirst :=
    ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero hmer hr
  rw [htrail] at hfirst
  norm_num at hfirst ⊢
  linarith

/-- Consequently the inverse product obeys the same order-`3 / 2`
characteristic bound on the radii used by the multiplication theorem. -/
theorem inv_xiCanonicalProductOccurrences_characteristic_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ValueDistribution.characteristic (xiCanonicalProductOccurrences⁻¹) ⊤ r ≤
        C * (1 + r) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hproduct⟩ :=
    xiCanonicalProductOccurrences_characteristic_three_halves
  refine ⟨C, hC, ?_⟩
  intro r hr
  rw [characteristic_inv_xiCanonicalProductOccurrences_eq (by linarith)]
  exact hproduct r (by linarith)

/-- Normal-form repair changes the raw quotient only on a discrete subset. -/
theorem xiRawQuotient_eventuallyEq_xiZeroFreeQuotient :
    xiRawQuotient =ᶠ[Filter.codiscrete ℂ] xiZeroFreeQuotient := by
  change xiRawQuotient =ᶠ[Filter.codiscreteWithin Set.univ]
    toMeromorphicNFOn xiRawQuotient Set.univ
  exact toMeromorphicNFOn_eqOn_codiscrete meromorphicOn_xiRawQuotient

/-- The raw quotient and its entire normal-form repair have the same
Nevanlinna characteristic at every nonzero radius. -/
theorem characteristic_xiZeroFreeQuotient_eq_xiRawQuotient
    {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.characteristic xiZeroFreeQuotient ⊤ r =
      ValueDistribution.characteristic xiRawQuotient ⊤ r := by
  exact (ValueDistribution.characteristic_congr_codiscrete
    xiRawQuotient_eventuallyEq_xiZeroFreeQuotient hr).symm

/-- The raw quotient characteristic is bounded by those of xi and the inverse
canonical product. -/
theorem characteristic_xiRawQuotient_le_add {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.characteristic xiRawQuotient ⊤ r ≤
      ValueDistribution.characteristic riemannXi ⊤ r +
        ValueDistribution.characteristic (xiCanonicalProductOccurrences⁻¹) ⊤ r := by
  have hxi_mer : Meromorphic riemannXi := fun z ↦
    (analyticAt_riemannXi z).meromorphicAt
  have hproduct_mer : Meromorphic xiCanonicalProductOccurrences := fun z ↦
    (differentiable_xiCanonicalProductOccurrences.analyticAt z).meromorphicAt
  have hxi_order : ∀ z, meromorphicOrderAt riemannXi z ≠ ⊤ := by
    intro z
    rw [(analyticAt_riemannXi z).meromorphicOrderAt_eq]
    simp [analyticOrderAt_riemannXi_ne_top z]
  have hproduct_order :
      ∀ z, meromorphicOrderAt (xiCanonicalProductOccurrences⁻¹) z ≠ ⊤ := by
    intro z
    rw [meromorphicOrderAt_inv,
      (differentiable_xiCanonicalProductOccurrences.analyticAt z).meromorphicOrderAt_eq]
    simp [analyticOrderAt_xiCanonicalProductOccurrences_ne_top z]
  have hmul := ValueDistribution.characteristic_mul_top_le hr
    hxi_mer hxi_order hproduct_mer.inv hproduct_order
  rw [show xiRawQuotient = riemannXi * xiCanonicalProductOccurrences⁻¹ by
    funext z
    simp [xiRawQuotient, div_eq_mul_inv]]
  exact hmul

/-- Principal Nevanlinna estimate for the repaired zero-free quotient. -/
theorem characteristic_xiZeroFreeQuotient_le :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
        ValueDistribution.characteristic xiZeroFreeQuotient ⊤ r ≤
          C * (1 + r) ^ (xiGrowthOrder + ε) := by
  intro ε hε
  obtain ⟨Cxi, hCxi, hxi⟩ := riemannXi_characteristic_subquadratic ε hε
  obtain ⟨CP, hCP, hproduct⟩ :=
    inv_xiCanonicalProductOccurrences_characteristic_three_halves
  refine ⟨Cxi + CP, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := by linarith
  have hbase : 1 ≤ 1 + r := by linarith
  have hpow : (1 + r) ^ (3 / 2 : ℝ) ≤
      (1 + r) ^ (xiGrowthOrder + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase
    norm_num [xiGrowthOrder]
    linarith
  calc
    ValueDistribution.characteristic xiZeroFreeQuotient ⊤ r =
        ValueDistribution.characteristic xiRawQuotient ⊤ r :=
      characteristic_xiZeroFreeQuotient_eq_xiRawQuotient (by linarith)
    _ ≤ ValueDistribution.characteristic riemannXi ⊤ r +
        ValueDistribution.characteristic (xiCanonicalProductOccurrences⁻¹) ⊤ r :=
      characteristic_xiRawQuotient_le_add hr
    _ ≤ Cxi * (1 + r) ^ (xiGrowthOrder + ε) +
        CP * (1 + r) ^ (3 / 2 : ℝ) :=
      add_le_add (hxi r hr0) (hproduct r hr)
    _ ≤ Cxi * (1 + r) ^ (xiGrowthOrder + ε) +
        CP * (1 + r) ^ (xiGrowthOrder + ε) := by
      gcongr
    _ = (Cxi + CP) * (1 + r) ^ (xiGrowthOrder + ε) := by ring

/-- The zero-free entire quotient admits a global entire logarithm. -/
theorem xiZeroFreeQuotient_eq_exp_entire :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z : ℂ,
      xiZeroFreeQuotient z = Complex.exp (k z) :=
  zeroFreeEntire_eq_exp_entire differentiable_xiZeroFreeQuotient
    xiZeroFreeQuotient_ne_zero

/-- The real part of any entire logarithm of the quotient is its log-norm. -/
theorem re_entireLog_xiZeroFreeQuotient_eq_log_norm
    {k : ℂ → ℂ}
    (hexp : ∀ z : ℂ, xiZeroFreeQuotient z = Complex.exp (k z))
    (z : ℂ) :
    (k z).re = Real.log ‖xiZeroFreeQuotient z‖ := by
  rw [hexp z, Complex.norm_exp, Real.log_exp]

/-- Poisson's formula converts the quotient's averaged positive-log growth
into a pointwise upper bound for the real part of its entire logarithm.  The
radius `2 * (1 + ‖z‖)` makes the Poisson kernel at most three. -/
theorem re_entireLog_xiZeroFreeQuotient_le_three_mul_characteristic
    {k : ℂ → ℂ}
    (hk : Differentiable ℂ k)
    (hexp : ∀ z : ℂ, xiZeroFreeQuotient z = Complex.exp (k z))
    (z : ℂ) :
    (k z).re ≤ 3 * ValueDistribution.characteristic xiZeroFreeQuotient ⊤
      (2 * (1 + ‖z‖)) := by
  let u : ℂ → ℝ := fun w ↦ (k w).re
  let R : ℝ := 2 * (1 + ‖z‖)
  have hR : 0 < R := by dsimp [R]; positivity
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [sub_zero]
    dsimp [R]
    nlinarith [norm_nonneg z]
  have hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall (0 : ℂ) R) := by
    intro w _hw
    exact (hk.analyticAt w).harmonicAt_re
  have hpoisson :
      Real.circleAverage (poissonKernel 0 z • u) 0 R = u z :=
    hu.circleAverage_poissonKernel_smul hzball
  have hucont : Continuous u := by
    exact Complex.continuous_re.comp hk.continuous
  have hkernel_cont :
      ContinuousOn (poissonKernel 0 z) (Metric.sphere (0 : ℂ) |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hzball)
  have hleft_integrable :
      CircleIntegrable (poissonKernel 0 z • u) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    simpa [Pi.smul_apply, smul_eq_mul, abs_of_pos hR] using
      hkernel_cont.mul hucont.continuousOn
  let v : ℂ → ℝ := fun w ↦ max (u w) 0
  have hvcont : Continuous v := by
    dsimp [v]
    fun_prop
  have hright_integrable : CircleIntegrable ((3 : ℝ) • v) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact (continuous_const.smul hvcont).continuousOn
  have havg :
      Real.circleAverage (poissonKernel 0 z • u) 0 R ≤
        Real.circleAverage ((3 : ℝ) • v) 0 R := by
    apply Real.circleAverage_mono hleft_integrable hright_integrable
    intro w hw
    have hwR : w ∈ Metric.sphere (0 : ℂ) R := by
      simpa [abs_of_pos hR] using hw
    have hupper0 := re_herglotzRieszKernel_le hwR hzball
    have hlower0 := le_re_herglotzRieszKernel hwR hzball
    have hden : 0 < R - ‖z - 0‖ := by
      simpa [Metric.mem_ball, Complex.dist_eq] using hzball
    have hsum : 0 < R + ‖z - 0‖ := by positivity
    have hratio_upper : (R + ‖z - 0‖) / (R - ‖z - 0‖) ≤ 3 := by
      rw [div_le_iff₀ hden]
      dsimp [R]
      simp only [sub_zero]
      nlinarith [norm_nonneg z]
    have hratio_lower : 0 ≤ (R - ‖z - 0‖) / (R + ‖z - 0‖) :=
      div_nonneg hden.le hsum.le
    have hkernel_upper : poissonKernel 0 z w ≤ 3 := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact hupper0.trans hratio_upper
    have hkernel_nonneg : 0 ≤ poissonKernel 0 z w := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact hratio_lower.trans hlower0
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases huw : 0 ≤ u w
    · rw [show v w = u w by simp [v, huw]]
      exact mul_le_mul_of_nonneg_right hkernel_upper huw
    · have huw' : u w ≤ 0 := le_of_not_ge huw
      rw [show v w = 0 by simp [v, huw']]
      simpa using mul_nonpos_of_nonneg_of_nonpos hkernel_nonneg huw'
  have hv_eq : v = fun w ↦ Real.posLog ‖xiZeroFreeQuotient w‖ := by
    funext w
    dsimp [v, u]
    rw [re_entireLog_xiZeroFreeQuotient_eq_log_norm hexp w]
    simp only [Real.posLog_apply, max_comm]
  have hchar_prox :
      ValueDistribution.characteristic xiZeroFreeQuotient ⊤ R =
        ValueDistribution.proximity xiZeroFreeQuotient ⊤ R := by
    rw [ValueDistribution.characteristic,
      logCounting_top_eq_zero_of_differentiable differentiable_xiZeroFreeQuotient]
    simp
  calc
    (k z).re = u z := rfl
    _ = Real.circleAverage (poissonKernel 0 z • u) 0 R := hpoisson.symm
    _ ≤ Real.circleAverage ((3 : ℝ) • v) 0 R := havg
    _ = 3 * Real.circleAverage v 0 R := by
      rw [Real.circleAverage_smul]
      rfl
    _ = 3 * ValueDistribution.proximity xiZeroFreeQuotient ⊤ R := by
      rw [hv_eq, ValueDistribution.proximity_top]
    _ = 3 * ValueDistribution.characteristic xiZeroFreeQuotient ⊤ R := by
      rw [hchar_prox]
    _ = 3 * ValueDistribution.characteristic xiZeroFreeQuotient ⊤
        (2 * (1 + ‖z‖)) := rfl

/-- The repaired xi quotient has the subquadratic growth required by the
Hadamard affine-factor theorem. -/
theorem xiQuotient_subquadratic_growth :
    XiQuotientSubquadraticGrowth := by
  obtain ⟨k, hk, hexp⟩ := xiZeroFreeQuotient_eq_exp_entire
  intro ε hε
  obtain ⟨C, hC, hcharacteristic⟩ :=
    characteristic_xiZeroFreeQuotient_le ε hε
  let p : ℝ := xiGrowthOrder + ε
  let D : ℝ := 3 * C * 3 ^ p
  have hp : 0 < p := by
    dsimp [p]
    linarith [one_le_xiGrowthOrder]
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro z
  let b : ℝ := 1 + ‖z‖
  let R : ℝ := 2 * b
  have hb : 1 ≤ b := by dsimp [b]; linarith [norm_nonneg z]
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  have hre := re_entireLog_xiZeroFreeQuotient_le_three_mul_characteristic
    hk hexp z
  have hre_characteristic :
      (k z).re ≤ 3 * (C * (1 + R) ^ p) := by
    have hchar := hcharacteristic R hR
    have hRdef : R = 2 * (1 + ‖z‖) := by rfl
    rw [← hRdef] at hre
    exact hre.trans (mul_le_mul_of_nonneg_left (by simpa [p] using hchar) (by norm_num))
  have hradial : (1 + R) ^ p ≤ 3 ^ p * b ^ p := by
    have hbase : 1 + R ≤ 3 * b := by
      dsimp [R, b]
      linarith [norm_nonneg z]
    calc
      (1 + R) ^ p ≤ (3 * b) ^ p :=
        Real.rpow_le_rpow (by positivity) hbase hp.le
      _ = 3 ^ p * b ^ p := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hre_final : (k z).re ≤ D * b ^ p := by
    calc
      (k z).re ≤ 3 * (C * (1 + R) ^ p) := hre_characteristic
      _ ≤ 3 * (C * (3 ^ p * b ^ p)) := by
        gcongr
      _ = D * b ^ p := by
        dsimp [D]
        ring
  rw [hexp z, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simpa [D, b, p] using hre_final

/-- Unconditional genus-one Hadamard representation of the Riemann xi
function, with the affine factor left unsimplified. -/
theorem riemannXi_eq_exp_affine_mul_canonicalProduct :
    ∃ A B : ℂ, ∀ s : ℂ,
      riemannXi s = Complex.exp (A + B * s) *
        xiCanonicalProductOccurrences s :=
  riemannXi_eq_exp_affine_mul_canonicalProduct_of_quotient_growth
    xiQuotient_subquadratic_growth

/-- The genus-one occurrence product has vanishing logarithmic derivative at
the origin.  Every corrected reciprocal summand vanishes there termwise. -/
theorem logDeriv_xiCanonicalProductOccurrences_zero :
    logDeriv xiCanonicalProductOccurrences 0 = 0 := by
  rw [logDeriv_xiCanonicalProductOccurrences (by simp)]
  simp

/-- The logarithmic derivative of an exponential affine function is its
linear coefficient. -/
theorem logDeriv_exp_affine (A B s : ℂ) :
    logDeriv (fun z : ℂ ↦ Complex.exp (A + B * z)) s = B := by
  change logDeriv (Complex.exp ∘ fun z : ℂ ↦ A + B * z) s = B
  rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_exp]
  simp

/-- The occurrence-indexed genus-one factorization normalized at the origin.
The constant exponential is fixed by `riemannXi 0 = 1 / 2`; its linear
coefficient is the logarithmic derivative of xi at zero. -/
theorem riemannXi_eq_half_mul_exp_logDeriv_zero_mul_canonicalProduct :
    ∀ s : ℂ,
      riemannXi s =
        (1 / 2 : ℂ) *
          Complex.exp (logDeriv riemannXi 0 * s) *
            xiCanonicalProductOccurrences s := by
  obtain ⟨A, B, hfactor⟩ :=
    riemannXi_eq_exp_affine_mul_canonicalProduct
  have hA : Complex.exp A = (1 / 2 : ℂ) := by
    have hzero := hfactor 0
    simpa using hzero.symm
  have hB : B = logDeriv riemannXi 0 := by
    have hexp_ne : Complex.exp (A + B * (0 : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have hproduct_ne : xiCanonicalProductOccurrences 0 ≠ 0 := by simp
    have hlog :
        logDeriv riemannXi 0 =
          logDeriv (fun z : ℂ ↦ Complex.exp (A + B * z)) 0 +
            logDeriv xiCanonicalProductOccurrences 0 := by
      rw [show riemannXi = fun z : ℂ ↦
          Complex.exp (A + B * z) * xiCanonicalProductOccurrences z from
        funext hfactor]
      exact logDeriv_mul 0 hexp_ne hproduct_ne
        (by fun_prop)
        differentiable_xiCanonicalProductOccurrences.differentiableAt
    simpa [logDeriv_exp_affine,
      logDeriv_xiCanonicalProductOccurrences_zero] using hlog.symm
  intro s
  calc
    riemannXi s = Complex.exp (A + B * s) *
        xiCanonicalProductOccurrences s := hfactor s
    _ = Complex.exp A * Complex.exp (B * s) *
        xiCanonicalProductOccurrences s := by rw [Complex.exp_add]
    _ = (1 / 2 : ℂ) *
          Complex.exp (logDeriv riemannXi 0 * s) *
            xiCanonicalProductOccurrences s := by rw [hA, hB]

/-- Exact global occurrence-indexed partial-fraction expansion of the
logarithmic derivative of Riemann xi away from its zeros. -/
theorem logDeriv_riemannXi_eq_zero_value_add_zero_sum
    {s : ℂ}
    (hs : riemannXi s ≠ 0) :
    logDeriv riemannXi s =
      logDeriv riemannXi 0 +
        ∑' a : XiZeroOccurrence,
          (1 / (s - a.value) + 1 / a.value) := by
  obtain ⟨A, B, hfactor⟩ :=
    riemannXi_eq_exp_affine_mul_canonicalProduct
  have hB : B = logDeriv riemannXi 0 := by
    have hexp_ne : Complex.exp (A + B * (0 : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have hproduct_ne : xiCanonicalProductOccurrences 0 ≠ 0 := by simp
    have hlog :
        logDeriv riemannXi 0 =
          logDeriv (fun z : ℂ ↦ Complex.exp (A + B * z)) 0 +
            logDeriv xiCanonicalProductOccurrences 0 := by
      rw [show riemannXi = fun z : ℂ ↦
          Complex.exp (A + B * z) * xiCanonicalProductOccurrences z from
        funext hfactor]
      exact logDeriv_mul 0 hexp_ne hproduct_ne
        (by fun_prop)
        differentiable_xiCanonicalProductOccurrences.differentiableAt
    simpa [logDeriv_exp_affine,
      logDeriv_xiCanonicalProductOccurrences_zero] using hlog.symm
  have hexp_ne : Complex.exp (A + B * s) ≠ 0 := Complex.exp_ne_zero _
  have hproduct_ne : xiCanonicalProductOccurrences s ≠ 0 :=
    xiCanonicalProductOccurrences_ne_zero hs
  calc
    logDeriv riemannXi s =
        logDeriv (fun z : ℂ ↦
          Complex.exp (A + B * z) * xiCanonicalProductOccurrences z) s := by
      rw [show riemannXi = fun z : ℂ ↦
          Complex.exp (A + B * z) * xiCanonicalProductOccurrences z from
        funext hfactor]
    _ = logDeriv (fun z : ℂ ↦ Complex.exp (A + B * z)) s +
        logDeriv xiCanonicalProductOccurrences s :=
      logDeriv_mul s hexp_ne hproduct_ne
        (by fun_prop)
        differentiable_xiCanonicalProductOccurrences.differentiableAt
    _ = logDeriv riemannXi 0 +
        ∑' a : XiZeroOccurrence,
          (1 / (s - a.value) + 1 / a.value) := by
      rw [logDeriv_exp_affine, hB,
        logDeriv_xiCanonicalProductOccurrences hs]

/-- The open occurrence-indexed xi partial-fraction proposition is discharged
by the normalized affine factorization. -/
theorem xiLogDerivPartialFractionOccurrences :
    XiLogDerivPartialFractionOccurrences := by
  refine ⟨logDeriv riemannXi 0, ?_⟩
  intro s hs
  exact logDeriv_riemannXi_eq_zero_value_add_zero_sum hs

end RHGarden
