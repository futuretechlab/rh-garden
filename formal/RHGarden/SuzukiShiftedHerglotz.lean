import RHGarden.SuzukiShiftedNevanlinna
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology ComplexConjugate ENNReal NNReal

namespace RHGarden

/-- The pole of the shifted xi logarithmic derivative associated to an
occurrence.  This is the existing shifted spectral coordinate, exposed under
the pole-oriented name used by the Herglotz reconstruction. -/
noncomputable def shiftedSpectralPole
    (ω : ℝ) (a : XiZeroOccurrence) : ℂ :=
  xiSpectralParameterShifted ω a

@[simp] theorem shiftedSpectralPole_im
    (ω : ℝ) (a : XiZeroOccurrence) :
    (shiftedSpectralPole ω a).im = a.value.re - 1 / 2 - ω := by
  simp [shiftedSpectralPole]

theorem shiftedSpectralPole_im_nonpos_of_zeroFreeRight
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) (a : XiZeroOccurrence) :
    (shiftedSpectralPole ω a).im ≤ 0 := by
  simpa [shiftedSpectralPole] using
    xiSpectralParameterShifted_im_nonpos_of_zeroFreeRight hzero a

/-- The nonnegative depth of a shifted pole below the real axis. -/
noncomputable def shiftedSpectralPoleDepth
    (ω : ℝ) (a : XiZeroOccurrence) : ℝ :=
  -(shiftedSpectralPole ω a).im

theorem shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) (a : XiZeroOccurrence) :
    0 ≤ shiftedSpectralPoleDepth ω a := by
  rw [shiftedSpectralPoleDepth]
  linarith [shiftedSpectralPole_im_nonpos_of_zeroFreeRight hzero a]

theorem shiftedSpectralPole_eq_re_sub_I_mul_depth
    (ω : ℝ) (a : XiZeroOccurrence) :
    shiftedSpectralPole ω a =
      ((shiftedSpectralPole ω a).re : ℂ) -
        Complex.I * (shiftedSpectralPoleDepth ω a : ℂ) := by
  apply Complex.ext <;> simp [shiftedSpectralPoleDepth]

/-- The probability measure on the real axis whose upper-half-plane Cauchy
transform is the resolvent of the lower-half-plane pole `α - iβ`.

For `β = 0` this is the point mass at `α`; for `β > 0` it is the Cauchy
distribution with location `α` and scale `β`. -/
noncomputable def lowerHalfPlanePoleMeasure
    (α β : ℝ) (hβ : 0 ≤ β) : Measure ℝ :=
  ProbabilityTheory.cauchyMeasure α β.toNNReal

instance lowerHalfPlanePoleMeasure.instIsProbabilityMeasure
    (α β : ℝ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (lowerHalfPlanePoleMeasure α β hβ) := by
  rw [lowerHalfPlanePoleMeasure]
  exact ProbabilityTheory.instIsProbabilityMeasure_cauchyMeasure α β.toNNReal

@[simp] theorem lowerHalfPlanePoleMeasure_apply_univ
    (α β : ℝ) (hβ : 0 ≤ β) :
    lowerHalfPlanePoleMeasure α β hβ Set.univ = 1 := by
  exact measure_univ

theorem lowerHalfPlanePoleMeasure_isFinite
    (α β : ℝ) (hβ : 0 ≤ β) :
    IsFiniteMeasure (lowerHalfPlanePoleMeasure α β hβ) := by
  infer_instance

@[simp] theorem lowerHalfPlanePoleMeasure_zero
    (α : ℝ) (hβ : 0 ≤ (0 : ℝ)) :
    lowerHalfPlanePoleMeasure α 0 hβ = Measure.dirac α := by
  simp [lowerHalfPlanePoleMeasure,
    ProbabilityTheory.cauchyMeasure_zero_scale]

/-- The requested Cauchy kernel, written in the convention used by
`MeasureTheory.resolventTransform`. -/
noncomputable def realCauchyKernel (z : ℂ) (x : ℝ) : ℂ :=
  1 / ((x : ℂ) - z)

theorem integral_cauchyKernel_lowerHalfPlanePole_zero
    (α : ℝ) {z : ℂ} :
    (∫ x : ℝ, realCauchyKernel z x
        ∂lowerHalfPlanePoleMeasure α 0 (le_refl 0)) =
      1 / ((α : ℂ) - z) := by
  simp [realCauchyKernel, lowerHalfPlanePoleMeasure]

private theorem integral_inv_sq_add_sq_univ {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, (x ^ 2 + c ^ 2)⁻¹) = Real.pi / c := by
  have hscale : c.toNNReal ≠ 0 := by positivity
  have h := ProbabilityTheory.integral_cauchyPDFReal_eq_one
    (0 : ℝ) hscale
  simp_rw [ProbabilityTheory.cauchyPDFReal_def] at h
  simp only [sub_zero, Real.coe_toNNReal _ hc.le,
    integral_const_mul] at h
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoef : Real.pi⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero hpi) hc.ne'
  have hI : (∫ x : ℝ, (x ^ 2 + c ^ 2)⁻¹) =
      1 / (Real.pi⁻¹ * c) := by
    apply (eq_div_iff hcoef).2
    simpa [mul_comm] using h
  rw [hI]
  field_simp

private theorem integrable_inv_sq_add_sq_univ {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => (x ^ 2 + c ^ 2)⁻¹) := by
  have hbase := integrable_inv_one_add_sq.comp_div hc.ne'
  have hscaled : Integrable
      (fun x : ℝ => c⁻¹ ^ 2 * (1 + (x / c) ^ 2)⁻¹) :=
    hbase.const_mul _
  convert hscaled using 1
  funext x
  field_simp
  ring

private theorem integral_lorentzian_product
    {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) (hne : y ≠ β) :
    (∫ x : ℝ,
        β * y / ((x ^ 2 + β ^ 2) * (x ^ 2 + y ^ 2))) =
      Real.pi / (β + y) := by
  have hden : y ^ 2 - β ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (ne_of_gt (add_pos hy hβ)) (sub_ne_zero.mpr hne)
  have hβi := integrable_inv_sq_add_sq_univ hβ
  have hyi := integrable_inv_sq_add_sq_univ hy
  rw [show (∫ x : ℝ,
      β * y / ((x ^ 2 + β ^ 2) * (x ^ 2 + y ^ 2))) =
        ∫ x : ℝ, (β * y / (y ^ 2 - β ^ 2)) *
          ((x ^ 2 + β ^ 2)⁻¹ - (x ^ 2 + y ^ 2)⁻¹) by
    apply integral_congr_ae
    filter_upwards with x
    have hβx : x ^ 2 + β ^ 2 ≠ 0 := by positivity
    have hyx : x ^ 2 + y ^ 2 ≠ 0 := by positivity
    field_simp
    ring]
  rw [integral_const_mul, integral_sub hβi hyi,
    integral_inv_sq_add_sq_univ hβ,
    integral_inv_sq_add_sq_univ hy]
  field_simp
  ring

private theorem integral_odd_lorentzian_product
    (β y : ℝ) :
    (∫ x : ℝ,
        β * x / ((x ^ 2 + β ^ 2) * (x ^ 2 + y ^ 2))) = 0 := by
  let f : ℝ → ℝ := fun x =>
    β * x / ((x ^ 2 + β ^ 2) * (x ^ 2 + y ^ 2))
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    ring
  have h := integral_neg_eq_self f (μ := volume)
  simp_rw [hodd, integral_neg] at h
  change (∫ x : ℝ, f x) = 0
  linarith

private theorem integrable_realCauchyKernel
    (α β : ℝ) (hβ : 0 ≤ β) {z : ℂ} (hz : 0 < z.im) :
    Integrable (realCauchyKernel z)
      (lowerHalfPlanePoleMeasure α β hβ) := by
  have hr : Integrable (resolvent z)
      (lowerHalfPlanePoleMeasure α β hβ) := by
    apply MeasureTheory.integrable_resolvent
    rintro ⟨x, _hx, hxz⟩
    have him := congrArg Complex.im hxz
    simp at him
    linarith
  exact hr.congr (Filter.Eventually.of_forall fun x => by
    simp only [realCauchyKernel, one_div, resolvent,
      Ring.inverse_eq_inv]
    congr 2)

private theorem integral_cauchyKernel_lowerHalfPlanePole_aligned
    (α : ℝ) {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) (hne : y ≠ β) :
    (∫ x : ℝ, realCauchyKernel ((α : ℂ) + Complex.I * y) x
        ∂lowerHalfPlanePoleMeasure α β hβ.le) =
      1 / ((α : ℂ) - Complex.I * β -
        ((α : ℂ) + Complex.I * y)) := by
  let γ : ℝ≥0 := β.toNNReal
  have hγ : γ ≠ 0 := by
    dsimp [γ]
    positivity
  have hγcoe : (γ : ℝ) = β := by
    dsimp [γ]
    exact Real.coe_toNNReal β hβ.le
  have hInt : Integrable
      (realCauchyKernel ((α : ℂ) + Complex.I * y))
      (lowerHalfPlanePoleMeasure α β hβ.le) :=
    integrable_realCauchyKernel α β hβ.le (by simp [hy])
  apply Complex.ext
  · change RCLike.re
      (∫ x : ℝ, realCauchyKernel ((α : ℂ) + Complex.I * y) x
        ∂lowerHalfPlanePoleMeasure α β hβ.le) =
      RCLike.re (1 / ((α : ℂ) - Complex.I * β -
        ((α : ℂ) + Complex.I * y)))
    rw [← integral_re hInt, RCLike.re_eq_complex_re]
    rw [lowerHalfPlanePoleMeasure,
      ProbabilityTheory.cauchyMeasure_of_scale_ne_zero α hγ]
    rw [integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_cauchyPDF α γ)
      (Filter.Eventually.of_forall fun x => by
        simp [ProbabilityTheory.cauchyPDF])]
    simp_rw [ProbabilityTheory.cauchyPDF,
      ENNReal.toReal_ofReal
        (ProbabilityTheory.cauchyPDF_pos α hγ _).le,
      ProbabilityTheory.cauchyPDFReal_def]
    rw [hγcoe]
    simp only [smul_eq_mul]
    rw [show (∫ x : ℝ,
        Real.pi⁻¹ * β * ((x - α) ^ 2 + β ^ 2)⁻¹ *
          (realCauchyKernel ((α : ℂ) + Complex.I * y) x).re) =
        Real.pi⁻¹ *
          (∫ u : ℝ, β * u /
            ((u ^ 2 + β ^ 2) * (u ^ 2 + y ^ 2))) by
      rw [← integral_sub_right_eq_self
        (fun u : ℝ => β * u /
          ((u ^ 2 + β ^ 2) * (u ^ 2 + y ^ 2))) α]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [realCauchyKernel, one_div, Complex.inv_re,
        Complex.sub_re, Complex.ofReal_re, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im,
        zero_mul, one_mul, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.sub_im, add_zero, zero_sub,
        Complex.normSq_apply]
      field_simp <;> ring]
    rw [integral_odd_lorentzian_product]
    simp
  · change RCLike.im
      (∫ x : ℝ, realCauchyKernel ((α : ℂ) + Complex.I * y) x
        ∂lowerHalfPlanePoleMeasure α β hβ.le) =
      RCLike.im (1 / ((α : ℂ) - Complex.I * β -
        ((α : ℂ) + Complex.I * y)))
    rw [← integral_im hInt, RCLike.im_eq_complex_im]
    rw [lowerHalfPlanePoleMeasure,
      ProbabilityTheory.cauchyMeasure_of_scale_ne_zero α hγ]
    rw [integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_cauchyPDF α γ)
      (Filter.Eventually.of_forall fun x => by
        simp [ProbabilityTheory.cauchyPDF])]
    simp_rw [ProbabilityTheory.cauchyPDF,
      ENNReal.toReal_ofReal
        (ProbabilityTheory.cauchyPDF_pos α hγ _).le,
      ProbabilityTheory.cauchyPDFReal_def]
    rw [hγcoe]
    simp only [smul_eq_mul]
    rw [show (∫ x : ℝ,
        Real.pi⁻¹ * β * ((x - α) ^ 2 + β ^ 2)⁻¹ *
          (realCauchyKernel ((α : ℂ) + Complex.I * y) x).im) =
        Real.pi⁻¹ *
          (∫ u : ℝ, β * y /
            ((u ^ 2 + β ^ 2) * (u ^ 2 + y ^ 2))) by
      rw [← integral_sub_right_eq_self
        (fun u : ℝ => β * y /
          ((u ^ 2 + β ^ 2) * (u ^ 2 + y ^ 2))) α]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [realCauchyKernel, one_div, Complex.inv_im,
        Complex.sub_re, Complex.ofReal_re, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im,
        zero_mul, one_mul, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.sub_im, add_zero, zero_sub,
        neg_neg, Complex.normSq_apply]
      field_simp <;> ring]
    rw [integral_lorentzian_product hβ hy hne]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    simp only [one_div, Complex.inv_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, add_zero, sub_zero,
      zero_sub, neg_neg, Complex.normSq_apply]
    have hsum : β + y ≠ 0 := ne_of_gt (add_pos hβ hy)
    have hneg : -β - y ≠ 0 := by linarith
    simp only [sub_self, zero_mul, add_zero, zero_add, neg_neg]
    field_simp [hpi, hsum, hneg] <;> ring

/-- The Cauchy transform of a single lower-half-plane pole measure. -/
noncomputable def lowerHalfPlanePoleCauchyTransform
    (α β : ℝ) (hβ : 0 ≤ β) (z : ℂ) : ℂ :=
  ∫ x : ℝ, realCauchyKernel z x
    ∂lowerHalfPlanePoleMeasure α β hβ

private theorem lowerHalfPlanePoleCauchyTransform_eq_resolventTransform
    (α β : ℝ) (hβ : 0 ≤ β) :
    lowerHalfPlanePoleCauchyTransform α β hβ =
      MeasureTheory.resolventTransform
        (lowerHalfPlanePoleMeasure α β hβ) := by
  funext z
  apply integral_congr_ae
  filter_upwards with x
  simp only [lowerHalfPlanePoleCauchyTransform,
    MeasureTheory.resolventTransform_apply, realCauchyKernel,
    one_div, resolvent, Ring.inverse_eq_inv]
  congr 2

theorem analyticOnNhd_lowerHalfPlanePoleCauchyTransform_upper
    (α β : ℝ) (hβ : 0 ≤ β) :
    AnalyticOnNhd ℂ (lowerHalfPlanePoleCauchyTransform α β hβ)
      {z : ℂ | 0 < z.im} := by
  rw [lowerHalfPlanePoleCauchyTransform_eq_resolventTransform]
  have hres := MeasureTheory.analyticOn_resolventTransform
    (μ := lowerHalfPlanePoleMeasure α β hβ)
  have hsub : {z : ℂ | 0 < z.im} ⊆
      ((algebraMap ℝ ℂ) ''
        (lowerHalfPlanePoleMeasure α β hβ).support)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff]
    rintro ⟨x, _hx, rfl⟩
    simp at hz
  have han : AnalyticOn ℂ
      (MeasureTheory.resolventTransform
        (lowerHalfPlanePoleMeasure α β hβ))
      {z : ℂ | 0 < z.im} := hres.mono hsub
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  exact hopen.analyticOn_iff_analyticOnNhd.mp han

private theorem analyticOnNhd_lowerPoleResolvent_upper
    (α β : ℝ) (hβ : 0 ≤ β) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => 1 / ((α : ℂ) - Complex.I * β - z))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < z.im at hz
  have hne : (α : ℂ) - Complex.I * β - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have haff : AnalyticAt ℂ
      (fun w : ℂ => (α : ℂ) - Complex.I * β - w) z := by
    fun_prop
  exact analyticAt_const.div haff hne

/-- A Cauchy probability measure centered at `α` with depth `β` represents
the upper-half-plane resolvent of the pole `α - iβ`. -/
theorem integral_cauchyKernel_lowerHalfPlanePole
    (α β : ℝ) (hβ : 0 ≤ β) {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, realCauchyKernel z x
        ∂lowerHalfPlanePoleMeasure α β hβ) =
      1 / ((α : ℂ) - Complex.I * β - z) := by
  rcases hβ.eq_or_lt with rfl | hβpos
  · simpa using integral_cauchyKernel_lowerHalfPlanePole_zero α
  let F : ℂ → ℂ := lowerHalfPlanePoleCauchyTransform α β hβ
  let G : ℂ → ℂ := fun w => 1 / ((α : ℂ) - Complex.I * β - w)
  let y₀ : ℝ := β + 1
  let z₀ : ℂ := (α : ℂ) + Complex.I * y₀
  have hy₀ : 0 < y₀ := by dsimp [y₀]; linarith
  have hz₀ : z₀ ∈ {w : ℂ | 0 < w.im} := by
    dsimp [z₀]
    simpa using hy₀
  have hF : AnalyticOnNhd ℂ F {w : ℂ | 0 < w.im} := by
    simpa [F] using
      analyticOnNhd_lowerHalfPlanePoleCauchyTransform_upper α β hβ
  have hG : AnalyticOnNhd ℂ G {w : ℂ | 0 < w.im} := by
    simpa [G] using analyticOnNhd_lowerPoleResolvent_upper α β hβ
  have hfreq : ∃ᶠ w : ℂ in nhdsWithin z₀ ({z₀} : Set ℂ)ᶜ,
      F w = G w := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n : ℕ =>
      (α : ℂ) + Complex.I *
        ((y₀ + 1 / (((n + 1 : ℕ) : ℝ))) : ℂ), ?_, ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · have hyc : Tendsto
            (fun n : ℕ =>
              (y₀ : ℂ) + 1 / (((n + 1 : ℕ) : ℂ)))
            atTop (nhds (y₀ : ℂ)) := by
          simpa [Nat.cast_add, Nat.cast_one] using
            (tendsto_const_nhds.add
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)))
        simpa [z₀] using tendsto_const_nhds.add
          (tendsto_const_nhds.mul hyc)
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        have hnonzero :
            Complex.I * (1 / (((n + 1 : ℕ) : ℂ))) ≠ 0 := by
          exact mul_ne_zero Complex.I_ne_zero (one_div_ne_zero hn)
        apply hnonzero
        dsimp [z₀] at heq
        linear_combination heq
    · intro n
      have hyn : 0 < y₀ + 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
      have hne : y₀ + 1 / (((n + 1 : ℕ) : ℝ)) ≠ β := by
        dsimp [y₀]
        have hpos : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
        linarith
      simpa [F, G, lowerHalfPlanePoleCauchyTransform] using
        integral_cauchyKernel_lowerHalfPlanePole_aligned α
          hβpos hyn hne
  have hevent : F =ᶠ[nhds z₀] G :=
    ((hF z₀ hz₀).frequently_eq_iff_eventually_eq (hG z₀ hz₀)).mp hfreq
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    (convex_halfSpace_im_gt 0).isPreconnected hz₀ hevent
  exact heq hz

/-- The standard Herglotz kernel on the real line.  The second term is real
and supplies the decay required for summing Cauchy transforms. -/
noncomputable def herglotzKernel (x : ℝ) (z : ℂ) : ℂ :=
  1 / ((x : ℂ) - z) - (x / (1 + x ^ 2) : ℝ)

private theorem integrable_real_herglotzCorrection
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x : ℝ => x / (1 + x ^ 2)) μ := by
  apply Integrable.of_bound (C := 1)
  · have hcont : Continuous (fun x : ℝ => x / (1 + x ^ 2)) := by
      exact continuous_id.div₀
        (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_div]
    have hden : 0 < 1 + x ^ 2 := by positivity
    rw [abs_of_pos hden]
    apply (div_le_one hden).2
    have hsquare : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]

/-- The real Herglotz correction contributed by one lower-half-plane pole. -/
noncomputable def lowerHalfPlanePoleRealCorrection
    (α β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  ∫ x : ℝ, x / (1 + x ^ 2) ∂lowerHalfPlanePoleMeasure α β hβ

/-- The Cauchy representation of a lower-half-plane pole in standard
Herglotz-corrected form.  Its residual correction is manifestly real. -/
theorem integral_herglotzKernel_lowerHalfPlanePole
    (α β : ℝ) (hβ : 0 ≤ β) {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, herglotzKernel x z
        ∂lowerHalfPlanePoleMeasure α β hβ) =
      1 / ((α : ℂ) - Complex.I * β - z) -
        (lowerHalfPlanePoleRealCorrection α β hβ : ℂ) := by
  change (∫ x : ℝ, realCauchyKernel z x -
      ((x / (1 + x ^ 2) : ℝ) : ℂ)
      ∂lowerHalfPlanePoleMeasure α β hβ) = _
  calc
    _ = (∫ x : ℝ, realCauchyKernel z x
          ∂lowerHalfPlanePoleMeasure α β hβ) -
        ∫ x : ℝ, ((x / (1 + x ^ 2) : ℝ) : ℂ)
          ∂lowerHalfPlanePoleMeasure α β hβ :=
      integral_sub
        (integrable_realCauchyKernel α β hβ hz)
        (integrable_real_herglotzCorrection
          (lowerHalfPlanePoleMeasure α β hβ)).ofReal
    _ = 1 / ((α : ℂ) - Complex.I * β - z) -
        (lowerHalfPlanePoleRealCorrection α β hβ : ℂ) := by
      rw [integral_cauchyKernel_lowerHalfPlanePole α β hβ hz]
      congr 1
      unfold lowerHalfPlanePoleRealCorrection
      exact integral_complex_ofReal
        (X := ℝ) (μ := lowerHalfPlanePoleMeasure α β hβ)
        (f := fun x : ℝ => x / (1 + x ^ 2))

/-- The Herglotz weight of one Cauchy pole measure.  This exact formula is
the summability bridge for the countable xi measure. -/
theorem integral_one_div_one_add_sq_lowerHalfPlanePole
    (α β : ℝ) (hβ : 0 ≤ β) :
    (∫ x : ℝ, 1 / (1 + x ^ 2)
        ∂lowerHalfPlanePoleMeasure α β hβ) =
      (β + 1) / (α ^ 2 + (β + 1) ^ 2) := by
  have hzI : 0 < (Complex.I : ℂ).im := by simp
  have hInt := integrable_realCauchyKernel α β hβ hzI
  have h := integral_cauchyKernel_lowerHalfPlanePole α β hβ hzI
  have him := congrArg Complex.im h
  change RCLike.im
      (∫ x : ℝ, realCauchyKernel Complex.I x
        ∂lowerHalfPlanePoleMeasure α β hβ) =
    RCLike.im (1 / ((α : ℂ) - Complex.I * β - Complex.I)) at him
  rw [← integral_im hInt, RCLike.im_eq_complex_im] at him
  simp only [realCauchyKernel, one_div, Complex.inv_im,
    Complex.sub_im, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.mul_im, Complex.mul_re, zero_mul, one_mul,
    mul_zero, zero_add, sub_zero, zero_sub, neg_neg,
    neg_one_mul, neg_mul, mul_neg, pow_two,
    Complex.normSq_apply] at him
  convert him using 1 <;> ring

@[simp] theorem lowerHalfPlanePoleRealCorrection_im
    (α β : ℝ) (hβ : 0 ≤ β) :
    ((lowerHalfPlanePoleRealCorrection α β hβ : ℂ)).im = 0 := by
  simp

/-- The positive real-axis measure assigned to one shifted xi pole. -/
noncomputable def shiftedXiPoleMeasure
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω)
    (a : XiZeroOccurrence) : Measure ℝ :=
  lowerHalfPlanePoleMeasure
    (shiftedSpectralPole ω a).re
    (shiftedSpectralPoleDepth ω a)
    (shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a)

noncomputable instance shiftedXiPoleMeasure.instIsProbabilityMeasure
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) (a : XiZeroOccurrence) :
    IsProbabilityMeasure (shiftedXiPoleMeasure ω hzero a) := by
  unfold shiftedXiPoleMeasure
  infer_instance

/-- The single-occurrence Herglotz correction is real. -/
noncomputable def shiftedXiPoleRealCorrection
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω)
    (a : XiZeroOccurrence) : ℝ :=
  lowerHalfPlanePoleRealCorrection
    (shiftedSpectralPole ω a).re
    (shiftedSpectralPoleDepth ω a)
    (shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a)

theorem integral_herglotzKernel_shiftedXiPole
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    (a : XiZeroOccurrence) {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, herglotzKernel x z ∂shiftedXiPoleMeasure ω hzero a) =
      1 / (shiftedSpectralPole ω a - z) -
        (shiftedXiPoleRealCorrection ω hzero a : ℂ) := by
  have h := integral_herglotzKernel_lowerHalfPlanePole
    (shiftedSpectralPole ω a).re
    (shiftedSpectralPoleDepth ω a)
    (shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a) hz
  unfold shiftedXiPoleMeasure shiftedXiPoleRealCorrection
  calc
    _ = 1 / (((shiftedSpectralPole ω a).re : ℂ) -
          Complex.I * (shiftedSpectralPoleDepth ω a : ℂ) - z) -
        (lowerHalfPlanePoleRealCorrection
          (shiftedSpectralPole ω a).re
          (shiftedSpectralPoleDepth ω a)
          (shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a) : ℂ) := h
    _ = _ := by
      rw [← shiftedSpectralPole_eq_re_sub_I_mul_depth ω a]

/-- The Herglotz weights of the shifted pole measures are summable.  No new
zero counting is used: the estimate is reduced to the existing reciprocal
square summability of xi-zero occurrences. -/
theorem summable_shiftedXiPole_herglotzWeight
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) :
    Summable (fun a : XiZeroOccurrence =>
      ∫ x : ℝ, 1 / (1 + x ^ 2) ∂shiftedXiPoleMeasure ω hzero a) := by
  let C : ℝ := |ω| + 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmajorant : Summable (fun a : XiZeroOccurrence =>
      C * (1 / ‖a.value‖ ^ 2)) :=
    xiOccurrence_reciprocal_sq_summable.mul_left C
  apply hmajorant.of_nonneg_of_le
  · intro a
    have hdepth := shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a
    rw [shiftedXiPoleMeasure,
      integral_one_div_one_add_sq_lowerHalfPlanePole]
    exact div_nonneg (by linarith) (by positivity)
  · intro a
    have hre := riemannXi_zero_re_mem_Ioo a.1.xi_eq_zero
    change 0 < a.value.re ∧ a.value.re < 1 at hre
    have hdepth : shiftedSpectralPoleDepth ω a =
        ω + 1 / 2 - a.value.re := by
      rw [shiftedSpectralPoleDepth, shiftedSpectralPole_im]
      ring
    have halpha : (shiftedSpectralPole ω a).re = -a.value.im := by
      simp [shiftedSpectralPole, xiSpectralParameterShifted]
    have hB : 1 ≤ shiftedSpectralPoleDepth ω a + 1 := by
      have := shiftedSpectralPoleDepth_nonneg_of_zeroFreeRight hzero a
      linarith
    have hBC : shiftedSpectralPoleDepth ω a + 1 ≤ C := by
      have habs : ω ≤ |ω| := le_abs_self _
      dsimp [C]
      rw [hdepth]
      linarith
    have hdenBig : 0 < (shiftedSpectralPole ω a).re ^ 2 +
        (shiftedSpectralPoleDepth ω a + 1) ^ 2 := by positivity
    have hdenSmall : 0 < 1 + (shiftedSpectralPole ω a).re ^ 2 := by
      positivity
    have hnormpos : 0 < ‖a.value‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr a.value_ne_zero)
    have hnormle : ‖a.value‖ ^ 2 ≤
        1 + (shiftedSpectralPole ω a).re ^ 2 := by
      have hr2 : a.value.re ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hre.1.le (sub_nonneg.mpr hre.2.le)]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, halpha]
      nlinarith
    rw [shiftedXiPoleMeasure,
      integral_one_div_one_add_sq_lowerHalfPlanePole]
    calc
      (shiftedSpectralPoleDepth ω a + 1) /
          ((shiftedSpectralPole ω a).re ^ 2 +
            (shiftedSpectralPoleDepth ω a + 1) ^ 2) ≤
          C / (1 + (shiftedSpectralPole ω a).re ^ 2) := by
        rw [div_le_div_iff₀ hdenBig hdenSmall]
        calc
          (shiftedSpectralPoleDepth ω a + 1) *
              (1 + (shiftedSpectralPole ω a).re ^ 2) ≤
              C * (1 + (shiftedSpectralPole ω a).re ^ 2) :=
            mul_le_mul_of_nonneg_right hBC hdenSmall.le
          _ ≤ C * ((shiftedSpectralPole ω a).re ^ 2 +
              (shiftedSpectralPoleDepth ω a + 1) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hC
            nlinarith [sq_nonneg (shiftedSpectralPole ω a).re]
      _ ≤ C / ‖a.value‖ ^ 2 := by
        rw [div_le_div_iff₀ hdenSmall hnormpos]
        exact mul_le_mul_of_nonneg_left hnormle hC
      _ = C * (1 / ‖a.value‖ ^ 2) := by ring

/-- The countable positive Herglotz measure reconstructed from all shifted
xi poles. -/
noncomputable def shiftedXiHerglotzMeasure
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) : Measure ℝ :=
  Measure.sum (shiftedXiPoleMeasure ω hzero)

noncomputable instance shiftedXiHerglotzMeasure.instSFinite
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    SFinite (shiftedXiHerglotzMeasure ω hzero) := by
  unfold shiftedXiHerglotzMeasure
  infer_instance

/-- The countable shifted xi measure satisfies the standard Herglotz
integrability condition. -/
theorem integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) :
    Integrable (fun x : ℝ => 1 / (1 + x ^ 2))
      (shiftedXiHerglotzMeasure ω hzero) := by
  rw [shiftedXiHerglotzMeasure]
  apply integrable_sum_measure
  · intro a
    letI : IsFiniteMeasure (shiftedXiPoleMeasure ω hzero a) := by
      rw [shiftedXiPoleMeasure]
      infer_instance
    apply Integrable.of_bound (C := 1)
    · have hcont : Continuous (fun x : ℝ => 1 / (1 + x ^ 2)) := by
        exact continuous_const.div₀
          (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
      exact hcont.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
      nlinarith [sq_nonneg x]
  · refine (summable_shiftedXiPole_herglotzWeight hzero).congr fun a => ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- On the upper half-plane the standard Herglotz kernel is bounded by a
constant (depending only on `z`) times its defining weight. -/
theorem norm_herglotzKernel_le_weight
    {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    ‖herglotzKernel x z‖ ≤
      (((1 + ‖z‖ ^ 2) / z.im + ‖z‖) /
        (1 + x ^ 2)) := by
  let d : ℝ := ‖(x : ℂ) - z‖
  let C : ℝ := (1 + ‖z‖ ^ 2) / z.im + ‖z‖
  have hxz : (x : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hdpos : 0 < d := by
    exact norm_pos_iff.mpr hxz
  have hyd : z.im ≤ d := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub,
      abs_neg, abs_of_pos hz] at h
    exact h
  have hxnorm : |x| ≤ d + ‖z‖ := by
    calc
      |x| = ‖(x : ℂ)‖ := by simp
      _ = ‖((x : ℂ) - z) + z‖ := by congr 2 <;> ring
      _ ≤ ‖(x : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
      _ = d + ‖z‖ := by rfl
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hratio : 1 + |x| * ‖z‖ ≤ C * d := by
    have hdy : 1 ≤ d / z.im := by
      rw [le_div_iff₀ hz]
      simpa [mul_comm] using hyd
    have hbase : 1 + ‖z‖ ^ 2 ≤
        (1 + ‖z‖ ^ 2) * (d / z.im) :=
      by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hdy
            (show 0 ≤ 1 + ‖z‖ ^ 2 by positivity)
    calc
      1 + |x| * ‖z‖ ≤ 1 + (d + ‖z‖) * ‖z‖ := by
        gcongr
      _ = (1 + ‖z‖ ^ 2) + ‖z‖ * d := by ring
      _ ≤ (1 + ‖z‖ ^ 2) * (d / z.im) + ‖z‖ * d := by
        gcongr
      _ = C * d := by
        dsimp [C]
        field_simp
  have hid : herglotzKernel x z =
      (1 + (x : ℂ) * z) /
        (((x : ℂ) - z) * ((1 + x ^ 2 : ℝ) : ℂ)) := by
    rw [herglotzKernel]
    push_cast
    have hreal : (1 : ℂ) + (x : ℂ) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by
        push_cast
        rfl]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    field_simp [hxz, hreal] <;> ring
  rw [hid, norm_div, norm_mul]
  have hnormden : ‖((1 + x ^ 2 : ℝ) : ℂ)‖ = 1 + x ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
  rw [hnormden]
  have hnum : ‖1 + (x : ℂ) * z‖ ≤ 1 + |x| * ‖z‖ := by
    calc
      ‖1 + (x : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) * z‖ :=
        norm_add_le _ _
      _ = 1 + |x| * ‖z‖ := by simp
  have hnumC : ‖1 + (x : ℂ) * z‖ ≤ C * d := hnum.trans hratio
  change ‖1 + (x : ℂ) * z‖ / (d * (1 + x ^ 2)) ≤
    C / (1 + x ^ 2)
  rw [div_le_div_iff₀ (mul_pos hdpos (by positivity)) (by positivity)]
  calc
    ‖1 + (x : ℂ) * z‖ * (1 + x ^ 2) ≤
        (C * d) * (1 + x ^ 2) :=
      mul_le_mul_of_nonneg_right hnumC (by positivity)
    _ = C * (d * (1 + x ^ 2)) := by ring

theorem integrable_herglotzKernel_shiftedXiHerglotzMeasure
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun x : ℝ => herglotzKernel x z)
      (shiftedXiHerglotzMeasure ω hzero) := by
  let C : ℝ := (1 + ‖z‖ ^ 2) / z.im + ‖z‖
  have hdom : Integrable (fun x : ℝ => C * (1 / (1 + x ^ 2)))
      (shiftedXiHerglotzMeasure ω hzero) :=
    (integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure hzero).const_mul C
  apply Integrable.mono' hdom
  · have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
      intro x h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hsub : Continuous (fun x : ℝ => (x : ℂ) - z) :=
      Complex.continuous_ofReal.sub continuous_const
    have hcauchy : Continuous (fun x : ℝ => 1 / ((x : ℂ) - z)) :=
      continuous_const.div₀ hsub hne
    have hcorrReal : Continuous (fun x : ℝ => x / (1 + x ^ 2)) :=
      continuous_id.div₀
        (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
    have hcorr : Continuous (fun x : ℝ => ((x / (1 + x ^ 2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hcorrReal
    have hcont : Continuous (fun x : ℝ => herglotzKernel x z) := by
      unfold herglotzKernel
      exact hcauchy.sub hcorr
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    change ‖herglotzKernel x z‖ ≤ C * (1 / (1 + x ^ 2))
    simpa [C, div_eq_mul_inv] using norm_herglotzKernel_le_weight hz x

/-- The contribution of one shifted xi pole to the Herglotz integral. -/
noncomputable def shiftedXiPoleHerglotzTerm
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω)
    (z : ℂ) (a : XiZeroOccurrence) : ℂ :=
  ∫ x : ℝ, herglotzKernel x z ∂shiftedXiPoleMeasure ω hzero a

theorem summable_shiftedXiPoleHerglotzTerm
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (shiftedXiPoleHerglotzTerm ω hzero z) := by
  have hInt := integrable_herglotzKernel_shiftedXiHerglotzMeasure hzero hz
  rw [shiftedXiHerglotzMeasure] at hInt
  change Summable (fun a : XiZeroOccurrence =>
    ∫ x : ℝ, herglotzKernel x z ∂shiftedXiPoleMeasure ω hzero a)
  exact (hasSum_integral_measure hInt).summable

/-- Integration against the countable shifted measure is the ordinary sum
of its single-pole Herglotz contributions. -/
theorem integral_herglotzKernel_shiftedXiHerglotzMeasure_eq_tsum
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) :
    (∫ x : ℝ, herglotzKernel x z
        ∂shiftedXiHerglotzMeasure ω hzero) =
      ∑' a : XiZeroOccurrence,
        shiftedXiPoleHerglotzTerm ω hzero z a := by
  have hInt := integrable_herglotzKernel_shiftedXiHerglotzMeasure hzero hz
  rw [shiftedXiHerglotzMeasure] at hInt ⊢
  exact integral_sum_measure hInt

/-- The real correction attached to a functional-equation reflection pair. -/
noncomputable def shiftedXiHerglotzPairCorrection
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω)
    (a : XiZeroOccurrence) : ℝ :=
  shiftedXiPoleRealCorrection ω hzero a +
    shiftedXiPoleRealCorrection ω hzero (xiOccurrenceOneSubEquiv a)

private theorem summable_shiftedXiProjectTerm
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (fun a : XiZeroOccurrence =>
      xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a) := by
  apply summable_xiSpectralCorrectedTerm
  have hne := riemannXi_shifted_center_ne_zero_of_zeroFreeRight hzero hz
  convert hne using 1
  push_cast
  rw [mul_add, ← mul_assoc, I_mul_I]
  ring

theorem summable_shiftedXiHerglotzPairCorrection
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) :
    Summable (shiftedXiHerglotzPairCorrection ω hzero) := by
  let z : ℂ := Complex.I
  have hz : 0 < z.im := by simp [z]
  let P : XiZeroOccurrence → ℂ := fun a =>
    xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a
  let H : XiZeroOccurrence → ℂ :=
    shiftedXiPoleHerglotzTerm ω hzero z
  have hP : Summable P := by
    simpa [P] using summable_shiftedXiProjectTerm hzero hz
  have hPr : Summable (fun a => P (xiOccurrenceOneSubEquiv a)) :=
    hP.comp_injective xiOccurrenceOneSubEquiv.injective
  have hH : Summable H := by
    simpa [H] using summable_shiftedXiPoleHerglotzTerm hzero hz
  have hHr : Summable (fun a => H (xiOccurrenceOneSubEquiv a)) :=
    hH.comp_injective xiOccurrenceOneSubEquiv.injective
  have hc : Summable (fun a : XiZeroOccurrence =>
      (shiftedXiHerglotzPairCorrection ω hzero a : ℂ)) := by
    apply (hP.add hPr |>.sub (hH.add hHr)).congr
    intro a
    have ha := integral_herglotzKernel_shiftedXiPole hzero a hz
    have har := integral_herglotzKernel_shiftedXiPole hzero
      (xiOccurrenceOneSubEquiv a) hz
    have hpair :
        xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
            xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
              (xiOccurrenceOneSubEquiv a) =
          1 / (shiftedSpectralPole ω a - z) +
            1 / (shiftedSpectralPole ω
              (xiOccurrenceOneSubEquiv a) - z) := by
      simp only [shiftedSpectralPole, xiSpectralCorrectedTerm,
        xiSpectralParameterShifted,
        xiSpectralParameter_oneSubOccurrence, one_div, inv_neg]
      ring
    dsimp [P, H, shiftedXiPoleHerglotzTerm] at *
    rw [hpair, ha, har]
    simp only [shiftedXiHerglotzPairCorrection]
    push_cast
    ring
  exact Complex.summable_ofReal.mp hc

/-- The real constant in the specialized shifted Herglotz representation. -/
noncomputable def shiftedXiHerglotzConstant
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) : ℝ :=
  (1 / 2 : ℝ) *
    ∑' a : XiZeroOccurrence,
      shiftedXiHerglotzPairCorrection ω hzero a

/-- Specialized Herglotz representation of the shifted xi logarithmic
derivative.  Reflection pairing shows directly that the affine Herglotz
slope is zero; only a real constant remains. -/
theorem xiNevanlinnaQShifted_eq_herglotzRepresentation
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) :
    xiNevanlinnaQShifted ω z =
      (shiftedXiHerglotzConstant ω hzero : ℂ) +
        ∫ x : ℝ, herglotzKernel x z
          ∂shiftedXiHerglotzMeasure ω hzero := by
  let P : XiZeroOccurrence → ℂ := fun a =>
    xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a
  let H : XiZeroOccurrence → ℂ :=
    shiftedXiPoleHerglotzTerm ω hzero z
  let C : XiZeroOccurrence → ℝ :=
    shiftedXiHerglotzPairCorrection ω hzero
  have hP : Summable P := by
    simpa [P] using summable_shiftedXiProjectTerm hzero hz
  have hPr : Summable (fun a => P (xiOccurrenceOneSubEquiv a)) :=
    hP.comp_injective xiOccurrenceOneSubEquiv.injective
  have hH : Summable H := by
    simpa [H] using summable_shiftedXiPoleHerglotzTerm hzero hz
  have hHr : Summable (fun a => H (xiOccurrenceOneSubEquiv a)) :=
    hH.comp_injective xiOccurrenceOneSubEquiv.injective
  have hC : Summable C := by
    simpa [C] using summable_shiftedXiHerglotzPairCorrection hzero
  have hCc : Summable (fun a => (C a : ℂ)) :=
    Complex.summable_ofReal.mpr hC
  have hpair : ∀ a : XiZeroOccurrence,
      P a + P (xiOccurrenceOneSubEquiv a) =
        H a + H (xiOccurrenceOneSubEquiv a) + (C a : ℂ) := by
    intro a
    have ha := integral_herglotzKernel_shiftedXiPole hzero a hz
    have har := integral_herglotzKernel_shiftedXiPole hzero
      (xiOccurrenceOneSubEquiv a) hz
    have hproject :
        xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
            xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
              (xiOccurrenceOneSubEquiv a) =
          1 / (shiftedSpectralPole ω a - z) +
            1 / (shiftedSpectralPole ω
              (xiOccurrenceOneSubEquiv a) - z) := by
      simp only [shiftedSpectralPole, xiSpectralCorrectedTerm,
        xiSpectralParameterShifted,
        xiSpectralParameter_oneSubOccurrence, one_div, inv_neg]
      ring
    dsimp [P, H, C, shiftedXiPoleHerglotzTerm,
      shiftedXiHerglotzPairCorrection]
    rw [hproject, ha, har]
    push_cast
    ring
  have hQP : xiNevanlinnaQShifted ω z = ∑' a, P a := by
    simpa [P] using xiNevanlinnaQShifted_eq_spectral_sum hzero hz
  have hIH :
      (∫ x : ℝ, herglotzKernel x z
          ∂shiftedXiHerglotzMeasure ω hzero) = ∑' a, H a := by
    simpa [H, shiftedXiPoleHerglotzTerm] using
      integral_herglotzKernel_shiftedXiHerglotzMeasure_eq_tsum hzero hz
  have hsumPairP :
      (∑' a, (P a + P (xiOccurrenceOneSubEquiv a))) =
        2 * ∑' a, P a := by
    rw [hP.tsum_add hPr,
      xiOccurrenceOneSubEquiv.tsum_eq P]
    ring
  have hsumPairH :
      (∑' a, (H a + H (xiOccurrenceOneSubEquiv a))) =
        2 * ∑' a, H a := by
    rw [hH.tsum_add hHr,
      xiOccurrenceOneSubEquiv.tsum_eq H]
    ring
  have hsumPair :
      (∑' a, (P a + P (xiOccurrenceOneSubEquiv a))) =
        (∑' a, (H a + H (xiOccurrenceOneSubEquiv a))) +
          ∑' a, (C a : ℂ) := by
    calc
      _ = ∑' a, ((H a + H (xiOccurrenceOneSubEquiv a)) +
          (C a : ℂ)) := tsum_congr hpair
      _ = _ := (hH.add hHr).tsum_add hCc
  have hCcast : (∑' a, (C a : ℂ)) =
      2 * (shiftedXiHerglotzConstant ω hzero : ℂ) := by
    rw [← Complex.ofReal_tsum]
    simp only [C, shiftedXiHerglotzConstant]
    push_cast
    ring
  rw [hsumPairP, hsumPairH, ← hQP, ← hIH, hCcast] at hsumPair
  linear_combination (1 / 2 : ℂ) * hsumPair

/-- The continuously extended rank-one Fourier feature.  The integral
definition gives the value `-i t` at `x = 0` without a case split. -/
noncomputable def shiftedScrewFeature (x t : ℝ) : ℂ :=
  (-Complex.I * (t : ℂ)) *
    ∫ s : ℝ in (0 : ℝ)..1,
      Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))

@[simp] theorem shiftedScrewFeature_zero (t : ℝ) :
    shiftedScrewFeature 0 t = -Complex.I * (t : ℂ) := by
  simp [shiftedScrewFeature]

@[simp] theorem shiftedScrewFeature_zero_time (x : ℝ) :
    shiftedScrewFeature x 0 = 0 := by
  simp [shiftedScrewFeature]

theorem shiftedScrewFeature_eq_div {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    shiftedScrewFeature x t =
      (Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1) / (x : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp [shiftedScrewFeature]
  · have hc : -Complex.I * ((x * t : ℝ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr (mul_ne_zero hx ht))
    rw [shiftedScrewFeature,
      integral_exp_mul_complex (a := 0) (b := 1) hc]
    norm_num
    field_simp [hx, ht, Complex.I_ne_zero]

theorem continuous_shiftedScrewFeature (t : ℝ) :
    Continuous (fun x : ℝ => shiftedScrewFeature x t) := by
  unfold shiftedScrewFeature
  fun_prop

theorem norm_shiftedScrewFeature_le_time (x t : ℝ) :
    ‖shiftedScrewFeature x t‖ ≤ |t| := by
  have hInt :
      ‖∫ s : ℝ in (0 : ℝ)..1,
          Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))‖ ≤ 1 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := (1 : ℝ))
      (f := fun s : ℝ =>
        Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ)))
      (fun s _ => by
        rw [Complex.norm_exp]
        simp)
    simpa using h
  rw [shiftedScrewFeature, norm_mul]
  have hpref : ‖-Complex.I * (t : ℂ)‖ = |t| := by simp
  rw [hpref]
  simpa using mul_le_mul_of_nonneg_left hInt (abs_nonneg t)

theorem norm_shiftedScrewFeature_le_two_div
    {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    ‖shiftedScrewFeature x t‖ ≤ 2 / |x| := by
  rw [shiftedScrewFeature_eq_div hx, norm_div, Complex.norm_real,
    Real.norm_eq_abs]
  apply (div_le_div_iff₀ (abs_pos.mpr hx) (abs_pos.mpr hx)).2
  have hnum : ‖Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp]
        norm_num
  exact mul_le_mul_of_nonneg_right hnum (abs_nonneg x)

theorem norm_shiftedScrewFeature_mul_conj_le_weight
    (x t u : ℝ) :
    ‖shiftedScrewFeature x t *
        starRingEnd ℂ (shiftedScrewFeature x u)‖ ≤
      (2 * |t| * |u| + 8) / (1 + x ^ 2) := by
  have hD : 0 ≤ 2 * |t| * |u| + 8 := by positivity
  rw [norm_mul]
  have hstar :
      ‖starRingEnd ℂ (shiftedScrewFeature x u)‖ =
        ‖shiftedScrewFeature x u‖ := by
    simp
  rw [hstar]
  by_cases hxsmall : |x| ≤ 1
  · have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxsmall
    have hp : ‖shiftedScrewFeature x t‖ *
        ‖shiftedScrewFeature x u‖ ≤ |t| * |u| :=
      mul_le_mul (norm_shiftedScrewFeature_le_time x t)
        (norm_shiftedScrewFeature_le_time x u)
        (norm_nonneg _) (abs_nonneg _)
    rw [le_div_iff₀ (by positivity)]
    calc
      ‖shiftedScrewFeature x t‖ * ‖shiftedScrewFeature x u‖ *
          (1 + x ^ 2) ≤ |t| * |u| * (1 + x ^ 2) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ |t| * |u| * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg t) (abs_nonneg u))
      _ ≤ 2 * |t| * |u| + 8 := by nlinarith [abs_nonneg t, abs_nonneg u]
  · have hxabs : 1 < |x| := lt_of_not_ge hxsmall
    have hx : x ≠ 0 := abs_pos.mp (lt_trans zero_lt_one hxabs)
    have hp : ‖shiftedScrewFeature x t‖ *
        ‖shiftedScrewFeature x u‖ ≤
          (2 / |x|) * (2 / |x|) :=
      mul_le_mul (norm_shiftedScrewFeature_le_two_div hx t)
        (norm_shiftedScrewFeature_le_two_div hx u)
        (norm_nonneg _) (by positivity)
    have hsq : 1 ≤ x ^ 2 :=
      (one_le_sq_iff_one_le_abs x).2 (le_of_lt hxabs)
    have hfrac : (2 / |x|) * (2 / |x|) * (1 + x ^ 2) ≤ 8 := by
      rw [show (2 / |x|) * (2 / |x|) = 4 / x ^ 2 by
        calc
          (2 / |x|) * (2 / |x|) = 4 / |x| ^ 2 := by ring
          _ = 4 / x ^ 2 := by rw [sq_abs]]
      rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_ne_zero hx)]
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc
      ‖shiftedScrewFeature x t‖ * ‖shiftedScrewFeature x u‖ *
          (1 + x ^ 2) ≤
          ((2 / |x|) * (2 / |x|)) * (1 + x ^ 2) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ 8 := hfrac
      _ ≤ 2 * |t| * |u| + 8 := by
        nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg u)]

theorem integrable_shiftedScrewFeature_mul_conj
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) (t u : ℝ) :
    Integrable (fun x : ℝ =>
      shiftedScrewFeature x t *
        starRingEnd ℂ (shiftedScrewFeature x u))
      (shiftedXiHerglotzMeasure ω hzero) := by
  let C : ℝ := 2 * |t| * |u| + 8
  have hdom : Integrable (fun x : ℝ => C * (1 / (1 + x ^ 2)))
      (shiftedXiHerglotzMeasure ω hzero) :=
    (integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure hzero).const_mul C
  apply Integrable.mono' hdom
  · exact ((continuous_shiftedScrewFeature t).mul
      ((continuous_shiftedScrewFeature u).star)).aestronglyMeasurable
  · filter_upwards with x
    simpa [C, div_eq_mul_inv] using
      norm_shiftedScrewFeature_mul_conj_le_weight x t u

/-- The positive rank-one kernel reconstructed from the shifted xi Herglotz
measure. -/
noncomputable def shiftedHerglotzKernel
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) (t u : ℝ) : ℂ :=
  ∫ x : ℝ,
    shiftedScrewFeature x t *
      starRingEnd ℂ (shiftedScrewFeature x u)
    ∂shiftedXiHerglotzMeasure ω hzero

private theorem shiftedFeature_double_sum_eq_normSq
    (x : ℝ) (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ) :
    (∑ i, ∑ j,
        (shiftedScrewFeature x (t i) *
          starRingEnd ℂ (shiftedScrewFeature x (t j))) *
          c i * starRingEnd ℂ (c j)) =
      (Complex.normSq
        (∑ i, shiftedScrewFeature x (t i) * c i) : ℂ) := by
  rw [← Complex.mul_conj]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

/-- The kernel reconstructed from the positive shifted-xi Herglotz measure
is positive semidefinite on every finite set of sample points. -/
theorem shiftedHerglotzKernel_psd
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) :
    KernelPSD (shiftedHerglotzKernel ω hzero) := by
  intro N t c
  let μ := shiftedXiHerglotzMeasure ω hzero
  have hInt (i j : Fin N) : Integrable (fun x : ℝ =>
      (shiftedScrewFeature x (t i) *
        starRingEnd ℂ (shiftedScrewFeature x (t j))) *
        c i * starRingEnd ℂ (c j)) μ :=
    ((integrable_shiftedScrewFeature_mul_conj hzero (t i) (t j)).mul_const
      (c i)).mul_const (starRingEnd ℂ (c j))
  have hSumInt : Integrable (fun x : ℝ =>
      ∑ i, ∑ j,
        (shiftedScrewFeature x (t i) *
          starRingEnd ℂ (shiftedScrewFeature x (t j))) *
          c i * starRingEnd ℂ (c j)) μ :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hInt i j
  have hIntegral :
      (∑ i, ∑ j,
          shiftedHerglotzKernel ω hzero (t i) (t j) * c i *
            starRingEnd ℂ (c j)) =
        ∫ x : ℝ, ∑ i, ∑ j,
          (shiftedScrewFeature x (t i) *
            starRingEnd ℂ (shiftedScrewFeature x (t j))) *
            c i * starRingEnd ℂ (c j) ∂μ := by
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ fun j _ => hInt i j)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j _ => hInt i j)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [shiftedHerglotzKernel, μ]
    rw [integral_mul_const, integral_mul_const]
  rw [hIntegral]
  change 0 ≤ RCLike.re (∫ x : ℝ, ∑ i, ∑ j,
    (shiftedScrewFeature x (t i) *
      starRingEnd ℂ (shiftedScrewFeature x (t j))) *
      c i * starRingEnd ℂ (c j) ∂μ)
  rw [← integral_re hSumInt]
  apply integral_nonneg
  intro x
  change 0 ≤ (∑ i, ∑ j,
    (shiftedScrewFeature x (t i) *
      starRingEnd ℂ (shiftedScrewFeature x (t j))) *
      c i * starRingEnd ℂ (c j)).re
  rw [shiftedFeature_double_sum_eq_normSq]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

private theorem integral_one_sub_mul_cexp {c : ℂ} (hc : c ≠ 0) :
    (∫ s : ℝ in (0 : ℝ)..1,
        ((1 : ℂ) - (s : ℂ)) * Complex.exp (c * (s : ℂ))) =
      (Complex.exp c - 1 - c) / c ^ 2 := by
  let P : ℝ → ℂ := fun s ↦
    Complex.exp (c * (s : ℂ)) *
      (((1 : ℂ) - (s : ℂ)) / c + 1 / c ^ 2)
  have hderiv : ∀ s : ℝ,
      HasDerivAt P
        (((1 : ℂ) - (s : ℂ)) * Complex.exp (c * (s : ℂ))) s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ ↦ c * (r : ℂ)) c s := by
      simpa using ((hasDerivAt_id s).ofReal_comp.const_mul c)
    have hexp : HasDerivAt (fun r : ℝ ↦ Complex.exp (c * (r : ℂ)))
        (c * Complex.exp (c * (s : ℂ))) s := by
      simpa [mul_comm] using hlin.cexp
    have haff : HasDerivAt
        (fun r : ℝ ↦ ((1 : ℂ) - (r : ℂ)) / c + 1 / c ^ 2)
        (-1 / c) s := by
      have hbase : HasDerivAt (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ)) (-1) s := by
        simpa using ((hasDerivAt_id s).ofReal_comp.const_sub (1 : ℂ))
      simpa using (hbase.div_const c).const_add (1 / c ^ 2)
    dsimp only [P]
    exact (hexp.mul haff).congr_deriv (by
      field_simp [hc]
      ring)
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ ((1 : ℂ) - (s : ℂ)) *
        Complex.exp (c * (s : ℂ))) volume 0 1 := by
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((1 : ℂ) - (s : ℂ)) * Complex.exp (c * (s : ℂ)))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hderiv s) hint
  rw [hFTC]
  dsimp only [P]
  norm_num
  field_simp [hc]
  ring

/-- The normalized screw atom associated with a real Herglotz spectral
point.  Its integral-remainder definition is continuous at `x = 0`; the
apparent reciprocal singularities cancel there. -/
noncomputable def shiftedHerglotzScrewAtom (x t : ℝ) : ℂ :=
  -((t ^ 2 : ℝ) : ℂ) *
      (∫ s : ℝ in (0 : ℝ)..1,
        ((1 : ℂ) - (s : ℂ)) *
          Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))) -
    Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ)

theorem shiftedHerglotzScrewAtom_eq
    {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    shiftedHerglotzScrewAtom x t =
      (Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1) / (x : ℂ) ^ 2 +
        Complex.I * (t : ℂ) /
          ((x : ℂ) * (1 + (x : ℂ) ^ 2)) := by
  by_cases ht : t = 0
  · subst t
    simp [shiftedHerglotzScrewAtom]
  · have hc : -Complex.I * ((x * t : ℝ) : ℂ) ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr (mul_ne_zero hx ht))
    have hrem :
        (∫ s : ℝ in (0 : ℝ)..1,
          ((1 : ℂ) - (s : ℂ)) *
            Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))) =
          (Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1 -
            (-Complex.I * ((x * t : ℝ) : ℂ))) /
            (-Complex.I * ((x * t : ℝ) : ℂ)) ^ 2 := by
      convert integral_one_sub_mul_cexp
        (c := -Complex.I * ((x * t : ℝ) : ℂ)) hc using 1 <;> ring
    rw [shiftedHerglotzScrewAtom]
    calc
      -((t ^ 2 : ℝ) : ℂ) *
            (∫ s : ℝ in (0 : ℝ)..1,
              ((1 : ℂ) - (s : ℂ)) *
                Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))) -
          Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ) =
        -((t ^ 2 : ℝ) : ℂ) *
            ((Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1 -
              (-Complex.I * ((x * t : ℝ) : ℂ))) /
              (-Complex.I * ((x * t : ℝ) : ℂ)) ^ 2) -
          Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ) := by
            exact congrArg (fun q : ℂ =>
              -((t ^ 2 : ℝ) : ℂ) * q -
                Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ)) hrem
      _ = _ := by
        push_cast
        have hden : (1 + (x : ℂ) ^ 2) ≠ 0 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_add]
          exact Complex.ofReal_ne_zero.mpr (by positivity)
        field_simp [hx, ht, Complex.I_ne_zero, hden]
        rw [Complex.I_sq, Complex.I_pow_three]
        field_simp [hden]
        ring

theorem continuous_shiftedHerglotzScrewAtom (t : ℝ) :
    Continuous (fun x : ℝ => shiftedHerglotzScrewAtom x t) := by
  have hInt : Continuous (fun x : ℝ =>
      ∫ s : ℝ in (0 : ℝ)..1,
        ((1 : ℂ) - (s : ℂ)) *
          Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))) := by
    fun_prop
  have hrat : Continuous (fun x : ℝ => x / (1 + x ^ 2)) := by
    exact continuous_id.div (continuous_const.add (continuous_id.pow 2))
      (fun x => by positivity)
  have hleft : Continuous (fun x : ℝ =>
      -((t ^ 2 : ℝ) : ℂ) *
        ∫ s : ℝ in (0 : ℝ)..1,
          ((1 : ℂ) - (s : ℂ)) *
            Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))) :=
    continuous_const.mul hInt
  have hright : Continuous (fun x : ℝ =>
      Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ)) :=
    (continuous_const.mul continuous_const).mul
      (Complex.continuous_ofReal.comp hrat)
  unfold shiftedHerglotzScrewAtom
  apply Continuous.sub
  · exact hleft
  · exact hright

theorem continuous_shiftedHerglotzScrewAtom_time (x : ℝ) :
    Continuous (fun t : ℝ => shiftedHerglotzScrewAtom x t) := by
  unfold shiftedHerglotzScrewAtom
  fun_prop

@[simp] theorem shiftedHerglotzScrewAtom_zero_time (x : ℝ) :
    shiftedHerglotzScrewAtom x 0 = 0 := by
  simp [shiftedHerglotzScrewAtom]

@[simp] theorem shiftedHerglotzScrewAtom_zero (t : ℝ) :
    shiftedHerglotzScrewAtom 0 t = -((t ^ 2 : ℝ) : ℂ) / 2 := by
  rw [shiftedHerglotzScrewAtom]
  have hInt :
      (∫ s : ℝ in (0 : ℝ)..1, ((1 : ℂ) - (s : ℂ))) = (1 / 2 : ℂ) := by
    have hreal : (∫ s : ℝ in (0 : ℝ)..1, (1 - s : ℝ)) = (1 / 2 : ℝ) := by
      let P : ℝ → ℝ := fun s => s - s ^ 2 / 2
      have hderiv : ∀ s : ℝ, HasDerivAt P (1 - s) s := by
        intro s
        dsimp only [P]
        have hsq : HasDerivAt (fun r : ℝ => r ^ 2 / 2) s s :=
          ((hasDerivAt_pow 2 s).div_const 2).congr_deriv (by norm_num)
        exact (hasDerivAt_id s).sub hsq
      have hint : IntervalIntegrable (fun s : ℝ => 1 - s) volume 0 1 :=
        (continuous_const.sub continuous_id).intervalIntegrable _ _
      calc
        _ = P 1 - P 0 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun s _ => hderiv s) hint
        _ = 1 / 2 := by norm_num [P]
    have hfun : (fun s : ℝ => (1 : ℂ) - (s : ℂ)) =
        (fun s : ℝ => ((1 - s : ℝ) : ℂ)) := by
      funext s
      push_cast
      rfl
    rw [hfun]
    calc
      _ = Complex.ofReal (∫ s : ℝ in (0 : ℝ)..1, (1 - s : ℝ)) :=
        @RCLike.intervalIntegral_ofReal ℂ _ 0 1 volume (fun s : ℝ => 1 - s)
      _ = (1 / 2 : ℂ) := by rw [hreal]; norm_num
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.ofReal_div, Complex.ofReal_one]
  have hIntOne :
      (∫ s : ℝ in (0 : ℝ)..1, ((1 : ℂ) - (s : ℂ)) * 1) = (1 / 2 : ℂ) := by
    simpa only [mul_one] using hInt
  rw [hIntOne]
  push_cast
  ring

theorem shiftedHerglotzScrewAtom_neg (x t : ℝ) :
    shiftedHerglotzScrewAtom x (-t) =
      starRingEnd ℂ (shiftedHerglotzScrewAtom x t) := by
  by_cases hx : x = 0
  · subst x
    simp [shiftedHerglotzScrewAtom_zero]
    rw [map_ofNat]
  · rw [shiftedHerglotzScrewAtom_eq hx,
      shiftedHerglotzScrewAtom_eq hx]
    change _ = conj _
    simp only [map_add, RCLike.conj_div, map_sub, map_neg, map_one, map_mul, map_pow,
      Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj]
    push_cast
    congr 1 <;> ring

theorem shiftedHerglotzScrewAtom_kernel
    (x t u : ℝ) :
    shiftedHerglotzScrewAtom x (t - u) -
          shiftedHerglotzScrewAtom x t -
          shiftedHerglotzScrewAtom x (-u) +
          shiftedHerglotzScrewAtom x 0 =
      shiftedScrewFeature x t *
        starRingEnd ℂ (shiftedScrewFeature x u) := by
  by_cases hx : x = 0
  · subst x
    simp only [shiftedHerglotzScrewAtom_zero,
      shiftedHerglotzScrewAtom_zero_time, shiftedScrewFeature_zero]
    have hstar : starRingEnd ℂ (-Complex.I * (u : ℂ)) =
        Complex.I * (u : ℂ) := by
      simp
    rw [hstar]
    push_cast
    have hprod : -Complex.I * (t : ℂ) *
        (Complex.I * (u : ℂ)) = (t : ℂ) * (u : ℂ) := by
      calc
        _ = -(Complex.I * Complex.I) * ((t : ℂ) * (u : ℂ)) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [hprod]
    ring
  · rw [shiftedHerglotzScrewAtom_eq hx,
      shiftedHerglotzScrewAtom_eq hx,
      shiftedHerglotzScrewAtom_eq hx,
      shiftedHerglotzScrewAtom_zero_time,
      shiftedScrewFeature_eq_div hx,
      shiftedScrewFeature_eq_div hx]
    have hconj : starRingEnd ℂ
        ((Complex.exp (-Complex.I * ((x * u : ℝ) : ℂ)) - 1) / (x : ℂ)) =
        (Complex.exp (Complex.I * ((x * u : ℝ) : ℂ)) - 1) / (x : ℂ) := by
      change conj
          ((Complex.exp (-Complex.I * ((x * u : ℝ) : ℂ)) - 1) / (x : ℂ)) = _
      rw [RCLike.conj_div, map_sub, map_one, Complex.conj_ofReal,
        ← Complex.exp_conj]
      congr 2
      simp
    rw [hconj]
    have hexpdiff :
        Complex.exp (-Complex.I * ((x * (t - u) : ℝ) : ℂ)) =
          Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((x * u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hexpneg :
        Complex.exp (-Complex.I * ((x * (-u) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((x * u : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hexpdiff, hexpneg]
    push_cast
    field_simp [hx]
    ring

theorem norm_shiftedHerglotzScrewAtom_le_weight
    (x t : ℝ) :
    ‖shiftedHerglotzScrewAtom x t‖ ≤
      (2 * t ^ 2 + 2 * |t| + 4) / (1 + x ^ 2) := by
  have hratio : |x / (1 + x ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 1 + x ^ 2),
      div_le_one (by positivity : 0 < 1 + x ^ 2)]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hC : 0 ≤ 2 * t ^ 2 + 2 * |t| + 4 := by positivity
  by_cases hxsmall : |x| ≤ 1
  · have hJ :
        ‖∫ s : ℝ in (0 : ℝ)..1,
          ((1 : ℂ) - (s : ℂ)) *
            Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))‖ ≤ 1 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := (1 : ℝ))
        (f := fun s : ℝ =>
          ((1 : ℂ) - (s : ℂ)) *
            Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ)))
        (fun s hs => by
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le zero_le_one] at hs
            exact ⟨hs.1.le, hs.2⟩
          have hsub : ‖(1 : ℂ) - (s : ℂ)‖ = 1 - s := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
              Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [hs'.2] : 0 ≤ 1 - s)]
          have hexp :
              ‖Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [norm_mul, hsub, hexp, mul_one]
          linarith [hs'.1, hs'.2])
      simpa using h
    have hatom : ‖shiftedHerglotzScrewAtom x t‖ ≤ t ^ 2 + |t| := by
      rw [shiftedHerglotzScrewAtom]
      calc
        _ ≤ ‖-((t ^ 2 : ℝ) : ℂ) *
              (∫ s : ℝ in (0 : ℝ)..1,
                ((1 : ℂ) - (s : ℂ)) *
                  Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ)))‖ +
              ‖Complex.I * (t : ℂ) * ((x / (1 + x ^ 2) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
        _ = t ^ 2 * ‖∫ s : ℝ in (0 : ℝ)..1,
                ((1 : ℂ) - (s : ℂ)) *
                  Complex.exp ((-Complex.I * ((x * t : ℝ) : ℂ)) * (s : ℂ))‖ +
              |t| * |x / (1 + x ^ 2)| := by
          simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg t), Complex.norm_I, one_mul]
        _ ≤ t ^ 2 * 1 + |t| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hJ (sq_nonneg t))
            (mul_le_mul_of_nonneg_left hratio (abs_nonneg t))
        _ = t ^ 2 + |t| := by ring
    have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxsmall
    rw [le_div_iff₀ (by positivity)]
    calc
      ‖shiftedHerglotzScrewAtom x t‖ * (1 + x ^ 2) ≤
          (t ^ 2 + |t|) * (1 + x ^ 2) :=
        mul_le_mul_of_nonneg_right hatom (by positivity)
      _ ≤ (t ^ 2 + |t|) * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (add_nonneg (sq_nonneg t) (abs_nonneg t))
      _ ≤ 2 * t ^ 2 + 2 * |t| + 4 := by
        nlinarith [sq_nonneg t, abs_nonneg t]
  · have hxabs : 1 < |x| := lt_of_not_ge hxsmall
    have hx : x ≠ 0 := abs_pos.mp (lt_trans zero_lt_one hxabs)
    have hsq : 1 ≤ x ^ 2 :=
      (one_le_sq_iff_one_le_abs x).2 (le_of_lt hxabs)
    have hnum :
        ‖Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp]; norm_num
    have hfirst :
        ‖(Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1) /
            (x : ℂ) ^ 2‖ ≤ 2 / x ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg x)
    have hsecond :
        ‖Complex.I * (t : ℂ) /
            ((x : ℂ) * (1 + (x : ℂ) ^ 2))‖ =
          |t| / (|x| * (1 + x ^ 2)) := by
      have hdennorm : ‖(1 : ℂ) + (x : ℂ) ^ 2‖ = 1 + x ^ 2 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_add,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
      simp only [norm_div, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, hdennorm]
    rw [shiftedHerglotzScrewAtom_eq hx]
    have hatom : ‖(Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) - 1) /
            (x : ℂ) ^ 2 + Complex.I * (t : ℂ) /
              ((x : ℂ) * (1 + (x : ℂ) ^ 2))‖ ≤
          2 / x ^ 2 + |t| / (|x| * (1 + x ^ 2)) :=
      (norm_add_le _ _).trans (add_le_add hfirst hsecond.le)
    rw [le_div_iff₀ (by positivity)]
    calc
      _ ≤ (2 / x ^ 2 + |t| / (|x| * (1 + x ^ 2))) *
          (1 + x ^ 2) := mul_le_mul_of_nonneg_right hatom (by positivity)
      _ = 2 * (1 + x ^ 2) / x ^ 2 + |t| / |x| := by
        field_simp [hx, ne_of_gt (lt_trans zero_lt_one hxabs)]
      _ ≤ 4 + |t| := by
        have hfirst' : 2 * (1 + x ^ 2) / x ^ 2 ≤ 4 := by
          rw [div_le_iff₀ (sq_pos_of_ne_zero hx)]
          nlinarith
        have hsecond' : |t| / |x| ≤ |t| := by
          exact (div_le_iff₀ (lt_trans zero_lt_one hxabs)).2
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (le_of_lt hxabs) (abs_nonneg t))
        exact add_le_add hfirst' hsecond'
      _ ≤ 2 * t ^ 2 + 2 * |t| + 4 := by
        have hnonneg : 0 ≤ 2 * t ^ 2 + |t| :=
          add_nonneg (mul_nonneg (by norm_num) (sq_nonneg t)) (abs_nonneg t)
        linarith

theorem integrable_shiftedHerglotzScrewAtom
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) (t : ℝ) :
    Integrable (fun x : ℝ => shiftedHerglotzScrewAtom x t)
      (shiftedXiHerglotzMeasure ω hzero) := by
  let C : ℝ := 2 * t ^ 2 + 2 * |t| + 4
  have hdom : Integrable (fun x : ℝ => C * (1 / (1 + x ^ 2)))
      (shiftedXiHerglotzMeasure ω hzero) :=
    (integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure hzero).const_mul C
  apply Integrable.mono' hdom
  · exact (continuous_shiftedHerglotzScrewAtom t).aestronglyMeasurable
  · filter_upwards with x
    simpa [C, div_eq_mul_inv] using
      norm_shiftedHerglotzScrewAtom_le_weight x t

/-- The screw function reconstructed from the shifted-xi Herglotz
representation.  The imaginary linear term realizes the real Herglotz
constant and disappears from its translation-difference kernel. -/
noncomputable def shiftedHerglotzScrew
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) (t : ℝ) : ℂ :=
  Complex.I * (shiftedXiHerglotzConstant ω hzero : ℂ) * (t : ℂ) +
    ∫ x : ℝ, shiftedHerglotzScrewAtom x t
      ∂shiftedXiHerglotzMeasure ω hzero

@[simp] theorem shiftedHerglotzScrew_zero
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    shiftedHerglotzScrew ω hzero 0 = 0 := by
  simp [shiftedHerglotzScrew]

theorem screwKernel_shiftedHerglotzScrew
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    screwKernel (shiftedHerglotzScrew ω hzero) =
      shiftedHerglotzKernel ω hzero := by
  funext t u
  let μ := shiftedXiHerglotzMeasure ω hzero
  have htu := integrable_shiftedHerglotzScrewAtom hzero (t - u)
  have ht := integrable_shiftedHerglotzScrewAtom hzero t
  have hnu := integrable_shiftedHerglotzScrewAtom hzero (-u)
  have h0 := integrable_shiftedHerglotzScrewAtom hzero 0
  have hIntegral :
      (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) ∂μ) -
          (∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) -
          (∫ x : ℝ, shiftedHerglotzScrewAtom x (-u) ∂μ) +
          (∫ x : ℝ, shiftedHerglotzScrewAtom x 0 ∂μ) =
        shiftedHerglotzKernel ω hzero t u := by
    have hsub₁ := integral_sub htu ht
    have hsub₂ := integral_sub (htu.sub ht) hnu
    have hadd := integral_add ((htu.sub ht).sub hnu) h0
    have hsub₁' :
        (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) -
          shiftedHerglotzScrewAtom x t ∂μ) =
        (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) ∂μ) -
          ∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ := by
      simpa only [Pi.sub_apply] using hsub₁
    have hsub₂' :
        (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) -
            shiftedHerglotzScrewAtom x t -
            shiftedHerglotzScrewAtom x (-u) ∂μ) =
          ((∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) ∂μ) -
            ∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) -
            ∫ x : ℝ, shiftedHerglotzScrewAtom x (-u) ∂μ := by
      calc
        _ = (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) -
              shiftedHerglotzScrewAtom x t ∂μ) -
              ∫ x : ℝ, shiftedHerglotzScrewAtom x (-u) ∂μ := by
            simpa only [μ, Pi.sub_apply] using hsub₂
        _ = _ := by rw [hsub₁']
    have hadd' :
        (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) -
            shiftedHerglotzScrewAtom x t -
            shiftedHerglotzScrewAtom x (-u) +
            shiftedHerglotzScrewAtom x 0 ∂μ) =
          (∫ x : ℝ, shiftedHerglotzScrewAtom x (t - u) -
            shiftedHerglotzScrewAtom x t -
            shiftedHerglotzScrewAtom x (-u) ∂μ) +
            ∫ x : ℝ, shiftedHerglotzScrewAtom x 0 ∂μ := by
      simpa only [μ, Pi.sub_apply, Pi.add_apply] using hadd
    calc
      _ = ∫ x : ℝ,
          shiftedHerglotzScrewAtom x (t - u) -
            shiftedHerglotzScrewAtom x t -
            shiftedHerglotzScrewAtom x (-u) +
            shiftedHerglotzScrewAtom x 0 ∂μ := by
          exact (hadd'.trans (by rw [hsub₂'])).symm
      _ = ∫ x : ℝ,
          shiftedScrewFeature x t *
            starRingEnd ℂ (shiftedScrewFeature x u) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          exact shiftedHerglotzScrewAtom_kernel x t u
      _ = shiftedHerglotzKernel ω hzero t u := by
          rfl
  unfold screwKernel shiftedHerglotzScrew
  dsimp only [μ] at hIntegral
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  have hlinear :
      Complex.I * (shiftedXiHerglotzConstant ω hzero : ℂ) * ((t - u : ℝ) : ℂ) -
          Complex.I * (shiftedXiHerglotzConstant ω hzero : ℂ) * (t : ℂ) -
          Complex.I * (shiftedXiHerglotzConstant ω hzero : ℂ) * ((-u : ℝ) : ℂ) +
          0 = 0 := by
    push_cast
    ring
  linear_combination hIntegral + hlinear

theorem screwKernel_shiftedHerglotzScrew_psd
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    KernelPSD (screwKernel (shiftedHerglotzScrew ω hzero)) := by
  rw [screwKernel_shiftedHerglotzScrew]
  exact shiftedHerglotzKernel_psd hzero

theorem shiftedHerglotzScrew_neg
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) (t : ℝ) :
    shiftedHerglotzScrew ω hzero (-t) =
      starRingEnd ℂ (shiftedHerglotzScrew ω hzero t) := by
  simp only [shiftedHerglotzScrew]
  change _ = conj _
  rw [map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_ofReal, ← integral_conj]
  simp_rw [shiftedHerglotzScrewAtom_neg]
  push_cast
  ring

theorem continuous_shiftedHerglotzScrew
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    Continuous (shiftedHerglotzScrew ω hzero) := by
  have hIntegral : Continuous (fun t : ℝ =>
      ∫ x : ℝ, shiftedHerglotzScrewAtom x t
        ∂shiftedXiHerglotzMeasure ω hzero) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    let M : ℝ := |t₀| + 1
    let C : ℝ := 2 * M ^ 2 + 2 * M + 4
    have hM : 0 ≤ M := by dsimp [M]; linarith [abs_nonneg t₀]
    have hboundInt : Integrable (fun x : ℝ => C * (1 / (1 + x ^ 2)))
        (shiftedXiHerglotzMeasure ω hzero) :=
      (integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure hzero).const_mul C
    have ht_near : ∀ᶠ t in 𝓝 t₀, |t| ≤ M := by
      filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
      have hdist : |t - t₀| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq] using ht
      calc
        |t| = |(t - t₀) + t₀| := by ring_nf
        _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
        _ ≤ M := by dsimp [M]; linarith
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => C * (1 / (1 + x ^ 2)))
    · exact Eventually.of_forall fun t =>
        (continuous_shiftedHerglotzScrewAtom t).aestronglyMeasurable
    · filter_upwards [ht_near] with t ht
      filter_upwards with x
      have htupper : t ≤ M := (le_abs_self t).trans ht
      have htlower : -M ≤ t := by
        nlinarith [neg_le_abs t]
      have htsq : t ^ 2 ≤ M ^ 2 := by
        nlinarith [sq_nonneg (M - t), sq_nonneg (M + t)]
      have hcoef : 2 * t ^ 2 + 2 * |t| + 4 ≤ C := by
        dsimp [C]
        nlinarith
      exact (norm_shiftedHerglotzScrewAtom_le_weight x t).trans
        (by
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_right hcoef
              (inv_nonneg.mpr (by positivity : 0 ≤ 1 + x ^ 2)))
    · exact hboundInt
    · filter_upwards with x
      exact (continuous_shiftedHerglotzScrewAtom_time x).continuousAt
  unfold shiftedHerglotzScrew
  exact (((continuous_const.mul continuous_const).mul
    Complex.continuous_ofReal).add hIntegral)

theorem isScrewFunction_shiftedHerglotzScrew
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    IsScrewFunction (shiftedHerglotzScrew ω hzero) := by
  refine ⟨continuous_shiftedHerglotzScrew ω hzero,
    shiftedHerglotzScrew_zero ω hzero, shiftedHerglotzScrew_neg ω hzero, ?_⟩
  exact screwKernel_shiftedHerglotzScrew_psd ω hzero

private theorem integrableOn_id_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ))) (Ioi 0) := by
  let y : ℝ := -a.re
  have hy : 0 < y := by dsimp [y]; linarith
  have hbase : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    norm_num
    ring
  have hscaled : IntegrableOn
      (fun x : ℝ => (y * x) * Real.exp (-(y * x))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => x * Real.exp (-x)) 0 hy).2 (by simpa using hbase)
  have hreal : IntegrableOn
      (fun x : ℝ => x * Real.exp (-y * x)) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    have h := hscaled.const_mul (1 / y)
    apply h.congr
    filter_upwards with x
    field_simp [hy.ne']
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ)))
      (volume.restrict (Ioi 0)) :=
    ((Complex.continuous_ofReal.mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  change Integrable _ (volume.restrict (Ioi 0))
  rw [← integrable_norm_iff hmeas]
  apply hreal.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [abs_of_pos hx]
  dsimp [y]
  congr 2
  ring

private theorem tendsto_id_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ))) atTop (𝓝 0) := by
  let y : ℝ := -a.re
  have hy : 0 < y := by dsimp [y]; linarith
  have hscale : Tendsto (fun x : ℝ => y * x) atTop atTop :=
    tendsto_id.const_mul_atTop hy
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hreal : Tendsto (fun x : ℝ => x * Real.exp (-y * x)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => 1 / y) atTop (𝓝 (1 / y)) :=
      tendsto_const_nhds
    have hmul := hconst.mul hbase
    have hmul' : Tendsto
        (fun x => 1 / y * ((y * x) ^ 1 * Real.exp (-(y * x))))
        atTop (𝓝 0) := by simpa only [Function.comp_apply, mul_zero] using hmul
    apply hmul'.congr'
    filter_upwards with x
    field_simp [hy.ne']
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [abs_of_nonneg hx]
  dsimp [y]
  congr 2
  ring

private theorem integral_id_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) * Complex.exp (a * (x : ℂ))) = 1 / a ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  let F : ℝ → ℂ := fun x =>
    Complex.exp (a * (x : ℂ)) * (a * (x : ℂ) - 1) / a ^ 2
  have hderiv : ∀ x : ℝ, HasDerivAt F
      ((x : ℂ) * Complex.exp (a * (x : ℂ))) x := by
    intro x
    have hlin : HasDerivAt (fun w : ℂ => a * w) a (x : ℂ) :=
      by simpa using (hasDerivAt_id (x : ℂ)).const_mul a
    have h := (hlin.cexp.mul (hlin.sub_const 1)).div_const (a ^ 2)
    apply h.comp_ofReal.congr_deriv
    field_simp [ha0]
    ring
  have hlimexp : Tendsto (fun x : ℝ => Complex.exp (a * (x : ℂ))) atTop (𝓝 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have hmul : Tendsto (fun x : ℝ => a.re * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg ha
    apply hmul.congr'
    filter_upwards with x
    simp [Complex.mul_re]
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hid := tendsto_id_mul_cexp_herglotz ha
    have hdecomp : F = fun x : ℝ =>
        (a / a ^ 2) * ((x : ℂ) * Complex.exp (a * (x : ℂ))) -
          (1 / a ^ 2) * Complex.exp (a * (x : ℂ)) := by
      funext x
      dsimp [F]
      field_simp [ha0]
    rw [hdecomp]
    simpa using (tendsto_const_nhds.mul hid).sub
      (tendsto_const_nhds.mul hlimexp)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hderiv x) (integrableOn_id_mul_cexp_herglotz ha) hlim]
  dsimp [F]
  field_simp [ha0]
  norm_num

private theorem integrableOn_sq_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ))) (Ioi 0) := by
  let y : ℝ := -a.re
  have hy : 0 < y := by dsimp [y]; linarith
  have hbase : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-x)) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := 3) (by norm_num)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    norm_num
    ring
  have hscaled : IntegrableOn
      (fun x : ℝ => (y * x) ^ 2 * Real.exp (-(y * x))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => x ^ 2 * Real.exp (-x)) 0 hy).2 (by simpa using hbase)
  have hreal : IntegrableOn
      (fun x : ℝ => x ^ 2 * Real.exp (-y * x)) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    have h := hscaled.const_mul (1 / y ^ 2)
    apply h.congr
    filter_upwards with x
    field_simp [hy.ne']
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ)))
      (volume.restrict (Ioi 0)) :=
    (((Complex.continuous_ofReal.pow 2).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  change Integrable _ (volume.restrict (Ioi 0))
  rw [← integrable_norm_iff hmeas]
  apply hreal.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [abs_of_pos hx]
  dsimp [y]
  congr 2
  ring

private theorem tendsto_sq_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ))) atTop (𝓝 0) := by
  let y : ℝ := -a.re
  have hy : 0 < y := by dsimp [y]; linarith
  have hscale : Tendsto (fun x : ℝ => y * x) atTop atTop :=
    tendsto_id.const_mul_atTop hy
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale
  have hreal : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-y * x)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => 1 / y ^ 2) atTop (𝓝 (1 / y ^ 2)) :=
      tendsto_const_nhds
    have hmul := hconst.mul hbase
    have hmul' : Tendsto
        (fun x => 1 / y ^ 2 * ((y * x) ^ 2 * Real.exp (-(y * x))))
        atTop (𝓝 0) := by simpa only [Function.comp_apply, mul_zero] using hmul
    apply hmul'.congr'
    filter_upwards with x
    field_simp [hy.ne']
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [abs_of_nonneg hx]
  dsimp [y]
  congr 2
  ring

private theorem integral_sq_mul_cexp_herglotz
    {a : ℂ} (ha : a.re < 0) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ))) =
      -2 / a ^ 3 := by
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  let F : ℝ → ℂ := fun x =>
    Complex.exp (a * (x : ℂ)) *
      (a ^ 2 * (x : ℂ) ^ 2 - 2 * a * (x : ℂ) + 2) / a ^ 3
  have hderiv : ∀ x : ℝ, HasDerivAt F
      ((x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ))) x := by
    intro x
    have hlin : HasDerivAt (fun w : ℂ => a * w) a (x : ℂ) :=
      by simpa using (hasDerivAt_id (x : ℂ)).const_mul a
    have hpoly : HasDerivAt
        (fun w : ℂ => a ^ 2 * w ^ 2 - 2 * a * w + 2)
        (2 * a ^ 2 * (x : ℂ) - 2 * a) (x : ℂ) := by
      have hraw := ((((hasDerivAt_id (x : ℂ)).pow 2).const_mul (a ^ 2)).sub
        ((hasDerivAt_id (x : ℂ)).const_mul (2 * a))).add_const 2
      exact hraw.congr_deriv (by
        simp only [Function.id_def, Nat.cast_ofNat, pow_one, mul_one]
        ring)
    have h := (hlin.cexp.mul hpoly).div_const (a ^ 3)
    apply h.comp_ofReal.congr_deriv
    field_simp [ha0]
    ring
  have hlimexp : Tendsto (fun x : ℝ => Complex.exp (a * (x : ℂ))) atTop (𝓝 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have hmul : Tendsto (fun x : ℝ => a.re * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg ha
    apply hmul.congr'
    filter_upwards with x
    simp [Complex.mul_re]
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hsq := tendsto_sq_mul_cexp_herglotz ha
    have hid := tendsto_id_mul_cexp_herglotz ha
    have hdecomp : F = fun x : ℝ =>
        (a ^ 2 / a ^ 3) * ((x : ℂ) ^ 2 * Complex.exp (a * (x : ℂ))) -
          (2 * a / a ^ 3) * ((x : ℂ) * Complex.exp (a * (x : ℂ))) +
          (2 / a ^ 3) * Complex.exp (a * (x : ℂ)) := by
      funext x
      dsimp [F]
      field_simp [ha0]
    rw [hdecomp]
    simpa using ((tendsto_const_nhds.mul hsq).sub
      (tendsto_const_nhds.mul hid)).add
        (tendsto_const_nhds.mul hlimexp)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hderiv x) (integrableOn_sq_mul_cexp_herglotz ha) hlim]
  dsimp [F]
  norm_num [Complex.exp_zero]
  ring

theorem integrableOn_shiftedHerglotzScrewAtom_exp
    {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    IntegrableOn (fun t : ℝ => shiftedHerglotzScrewAtom x t *
      Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  by_cases hx : x = 0
  · subst x
    have hsq := integrableOn_sq_mul_cexp_herglotz ha
    apply ((hsq.const_mul (-(1 / 2 : ℂ))).congr)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [shiftedHerglotzScrewAtom_zero]
    dsimp [a]
    push_cast
    ring
  · let b : ℂ := Complex.I * (z - (x : ℂ))
    have hb : b.re < 0 := by
      dsimp [b]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.sub_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
      exact neg_lt_zero.mpr hz
    have hA := integrableOn_exp_mul_complex_Ioi ha 0
    have hB := integrableOn_exp_mul_complex_Ioi hb 0
    have hM := integrableOn_id_mul_cexp_herglotz ha
    have hcombo := ((hB.sub hA).const_mul (1 / (x : ℂ) ^ 2)).add
      (hM.const_mul (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))))
    apply hcombo.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [shiftedHerglotzScrewAtom_eq hx]
    dsimp [a, b]
    have hexp : Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) *
          Complex.exp (Complex.I * z * (t : ℂ)) =
        Complex.exp (Complex.I * (z - (x : ℂ)) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    symm
    calc
      _ = (1 / (x : ℂ) ^ 2) *
            (Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) *
                Complex.exp (Complex.I * z * (t : ℂ)) -
              Complex.exp (Complex.I * z * (t : ℂ))) +
          (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
            ((t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) := by ring
      _ = _ := by rw [hexp]

/-- The one-sided Fourier-Laplace transform of one normalized real
Herglotz screw atom. -/
theorem integral_shiftedHerglotzScrewAtom_exp
    (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (∫ t : ℝ in Ioi 0, shiftedHerglotzScrewAtom x t *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      -(Complex.I / z ^ 2) * herglotzKernel x z := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  by_cases hx : x = 0
  · subst x
    calc
      (∫ t : ℝ in Ioi 0, shiftedHerglotzScrewAtom 0 t *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        -(1 / 2 : ℂ) *
          ∫ t : ℝ in Ioi 0,
            (t : ℂ) ^ 2 * Complex.exp (a * (t : ℂ)) := by
          rw [← MeasureTheory.integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change shiftedHerglotzScrewAtom 0 t *
              Complex.exp (Complex.I * z * (t : ℂ)) = _
          simp only [shiftedHerglotzScrewAtom_zero]
          dsimp [a]
          push_cast
          ring
      _ = -(1 / 2 : ℂ) * (-2 / a ^ 3) := by
          rw [integral_sq_mul_cexp_herglotz ha]
      _ = -(Complex.I / z ^ 2) * herglotzKernel 0 z := by
          dsimp [a]
          simp only [herglotzKernel, Complex.ofReal_zero, zero_sub, zero_div,
            sub_zero]
          field_simp [hz0, Complex.I_ne_zero]
          norm_num [Complex.I_sq]
  · let b : ℂ := Complex.I * (z - (x : ℂ))
    have hb : b.re < 0 := by
      dsimp [b]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.sub_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
      exact neg_lt_zero.mpr hz
    have hA := integrableOn_exp_mul_complex_Ioi ha 0
    have hB := integrableOn_exp_mul_complex_Ioi hb 0
    have hM := integrableOn_id_mul_cexp_herglotz ha
    have hpoint : ∀ t : ℝ,
        shiftedHerglotzScrewAtom x t *
            Complex.exp (Complex.I * z * (t : ℂ)) =
          (1 / (x : ℂ) ^ 2) *
              (Complex.exp (b * (t : ℂ)) - Complex.exp (a * (t : ℂ))) +
            (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
              ((t : ℂ) * Complex.exp (a * (t : ℂ))) := by
      intro t
      rw [shiftedHerglotzScrewAtom_eq hx]
      dsimp [a, b]
      have hexp : Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) *
            Complex.exp (Complex.I * z * (t : ℂ)) =
          Complex.exp (Complex.I * (z - (x : ℂ)) * (t : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = (1 / (x : ℂ) ^ 2) *
              (Complex.exp (-Complex.I * ((x * t : ℝ) : ℂ)) *
                  Complex.exp (Complex.I * z * (t : ℂ)) -
                Complex.exp (Complex.I * z * (t : ℂ))) +
            (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
              ((t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) := by ring
        _ = _ := by rw [hexp]
    calc
      (∫ t : ℝ in Ioi 0, shiftedHerglotzScrewAtom x t *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          (1 / (x : ℂ) ^ 2) *
              (Complex.exp (b * (t : ℂ)) - Complex.exp (a * (t : ℂ))) +
            (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
              ((t : ℂ) * Complex.exp (a * (t : ℂ))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact hpoint t
      _ = (∫ t : ℝ in Ioi 0, (1 / (x : ℂ) ^ 2) *
              (Complex.exp (b * (t : ℂ)) - Complex.exp (a * (t : ℂ)))) +
            ∫ t : ℝ in Ioi 0,
              (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
                ((t : ℂ) * Complex.exp (a * (t : ℂ))) := by
          exact integral_add
            ((hB.sub hA).const_mul (1 / (x : ℂ) ^ 2))
            (hM.const_mul (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))))
      _ = (1 / (x : ℂ) ^ 2) *
              ((∫ t : ℝ in Ioi 0, Complex.exp (b * (t : ℂ))) -
                ∫ t : ℝ in Ioi 0, Complex.exp (a * (t : ℂ))) +
            (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
              ∫ t : ℝ in Ioi 0,
                (t : ℂ) * Complex.exp (a * (t : ℂ)) := by
          rw [integral_const_mul, integral_sub hB hA, integral_const_mul]
      _ = (1 / (x : ℂ) ^ 2) *
              ((-1 / b) - (-1 / a)) +
            (Complex.I / ((x : ℂ) * (1 + (x : ℂ) ^ 2))) *
              (1 / a ^ 2) := by
          rw [integral_exp_mul_complex_Ioi hb 0,
            integral_exp_mul_complex_Ioi ha 0,
            integral_id_mul_cexp_herglotz ha]
          simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      _ = -(Complex.I / z ^ 2) * herglotzKernel x z := by
          dsimp [a, b]
          have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
          have hzx : z - (x : ℂ) ≠ 0 := by
            intro h
            have him := congrArg Complex.im h
            simp at him
            linarith
          have hxz : -z + (x : ℂ) ≠ 0 := by
            intro h
            apply hzx
            calc
              z - (x : ℂ) = -(-z + (x : ℂ)) := by ring
              _ = 0 := by rw [h]; simp
          have hxz' : (x : ℂ) - z ≠ 0 := by
            simpa only [neg_sub] using neg_ne_zero.mpr hzx
          have hone : (1 : ℂ) + (x : ℂ) ^ 2 ≠ 0 := by
            rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_add]
            exact Complex.ofReal_ne_zero.mpr (by positivity)
          unfold herglotzKernel
          push_cast
          simp only [mul_pow, Complex.I_sq]
          field_simp [hz0, hxC, hzx, hxz, hone, Complex.I_ne_zero]
          field_simp [hxz']
          rw [Complex.I_sq]
          ring

private theorem integrable_shiftedHerglotzScrewAtom_exp_prod
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun p : ℝ × ℝ =>
      shiftedHerglotzScrewAtom p.2 p.1 *
        Complex.exp (Complex.I * z * (p.1 : ℂ)))
      ((volume.restrict (Ioi 0)).prod (shiftedXiHerglotzMeasure ω hzero)) := by
  let a : ℂ := Complex.I * z
  let A : ℝ → ℝ := fun t =>
    2 * ‖(t : ℂ) ^ 2 * Complex.exp (a * (t : ℂ))‖ +
      2 * ‖(t : ℂ) * Complex.exp (a * (t : ℂ))‖ +
      4 * ‖Complex.exp (a * (t : ℂ))‖
  let B : ℝ → ℝ := fun x => 1 / (1 + x ^ 2)
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hA : Integrable A (volume.restrict (Ioi 0)) := by
    exact (((integrableOn_sq_mul_cexp_herglotz ha).norm.const_mul 2).add
      ((integrableOn_id_mul_cexp_herglotz ha).norm.const_mul 2)).add
        ((integrableOn_exp_mul_complex_Ioi ha 0).norm.const_mul 4)
  have hB : Integrable B (shiftedXiHerglotzMeasure ω hzero) := by
    simpa [B] using integrable_one_div_one_add_sq_shiftedXiHerglotzMeasure hzero
  have hdom : Integrable (fun p : ℝ × ℝ => A p.1 * B p.2)
      ((volume.restrict (Ioi 0)).prod (shiftedXiHerglotzMeasure ω hzero)) :=
    hA.mul_prod hB
  apply hdom.mono'
  · have hcont : Continuous (fun p : ℝ × ℝ =>
        shiftedHerglotzScrewAtom p.2 p.1 *
          Complex.exp (Complex.I * z * (p.1 : ℂ))) := by
      have hrat : Continuous (fun p : ℝ × ℝ =>
          p.2 / (1 + p.2 ^ 2)) :=
        continuous_snd.div₀ (continuous_const.add (continuous_snd.pow 2))
          (fun p => by positivity)
      have hInt : Continuous (fun p : ℝ × ℝ =>
          ∫ s : ℝ in (0 : ℝ)..1,
            ((1 : ℂ) - (s : ℂ)) *
              Complex.exp ((-Complex.I * ((p.2 * p.1 : ℝ) : ℂ)) * (s : ℂ))) := by
        fun_prop
      have hAtom : Continuous (fun p : ℝ × ℝ =>
          shiftedHerglotzScrewAtom p.2 p.1) := by
        have hleft : Continuous (fun p : ℝ × ℝ =>
            -(((p.1 ^ 2 : ℝ) : ℂ)) *
              ∫ s : ℝ in (0 : ℝ)..1,
                ((1 : ℂ) - (s : ℂ)) *
                  Complex.exp ((-Complex.I * ((p.2 * p.1 : ℝ) : ℂ)) *
                    (s : ℂ))) :=
          (Complex.continuous_ofReal.comp (continuous_fst.pow 2)).neg.mul hInt
        have hright : Continuous (fun p : ℝ × ℝ =>
            Complex.I * (p.1 : ℂ) * ((p.2 / (1 + p.2 ^ 2) : ℝ) : ℂ)) :=
          (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
            (Complex.continuous_ofReal.comp hrat)
        unfold shiftedHerglotzScrewAtom
        exact hleft.sub hright
      exact hAtom.mul (Complex.continuous_exp.comp (by fun_prop))
    exact hcont.aestronglyMeasurable
  · filter_upwards with p
    have hatom := norm_shiftedHerglotzScrewAtom_le_weight p.2 p.1
    simp only [norm_mul, Complex.norm_exp]
    have hexp :
        (Complex.I * z * (p.1 : ℂ)).re = -z.im * p.1 := by
      simp [Complex.mul_re]
    rw [hexp]
    have hAeq : A p.1 =
        (2 * p.1 ^ 2 + 2 * |p.1| + 4) * Real.exp (-z.im * p.1) := by
      dsimp [A, a]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, abs_sq]
      rw [sq_abs]
      ring
    rw [hAeq]
    dsimp [B]
    calc
      ‖shiftedHerglotzScrewAtom p.2 p.1‖ * Real.exp (-z.im * p.1) ≤
          ((2 * p.1 ^ 2 + 2 * |p.1| + 4) / (1 + p.2 ^ 2)) *
            Real.exp (-z.im * p.1) :=
        mul_le_mul_of_nonneg_right hatom (Real.exp_pos _).le
      _ = (2 * p.1 ^ 2 + 2 * |p.1| + 4) * Real.exp (-z.im * p.1) *
          (1 / (1 + p.2 ^ 2)) := by ring

/-- The screw reconstructed from the shifted-xi Herglotz measure has the
Suzuki one-sided transform on the whole upper half-plane. -/
theorem integral_shiftedHerglotzScrew_exp_eq_xiNevanlinnaQShifted
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im) :
    (∫ t : ℝ in Ioi 0, shiftedHerglotzScrew ω hzero t *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      -(Complex.I / z ^ 2) * xiNevanlinnaQShifted ω z := by
  let μ := shiftedXiHerglotzMeasure ω hzero
  let A : ℝ := shiftedXiHerglotzConstant ω hzero
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  have hprod := integrable_shiftedHerglotzScrewAtom_exp_prod hzero hz
  have hswap :
      (∫ t : ℝ in Ioi 0,
          ∫ x : ℝ, shiftedHerglotzScrewAtom x t *
            Complex.exp (Complex.I * z * (t : ℂ)) ∂μ) =
        ∫ x : ℝ,
          (∫ t : ℝ in Ioi 0, shiftedHerglotzScrewAtom x t *
            Complex.exp (Complex.I * z * (t : ℂ))) ∂μ := by
    exact integral_integral_swap
        (f := fun t x : ℝ => shiftedHerglotzScrewAtom x t *
          Complex.exp (Complex.I * z * (t : ℂ))) hprod
  have hAtomIntegral :
      (∫ t : ℝ in Ioi 0,
          (∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) *
            Complex.exp (Complex.I * z * (t : ℂ))) =
        -(Complex.I / z ^ 2) *
          ∫ x : ℝ, herglotzKernel x z ∂μ := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
          ∫ x : ℝ, shiftedHerglotzScrewAtom x t *
            Complex.exp (Complex.I * z * (t : ℂ)) ∂μ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact (MeasureTheory.integral_mul_const
            (Complex.exp (Complex.I * z * (t : ℂ)))
            (fun x : ℝ => shiftedHerglotzScrewAtom x t)).symm
      _ = ∫ x : ℝ,
          (∫ t : ℝ in Ioi 0, shiftedHerglotzScrewAtom x t *
            Complex.exp (Complex.I * z * (t : ℂ))) ∂μ := hswap
      _ = ∫ x : ℝ, -(Complex.I / z ^ 2) * herglotzKernel x z ∂μ := by
          exact congrArg (fun F : ℝ → ℂ => ∫ x : ℝ, F x ∂μ)
            (funext fun x => integral_shiftedHerglotzScrewAtom_exp x hz)
      _ = -(Complex.I / z ^ 2) *
          ∫ x : ℝ, herglotzKernel x z ∂μ := by
          rw [integral_const_mul]
  have hlinInt : IntegrableOn (fun t : ℝ =>
      (Complex.I * (A : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    have hm := integrableOn_id_mul_cexp_herglotz ha
    apply (hm.const_mul (Complex.I * (A : ℂ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [a]
    ring
  have hatomInt : IntegrableOn (fun t : ℝ =>
      (∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    have hi := hprod.integral_prod_left
    apply hi.congr
    filter_upwards with t
    exact MeasureTheory.integral_mul_const
      (Complex.exp (Complex.I * z * (t : ℂ)))
      (fun x : ℝ => shiftedHerglotzScrewAtom x t)
  calc
    (∫ t : ℝ in Ioi 0, shiftedHerglotzScrew ω hzero t *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      (∫ t : ℝ in Ioi 0,
          (Complex.I * (A : ℂ) * (t : ℂ)) *
            Complex.exp (Complex.I * z * (t : ℂ))) +
        ∫ t : ℝ in Ioi 0,
          (∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) *
            Complex.exp (Complex.I * z * (t : ℂ)) := by
        rw [← integral_add hlinInt hatomInt]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [shiftedHerglotzScrew, A, μ]
        ring
    _ = (Complex.I * (A : ℂ)) * (1 / a ^ 2) +
        (-(Complex.I / z ^ 2) *
          ∫ x : ℝ, herglotzKernel x z ∂μ) := by
        rw [hAtomIntegral]
        congr 1
        calc
          (∫ t : ℝ in Ioi 0,
              Complex.I * (A : ℂ) * (t : ℂ) *
                Complex.exp (Complex.I * z * (t : ℂ))) =
              (Complex.I * (A : ℂ)) *
                ∫ t : ℝ in Ioi 0,
                  (t : ℂ) * Complex.exp (a * (t : ℂ)) := by
            rw [← MeasureTheory.integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp [a]
            ring
          _ = _ := by rw [integral_id_mul_cexp_herglotz ha]
    _ = -(Complex.I / z ^ 2) *
        ((A : ℂ) + ∫ x : ℝ, herglotzKernel x z ∂μ) := by
          dsimp [a]
          simp only [mul_pow, Complex.I_sq]
          field_simp [hz0, Complex.I_ne_zero]
          ring
    _ = -(Complex.I / z ^ 2) * xiNevanlinnaQShifted ω z := by
          rw [xiNevanlinnaQShifted_eq_herglotzRepresentation hzero hz]

private theorem integrable_mul_cexp_real_frequency
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t : ℝ => f t *
      Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) := by
  refine Integrable.mono'
    (f := fun t : ℝ => f t *
      Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)))
    (g := fun t : ℝ => ‖f t‖) hf.norm ?_ ?_
  · exact (hf.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards with t
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]

/-- Uniqueness of the ordinary Fourier transform for a real `L¹` density,
deduced from Mathlib's uniqueness theorem for characteristic functions of
finite positive measures. -/
theorem ae_eq_zero_of_real_fourier_integral_eq_zero
    {q : ℝ → ℝ} (hq : Integrable q)
    (hfourier : ∀ x : ℝ,
      (∫ t : ℝ, (q t : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) = 0) :
    q =ᵐ[volume] 0 := by
  let μp : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (q t))
  let μn : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (-q t))
  letI : IsFiniteMeasure μp := by
    dsimp [μp]
    exact isFiniteMeasure_withDensity_ofReal hq.2
  letI : IsFiniteMeasure μn := by
    dsimp [μn]
    exact isFiniteMeasure_withDensity_ofReal hq.neg.2
  have hqmeas : AEMeasurable q volume := hq.aestronglyMeasurable.aemeasurable
  have hqnegmeas : AEMeasurable (fun t => -q t) volume := hqmeas.neg
  have hpInt (x : ℝ) : Integrable (fun t : ℝ =>
      ((max (q t) 0 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) := by
    refine Integrable.mono'
      (f := fun t : ℝ => ((max (q t) 0 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)))
      (g := fun t : ℝ => ‖q t‖) hq.norm ?_ ?_
    · exact (((hqmeas.max aemeasurable_const).complex_ofReal.aestronglyMeasurable).mul
          (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards with t
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, Real.exp_zero,
        mul_one, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hnInt (x : ℝ) : Integrable (fun t : ℝ =>
      ((max (-q t) 0 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) := by
    refine Integrable.mono'
      (f := fun t : ℝ => ((max (-q t) 0 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)))
      (g := fun t : ℝ => ‖q t‖) hq.norm ?_ ?_
    · exact (((hqnegmeas.max aemeasurable_const).complex_ofReal.aestronglyMeasurable).mul
          (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards with t
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, Real.exp_zero,
        mul_one]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have hchar : MeasureTheory.charFun μp = MeasureTheory.charFun μn := by
    funext x
    rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply_real]
    have hpDensity := integral_withDensity_eq_integral_toReal_smul₀
      hqmeas.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t : ℝ =>
        Complex.exp (x * t * Complex.I))
    have hnDensity := integral_withDensity_eq_integral_toReal_smul₀
      hqnegmeas.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t : ℝ =>
        Complex.exp (x * t * Complex.I))
    change (∫ t : ℝ, Complex.exp (x * t * Complex.I) ∂μp) =
      ∫ t : ℝ, Complex.exp (x * t * Complex.I) ∂μn
    rw [hpDensity, hnDensity]
    change (∫ t : ℝ, ((max (q t) 0 : ℝ) : ℂ) *
        Complex.exp (x * t * Complex.I)) =
      ∫ t : ℝ, ((max (-q t) 0 : ℝ) : ℂ) *
        Complex.exp (x * t * Complex.I)
    have hdiff := integral_sub (hpInt x) (hnInt x)
    have hzero := hfourier x
    have hpoint : (fun t : ℝ =>
        ((max (q t) 0 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) -
          ((max (-q t) 0 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
        (fun t : ℝ => (q t : ℂ) *
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) := by
      funext t
      rw [← sub_mul]
      have hmax : max (q t) 0 - max (-q t) 0 = q t :=
        max_zero_sub_max_neg_zero_eq_self (q t)
      rw [← Complex.ofReal_sub, hmax]
    have hsubzero :
        (∫ t : ℝ, ((max (q t) 0 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) -
          ∫ t : ℝ, ((max (-q t) 0 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) = 0 := by
      calc
        _ = ∫ t : ℝ,
            ((max (q t) 0 : ℝ) : ℂ) *
                Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) -
              ((max (-q t) 0 : ℝ) : ℂ) *
                Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) :=
          hdiff.symm
        _ = ∫ t : ℝ, (q t : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) := by rw [hpoint]
        _ = 0 := hzero
    have hright := sub_eq_zero.mp hsubzero
    convert hright using 1 <;>
      apply MeasureTheory.integral_congr_ae <;>
      filter_upwards with t <;>
      congr 1 <;> ring
  have hμ : μp = μn := Measure.ext_of_charFun hchar
  have hdensity : (fun t : ℝ => ENNReal.ofReal (q t)) =ᵐ[volume]
      (fun t : ℝ => ENNReal.ofReal (-q t)) :=
    (withDensity_eq_iff_of_sigmaFinite hqmeas.ennreal_ofReal
      hqnegmeas.ennreal_ofReal).mp hμ
  filter_upwards [hdensity] with t ht
  by_cases hqt : 0 ≤ q t
  · have hnonpos : -q t ≤ 0 := neg_nonpos.mpr hqt
    have hright : ENNReal.ofReal (-q t) = 0 := ENNReal.ofReal_eq_zero.mpr hnonpos
    rw [hright] at ht
    have hleft : q t ≤ 0 := ENNReal.ofReal_eq_zero.mp ht
    exact le_antisymm hleft hqt
  · have hneg : 0 < -q t := neg_pos.mpr (lt_of_not_ge hqt)
    have hleft : ENNReal.ofReal (q t) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hqt)
    rw [hleft] at ht
    have : -q t ≤ 0 := ENNReal.ofReal_eq_zero.mp ht.symm
    linarith

/-- Ordinary Fourier uniqueness for a complex `L¹` density.  The proof
reduces real and imaginary parts to the preceding positive-measure result. -/
theorem ae_eq_zero_of_complex_fourier_integral_eq_zero
    {f : ℝ → ℂ} (hf : Integrable f)
    (hfourier : ∀ x : ℝ,
      (∫ t : ℝ, f t *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) = 0) :
    f =ᵐ[volume] 0 := by
  have hreInt : Integrable (fun t : ℝ => (f t).re) := hf.re
  have himInt : Integrable (fun t : ℝ => (f t).im) := hf.im
  have hreFourier : ∀ x : ℝ,
      (∫ t : ℝ, (((f t).re : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) = 0 := by
    intro x
    have hrex := integrable_mul_cexp_real_frequency hreInt.ofReal x
    have hfx := integrable_mul_cexp_real_frequency hf x
    have hfn := integrable_mul_cexp_real_frequency hf (-x)
    have hfnConj : Integrable (fun t : ℝ => starRingEnd ℂ
        (f t * Complex.exp (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)))) :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hfn
    have hEq :
        (2 : ℂ) * (∫ t : ℝ, (((f t).re : ℝ) : ℂ) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
          (∫ t : ℝ, f t *
              Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) +
            starRingEnd ℂ (∫ t : ℝ, f t *
              Complex.exp (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ))) := by
      rw [← MeasureTheory.integral_const_mul, ← integral_conj,
        ← integral_add hfx hfnConj]
      apply integral_congr_ae
      filter_upwards with t
      change (2 : ℂ) * (((f t).re : ℂ) *
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
        f t * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) +
          conj (f t * Complex.exp
            (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)))
      rw [map_mul, ← Complex.exp_conj]
      have he : conj (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)) =
          Complex.I * (x : ℂ) * (t : ℂ) := by
        simp
      rw [he]
      apply Complex.ext <;> simp <;> ring
    rw [hfourier x, hfourier (-x), map_zero, add_zero] at hEq
    exact (mul_eq_zero.mp hEq).resolve_left (by norm_num)
  have himFourier : ∀ x : ℝ,
      (∫ t : ℝ, (((f t).im : ℝ) : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) = 0 := by
    intro x
    have himx := integrable_mul_cexp_real_frequency himInt.ofReal x
    have hfx := integrable_mul_cexp_real_frequency hf x
    have hfn := integrable_mul_cexp_real_frequency hf (-x)
    have hfnConj : Integrable (fun t : ℝ => starRingEnd ℂ
        (f t * Complex.exp (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)))) :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hfn
    have hEq :
        ((2 : ℂ) * Complex.I) *
            (∫ t : ℝ, (((f t).im : ℝ) : ℂ) *
              Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
          (∫ t : ℝ, f t *
              Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) -
            starRingEnd ℂ (∫ t : ℝ, f t *
              Complex.exp (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ))) := by
      rw [← MeasureTheory.integral_const_mul, ← integral_conj,
        ← integral_sub hfx hfnConj]
      apply integral_congr_ae
      filter_upwards with t
      change ((2 : ℂ) * Complex.I) * (((f t).im : ℂ) *
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
        f t * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) -
          conj (f t * Complex.exp
            (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)))
      rw [map_mul, ← Complex.exp_conj]
      have he : conj (Complex.I * ((-x : ℝ) : ℂ) * (t : ℂ)) =
          Complex.I * (x : ℂ) * (t : ℂ) := by
        simp
      rw [he]
      apply Complex.ext <;> simp <;> ring
    rw [hfourier x, hfourier (-x), map_zero, sub_zero] at hEq
    exact (mul_eq_zero.mp hEq).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hreZero := ae_eq_zero_of_real_fourier_integral_eq_zero hreInt hreFourier
  have himZero := ae_eq_zero_of_real_fourier_integral_eq_zero himInt himFourier
  filter_upwards [hreZero, himZero] with t hrt hit
  apply Complex.ext
  · simpa using hrt
  · simpa using hit

/-- Specialized uniqueness for one-sided Fourier-Laplace transforms of
continuous functions.  Fixing one positive damping height turns the
one-sided transforms into ordinary Fourier transforms of zero-extended
`L¹` functions. -/
theorem continuous_oneSidedFourier_unique
    {f g : ℝ → ℂ} (hfcont : Continuous f) (hgcont : Continuous g)
    {y : ℝ} (hy : 0 < y)
    (hfint : IntegrableOn (fun t : ℝ => f t *
      Complex.exp (-(y : ℂ) * (t : ℂ))) (Ioi 0))
    (hgint : IntegrableOn (fun t : ℝ => g t *
      Complex.exp (-(y : ℂ) * (t : ℂ))) (Ioi 0))
    (htransform : ∀ x : ℝ,
      (∫ t : ℝ in Ioi 0, f t *
        Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) =
      ∫ t : ℝ in Ioi 0, g t *
        Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) :
    EqOn f g (Ioi 0) := by
  let H : ℝ → ℂ := fun t =>
    (Ioi (0 : ℝ)).indicator (fun t =>
      (f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ))) t
  have hweighted : IntegrableOn (fun t : ℝ =>
      (f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ))) (Ioi 0) := by
    apply (hfint.sub hgint).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Pi.sub_apply]
    ring
  have hint : Integrable H := by
    dsimp only [H]
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact hweighted
  have hfourier : ∀ x : ℝ,
      (∫ t : ℝ, H t *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) = 0 := by
    intro x
    have hmulFreq {q : ℝ → ℂ}
        (hq : IntegrableOn q (Ioi 0)) :
        IntegrableOn (fun t : ℝ => q t *
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) (Ioi 0) := by
      refine Integrable.mono' hq.norm ?_ ?_
      · exact hq.aestronglyMeasurable.mul
          (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards with t
        simp [Complex.norm_exp, Complex.mul_re]
    have hexpShift (t : ℝ) : Complex.exp
        (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ)) =
      Complex.exp (-(y : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) := by
      have harg :
          Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ) =
            -(y : ℂ) * (t : ℂ) + Complex.I * (x : ℂ) * (t : ℂ) := by
        calc
          _ = Complex.I * (x : ℂ) * (t : ℂ) +
              (Complex.I * Complex.I) * ((y : ℂ) * (t : ℂ)) := by ring
          _ = Complex.I * (x : ℂ) * (t : ℂ) -
              (y : ℂ) * (t : ℂ) := by rw [Complex.I_mul_I]; ring
          _ = _ := by ring
      rw [harg, Complex.exp_add]
    dsimp only [H]
    have hind : (fun t : ℝ =>
        (Ioi (0 : ℝ)).indicator (fun t =>
          (f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ))) t *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
        (fun t => ((Ioi (0 : ℝ)).indicator (fun t =>
          ((f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ))) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)))) t) := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [Set.indicator, ht]
    rw [hind, integral_indicator measurableSet_Ioi]
    have hfi : IntegrableOn (fun t : ℝ => f t *
        Complex.exp
          (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) (Ioi 0) := by
      apply (hmulFreq hfint).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hexpShift]
      ring
    have hgi : IntegrableOn (fun t : ℝ => g t *
        Complex.exp
          (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) (Ioi 0) := by
      apply (hmulFreq hgint).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hexpShift]
      ring
    calc
      (∫ t : ℝ in Ioi 0,
          ((f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ))) *
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) =
        (∫ t : ℝ in Ioi 0, f t *
            Complex.exp
              (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) -
          ∫ t : ℝ in Ioi 0, g t *
            Complex.exp
              (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ)) := by
          rw [← integral_sub hfi hgi]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change (f t - g t) * Complex.exp (-(y : ℂ) * (t : ℂ)) *
              Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) =
            f t * Complex.exp
                (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ)) -
              g t * Complex.exp
                (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))
          rw [hexpShift]
          ring
      _ = 0 := sub_eq_zero.mpr (htransform x)
  have hzero := ae_eq_zero_of_complex_fourier_integral_eq_zero hint hfourier
  have hfgAE : f =ᵐ[volume.restrict (Ioi 0)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae hzero] with t ht hzt
    dsimp [H] at hzt
    rw [Set.indicator_of_mem ht] at hzt
    have hexp : Complex.exp (-(y : ℂ) * (t : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzt).resolve_right hexp)
  exact volume.eqOn_open_of_ae_eq hfgAE isOpen_Ioi
    hfcont.continuousOn hgcont.continuousOn

theorem integrableOn_shiftedHerglotzScrew_exp
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im) :
    IntegrableOn (fun t : ℝ => shiftedHerglotzScrew ω hzero t *
      Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  let μ := shiftedXiHerglotzMeasure ω hzero
  let A : ℝ := shiftedXiHerglotzConstant ω hzero
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hprod := integrable_shiftedHerglotzScrewAtom_exp_prod hzero hz
  have hatom : IntegrableOn (fun t : ℝ =>
      (∫ x : ℝ, shiftedHerglotzScrewAtom x t ∂μ) *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) :=
    by
      have hi := hprod.integral_prod_left
      apply hi.congr
      filter_upwards with t
      exact MeasureTheory.integral_mul_const
        (Complex.exp (Complex.I * z * (t : ℂ)))
        (fun x : ℝ => shiftedHerglotzScrewAtom x t)
  have hlin : IntegrableOn (fun t : ℝ =>
      (Complex.I * (A : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    have hm := integrableOn_id_mul_cexp_herglotz ha
    apply (hm.const_mul (Complex.I * (A : ℂ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [a]
    ring
  apply (hlin.add hatom).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.add_apply, shiftedHerglotzScrew, A, μ]
  ring

/-- The Herglotz screw reconstructed from shifted xi is exactly the
negative of Suzuki's shifted Psi. -/
theorem shiftedHerglotzScrew_eq_neg_suzukiPsiShifted
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) (t : ℝ) :
    shiftedHerglotzScrew ω hzero t = -(suzukiPsiShifted ω t : ℂ) := by
  let y : ℝ := |1 / 2 - ω| + 1
  have hy : 0 < y := by dsimp [y]; positivity
  have hstrip : 1 / 2 - ω < y := by
    dsimp [y]
    linarith [le_abs_self (1 / 2 - ω)]
  have hfint : IntegrableOn (fun t : ℝ => shiftedHerglotzScrew ω hzero t *
      Complex.exp (-(y : ℂ) * (t : ℂ))) (Ioi 0) := by
    have h := integrableOn_shiftedHerglotzScrew_exp hzero
      (z := Complex.I * (y : ℂ)) (by simpa using hy)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    congr 1
    congr 1
    calc
      Complex.I * (Complex.I * (y : ℂ)) * (t : ℂ) =
          (Complex.I * Complex.I) * ((y : ℂ) * (t : ℂ)) := by ring
      _ = -((y : ℂ) * (t : ℂ)) := by rw [Complex.I_mul_I]; ring
      _ = -(y : ℂ) * (t : ℂ) := by ring
  have hpsi : laplaceConvergesAt (suzukiPsiShifted ω) y :=
    laplaceConvergesAt_suzukiPsiShifted_initial ω hy hstrip
  have hgint : IntegrableOn (fun t : ℝ => -(suzukiPsiShifted ω t : ℂ) *
      Complex.exp (-(y : ℂ) * (t : ℂ))) (Ioi 0) := by
    apply hpsi.neg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Pi.neg_apply]
    ring
  have htransform : ∀ x : ℝ,
      (∫ t : ℝ in Ioi 0, shiftedHerglotzScrew ω hzero t *
        Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) =
      ∫ t : ℝ in Ioi 0, -(suzukiPsiShifted ω t : ℂ) *
        Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ)) := by
    intro x
    let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    have hz : 0 < z.im := by simpa [z] using hy
    have hzs : 1 / 2 - ω < z.im := by simpa [z] using hstrip
    rw [integral_shiftedHerglotzScrew_exp_eq_xiNevanlinnaQShifted hzero hz]
    have hpsiTransform := integral_suzukiPsiShifted_exp_eq_xiNevanlinnaQShifted
      (ω := ω) (z := z) hz hzs
    have hneg :
      (∫ t : ℝ in Ioi 0, -(suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) * (t : ℂ))) =
        -(∫ t : ℝ in Ioi 0, (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) := by
            rw [← integral_neg]
            exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
              dsimp [z]
              ring)
    calc
      -(Complex.I / z ^ 2) * xiNevanlinnaQShifted ω z =
          -((Complex.I / z ^ 2) * xiNevanlinnaQShifted ω z) := by ring
      _ = -(∫ t : ℝ in Ioi 0, (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) := by rw [hpsiTransform]
      _ = (∫ t : ℝ in Ioi 0, -(suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * ((x : ℂ) + Complex.I * (y : ℂ)) *
            (t : ℂ))) := hneg.symm

  have hpos : EqOn (shiftedHerglotzScrew ω hzero)
      (fun t : ℝ => -(suzukiPsiShifted ω t : ℂ)) (Ioi 0) :=
    continuous_oneSidedFourier_unique
      (continuous_shiftedHerglotzScrew ω hzero)
      ((Complex.continuous_ofReal.comp (continuous_suzukiPsiShifted ω)).neg)
      hy hfint hgint htransform
  by_cases ht : 0 < t
  · exact hpos ht
  · by_cases ht0 : t = 0
    · subst t
      simp
    · have htn : 0 < -t := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt ht) ht0)
      have hv := hpos htn
      have hsymm := shiftedHerglotzScrew_neg ω hzero (-t)
      rw [neg_neg] at hsymm
      calc
        shiftedHerglotzScrew ω hzero t =
            starRingEnd ℂ (shiftedHerglotzScrew ω hzero (-t)) := hsymm
        _ = starRingEnd ℂ (-(suzukiPsiShifted ω (-t) : ℂ)) := by rw [hv]
        _ = -(suzukiPsiShifted ω t : ℂ) := by simp

/-- The shifted Nevanlinna condition implies global pointwise
nonnegativity of Suzuki's shifted Psi. -/
theorem xiShiftedNevanlinna_implies_shiftedPsi_nonnegative
    (ω : ℝ) (hN : XiShiftedNevanlinna ω) :
    ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t := by
  have hzero : XiZeroFreeRightOf ω :=
    (xiZeroFreeRightOf_iff_xiShiftedNevanlinna ω).mpr hN
  intro t
  have hPSD := screwKernel_shiftedHerglotzScrew_psd ω hzero
  have hdiag : 0 ≤
      (screwKernel (shiftedHerglotzScrew ω hzero) t t).re := by
    have h := hPSD 1 (fun _ => t) (fun _ => 1)
    simpa using h
  simp only [screwKernel] at hdiag
  rw [shiftedHerglotzScrew_eq_neg_suzukiPsiShifted ω hzero (t - t),
    shiftedHerglotzScrew_eq_neg_suzukiPsiShifted ω hzero t,
    shiftedHerglotzScrew_eq_neg_suzukiPsiShifted ω hzero (-t),
    shiftedHerglotzScrew_eq_neg_suzukiPsiShifted ω hzero 0] at hdiag
  simp at hdiag
  linarith

/-- The project-facing shifted Nevanlinna-to-Psi bridge, reconstructed from
the explicit positive Herglotz measure rather than assumed from the general
Krein--Langer correspondence. -/
theorem shiftedNevanlinnaToPsiNonnegative :
    ShiftedNevanlinnaToPsiNonnegative :=
  xiShiftedNevanlinna_implies_shiftedPsi_nonnegative

theorem xiZeroFreeRightOf_implies_shiftedEventuallyNonnegative
    (ω : ℝ) :
    XiZeroFreeRightOf ω → SuzukiPsiShiftedEventuallyNonnegative ω :=
  xiZeroFreeRightOf_implies_shiftedEventuallyNonnegative_of_bridge
    shiftedNevanlinnaToPsiNonnegative ω

theorem xiZeroFreeRightOf_iff_shiftedEventuallyNonnegative
    (ω : ℝ) :
    XiZeroFreeRightOf ω ↔ SuzukiPsiShiftedEventuallyNonnegative ω :=
  xiZeroFreeRightOf_iff_shiftedEventuallyNonnegative_of_bridge
    shiftedNevanlinnaToPsiNonnegative ω

theorem suzukiShiftedEventualCriterion : SuzukiShiftedEventualCriterion :=
  suzukiShiftedEventualCriterion_of_nevanlinna_bridge
    shiftedNevanlinnaToPsiNonnegative

theorem suzukiPsiShifted_half_nonnegative :
    ∀ t : ℝ, 0 ≤ suzukiPsiShifted (1 / 2) t :=
  xiShiftedNevanlinna_implies_shiftedPsi_nonnegative
    (1 / 2) xiShiftedNevanlinna_half

theorem suzukiPsiShifted_nonnegative_of_half_le
    {ω : ℝ} (hω : 1 / 2 ≤ ω) :
    ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t := by
  have hη : 0 ≤ ω - 1 / 2 := sub_nonneg.mpr hω
  have h := suzukiPsiShifted_nonneg_of_nonneg_add hη
    suzukiPsiShifted_half_nonnegative
  convert h using 1 <;> ring

theorem suzukiShiftedPositivitySet_eq_zeroFreeParameters :
    SuzukiShiftedPositivitySet = {ω : ℝ | XiZeroFreeRightOf ω} := by
  ext ω
  constructor
  · intro hω
    apply xiZeroFreeRightOf_of_shifted_eventually_nonnegative ω
    exact ⟨0, fun t _ => hω t⟩
  · intro hω
    exact xiShiftedNevanlinna_implies_shiftedPsi_nonnegative ω
      ((xiZeroFreeRightOf_iff_xiShiftedNevanlinna ω).mp hω)

theorem suzukiShiftedEventualPositivitySet_eq_zeroFreeParameters :
    SuzukiShiftedEventualPositivitySet = {ω : ℝ | XiZeroFreeRightOf ω} := by
  ext ω
  exact (xiZeroFreeRightOf_iff_shiftedEventuallyNonnegative ω).symm

theorem suzukiShiftedPositivitySet_eq_eventualPositivitySet :
    SuzukiShiftedPositivitySet = SuzukiShiftedEventualPositivitySet := by
  rw [suzukiShiftedPositivitySet_eq_zeroFreeParameters,
    suzukiShiftedEventualPositivitySet_eq_zeroFreeParameters]

/-- On a functional-equation reflection pair, the project genus-one
corrections cancel.  The remaining difference from the standard Herglotz
representation is an explicitly real constant. -/
theorem shiftedSpectralReflectionPair_hRepresentation
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    {z : ℂ} (hz : 0 < z.im) (a : XiZeroOccurrence) :
    xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
        xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
          (xiOccurrenceOneSubEquiv a) =
      (∫ x : ℝ, herglotzKernel x z ∂shiftedXiPoleMeasure ω hzero a) +
      (∫ x : ℝ, herglotzKernel x z
        ∂shiftedXiPoleMeasure ω hzero (xiOccurrenceOneSubEquiv a)) +
      ((shiftedXiPoleRealCorrection ω hzero a +
        shiftedXiPoleRealCorrection ω hzero
          (xiOccurrenceOneSubEquiv a) : ℝ) : ℂ) := by
  have ha := integral_herglotzKernel_shiftedXiPole hzero a hz
  have har := integral_herglotzKernel_shiftedXiPole hzero
    (xiOccurrenceOneSubEquiv a) hz
  have hpair :
      xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
          xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
            (xiOccurrenceOneSubEquiv a) =
        1 / (shiftedSpectralPole ω a - z) +
          1 / (shiftedSpectralPole ω (xiOccurrenceOneSubEquiv a) - z) := by
    simp only [shiftedSpectralPole, xiSpectralCorrectedTerm,
      xiSpectralParameterShifted,
      xiSpectralParameter_oneSubOccurrence, one_div, inv_neg]
    ring
  rw [hpair]
  rw [ha, har]
  push_cast
  ring

@[simp] theorem shiftedSpectralReflectionPair_realCorrection_im
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω)
    (a : XiZeroOccurrence) :
    (((shiftedXiPoleRealCorrection ω hzero a +
      shiftedXiPoleRealCorrection ω hzero
        (xiOccurrenceOneSubEquiv a) : ℝ) : ℂ)).im = 0 := by
  simp

end RHGarden
