import RHGarden.SuzukiShifted
import Zeta23.WeilEF.Main
import Zeta23.XiPrime.ExplicitFormula.FullLine
import Zeta23.GammaFacts.Mu
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ZetaValues

noncomputable section

open Complex ContinuousLinearMap Filter Function MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution FourierTransform Pointwise Topology

namespace RHGarden

/-! ## The triangular Weil test and its smooth approximants -/

/-- Suzuki's triangular (tent) test function. -/
def suzukiTriangleTest (t u : ℝ) : ℝ :=
  max (t - |u|) 0

@[simp] theorem suzukiTriangleTest_zero {t : ℝ} (ht : 0 ≤ t) :
    suzukiTriangleTest t 0 = t := by
  simp [suzukiTriangleTest, ht]

@[simp] theorem suzukiTriangleTest_neg (t u : ℝ) :
    suzukiTriangleTest t (-u) = suzukiTriangleTest t u := by
  simp [suzukiTriangleTest]

theorem suzukiTriangleTest_nonneg (t u : ℝ) :
    0 ≤ suzukiTriangleTest t u := by
  simp [suzukiTriangleTest]

theorem suzukiTriangleTest_eq_zero_of_le_abs {t u : ℝ} (h : t ≤ |u|) :
    suzukiTriangleTest t u = 0 := by
  simp [suzukiTriangleTest, h]

theorem support_suzukiTriangleTest_subset {t : ℝ} (ht : 0 ≤ t) :
    Function.support (suzukiTriangleTest t) ⊆ Set.Icc (-t) t := by
  intro u hu
  simp only [Function.mem_support, ne_eq] at hu
  have hlt : |u| < t := by
    by_contra hnot
    exact hu (suzukiTriangleTest_eq_zero_of_le_abs (le_of_not_gt hnot))
  exact ⟨by linarith [neg_le_of_abs_le hlt.le], le_of_abs_le hlt.le⟩

theorem hasCompactSupport_suzukiTriangleTest {t : ℝ} (ht : 0 ≤ t) :
    HasCompactSupport (suzukiTriangleTest t) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-t) t))
  intro u hu
  by_contra hne
  exact hu (support_suzukiTriangleTest_subset ht hne)

theorem lipschitzWith_suzukiTriangleTest (t : ℝ) :
    LipschitzWith 1 (suzukiTriangleTest t) := by
  apply LipschitzWith.mk_one
  intro u v
  rw [Real.dist_eq, Real.dist_eq]
  unfold suzukiTriangleTest
  calc
    |max (t - |u|) 0 - max (t - |v|) 0|
        ≤ |(t - |u|) - (t - |v|)| := by
          simpa using abs_max_sub_max_le_abs (t - |u|) (t - |v|) 0
    _ = abs (|v| - |u|) := by congr 1 <;> ring
    _ ≤ |v - u| := abs_abs_sub_abs_le_abs_sub v u
    _ = |u - v| := abs_sub_comm v u

theorem continuous_suzukiTriangleTest (t : ℝ) :
    Continuous (suzukiTriangleTest t) :=
  (lipschitzWith_suzukiTriangleTest t).continuous

/-- A standard normalized mollifier with outer radius `1/(n+1)`. -/
def suzukiTriangleMollifier (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * (n + 1 : ℝ)), 1 / (n + 1 : ℝ), by positivity, by
    have hn : (0 : ℝ) < n + 1 := by positivity
    exact one_div_lt_one_div_of_lt hn (by nlinarith)⟩

@[simp] theorem suzukiTriangleMollifier_rOut (n : ℕ) :
    (suzukiTriangleMollifier n).rOut = 1 / (n + 1 : ℝ) := rfl

theorem tendsto_suzukiTriangleMollifier_rOut :
    Tendsto (fun n : ℕ ↦ (suzukiTriangleMollifier n).rOut) atTop (nhds 0) := by
  simpa [suzukiTriangleMollifier] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Smooth compactly-supported mollifications of the triangular test. -/
def suzukiTriangleSmooth (t : ℝ) (n : ℕ) : ℝ → ℝ :=
  (suzukiTriangleMollifier n).normed volume
    ⋆[lsmul ℝ ℝ, volume] suzukiTriangleTest t

theorem contDiff_suzukiTriangleSmooth (t : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (suzukiTriangleSmooth t n) := by
  exact (suzukiTriangleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (suzukiTriangleMollifier n).contDiff_normed
    (continuous_suzukiTriangleTest t).locallyIntegrable

theorem hasCompactSupport_suzukiTriangleSmooth {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasCompactSupport (suzukiTriangleSmooth t n) := by
  exact (suzukiTriangleMollifier n).hasCompactSupport_normed.convolution
    (lsmul ℝ ℝ) (hasCompactSupport_suzukiTriangleTest ht)

theorem support_suzukiTriangleSmooth_subset {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Function.support (suzukiTriangleSmooth t n) ⊆ Set.Icc (-(t + 1)) (t + 1) := by
  intro u hu
  have husum : u ∈
      Function.support ((suzukiTriangleMollifier n).normed volume) +
        Function.support (suzukiTriangleTest t) := by
    exact support_convolution_subset (lsmul ℝ ℝ) hu
  rcases husum with ⟨x, hx, y, hy, rfl⟩
  have hxball : x ∈ Metric.ball (0 : ℝ) (suzukiTriangleMollifier n).rOut := by
    simpa only [(suzukiTriangleMollifier n).support_normed_eq] using hx
  have hxabs : |x| < (suzukiTriangleMollifier n).rOut := by
    simpa [Metric.mem_ball, Real.dist_eq] using hxball
  have hr : (suzukiTriangleMollifier n).rOut ≤ 1 := by
    rw [suzukiTriangleMollifier_rOut]
    calc
      1 / (n + 1 : ℝ) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num)
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ = 1 := by norm_num
  have hyIcc := support_suzukiTriangleTest_subset ht hy
  have hxle : |x| ≤ 1 := hxabs.le.trans hr
  have hxlower : -1 ≤ x := neg_le_of_abs_le hxle
  have hxupper : x ≤ 1 := le_of_abs_le hxle
  constructor
  · linarith [hyIcc.1]
  · linarith [hyIcc.2]

theorem tendsto_suzukiTriangleSmooth (t u : ℝ) :
    Tendsto (fun n : ℕ ↦ suzukiTriangleSmooth t n u) atTop
      (nhds (suzukiTriangleTest t u)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    tendsto_suzukiTriangleMollifier_rOut (continuous_suzukiTriangleTest t) u

/-- A global quantitative form of convergence: the mollification error is
at most the outer radius. -/
theorem dist_suzukiTriangleSmooth_le_rOut (t : ℝ) (n : ℕ) (u : ℝ) :
    dist (suzukiTriangleSmooth t n u) (suzukiTriangleTest t u) ≤
      (suzukiTriangleMollifier n).rOut := by
  apply (suzukiTriangleMollifier n).dist_normed_convolution_le
    (continuous_suzukiTriangleTest t).aestronglyMeasurable
  intro x hx
  have hx' : dist x u < 1 / (n + 1 : ℝ) := by
    simpa [mem_ball, suzukiTriangleMollifier] using hx
  exact (lipschitzWith_suzukiTriangleTest t).dist_le_mul_of_le
    (by simpa [one_div] using hx'.le)

theorem abs_suzukiTriangleSmooth_sub_test_le (t : ℝ) (n : ℕ) (u : ℝ) :
    |suzukiTriangleSmooth t n u - suzukiTriangleTest t u| ≤
      1 / (n + 1 : ℝ) := by
  simpa [Real.dist_eq] using dist_suzukiTriangleSmooth_le_rOut t n u

/-- Normalized convolution preserves the tent's unit Lipschitz constant. -/
theorem lipschitzWith_suzukiTriangleSmooth (t : ℝ) (n : ℕ) :
    LipschitzWith 1 (suzukiTriangleSmooth t n) := by
  apply LipschitzWith.mk_one
  intro u v
  let φ : ℝ → ℝ := (suzukiTriangleMollifier n).normed volume
  let h : ℝ → ℝ := suzukiTriangleTest t
  have hφi : Integrable φ := (suzukiTriangleMollifier n).integrable_normed
  have hconv : ConvolutionExists φ h (lsmul ℝ ℝ) volume := by
    exact HasCompactSupport.convolutionExists_left
      (lsmul ℝ ℝ)
      (suzukiTriangleMollifier n).hasCompactSupport_normed
      (suzukiTriangleMollifier n).continuous_normed
      (continuous_suzukiTriangleTest t).locallyIntegrable
  have hu : Integrable (fun x ↦ φ x * h (u - x)) := by
    simpa [lsmul_apply] using (hconv u).integrable
  have hv : Integrable (fun x ↦ φ x * h (v - x)) := by
    simpa [lsmul_apply] using (hconv v).integrable
  rw [Real.dist_eq, suzukiTriangleSmooth, convolution_def, convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  rw [← integral_sub hu hv]
  have hbound : ∀ x : ℝ,
      |φ x * h (u - x) - φ x * h (v - x)| ≤ |φ x| * |u - v| := by
    intro x
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [h, Real.dist_eq] using
        (lipschitzWith_suzukiTriangleTest t).dist_le_mul (u - x) (v - x))
      (abs_nonneg _)
  have hiBound : Integrable (fun x ↦ |φ x| * |u - v|) := hφi.norm.mul_const _
  have hnorm :
      |∫ x, φ x * h (u - x) - φ x * h (v - x)| ≤
        ∫ x, |φ x| * |u - v| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le
        (f := fun x ↦ φ x * h (u - x) - φ x * h (v - x))
        hiBound (Eventually.of_forall hbound))
  calc
    |∫ x, φ x * h (u - x) - φ x * h (v - x)|
        ≤ ∫ x, |φ x| * |u - v| := hnorm
    _ = (∫ x, |φ x|) * |u - v| := integral_mul_const _ _
    _ = |u - v| := by
      have hnonneg : ∀ x, 0 ≤ φ x := (suzukiTriangleMollifier n).nonneg_normed
      simp_rw [abs_of_nonneg (hnonneg _)]
      rw [(suzukiTriangleMollifier n).integral_normed]
      simp

theorem suzukiTriangleSmooth_sub_zero_le (t : ℝ) (n : ℕ) (u : ℝ) :
    |suzukiTriangleSmooth t n u - suzukiTriangleSmooth t n 0| ≤ |u| := by
  simpa [Real.dist_eq] using
    (lipschitzWith_suzukiTriangleSmooth t n).dist_le_mul u 0

/-- The complex-valued version used by Zeta23's explicit formula. -/
def suzukiTriangleSmoothC (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  (suzukiTriangleSmooth t n u : ℂ)

theorem contDiff_suzukiTriangleSmoothC (t : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (suzukiTriangleSmoothC t n) := by
  have hreal : ContDiff ℝ 2 (suzukiTriangleSmooth t n) := by
    exact (suzukiTriangleMollifier n).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (suzukiTriangleMollifier n).contDiff_normed
      (continuous_suzukiTriangleTest t).locallyIntegrable
  change ContDiff ℝ 2 (fun x ↦ (suzukiTriangleSmooth t n x : ℂ))
  exact Complex.ofRealCLM.contDiff.comp hreal

theorem hasCompactSupport_suzukiTriangleSmoothC {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasCompactSupport (suzukiTriangleSmoothC t n) :=
  (hasCompactSupport_suzukiTriangleSmooth ht n).comp_left Complex.ofReal_zero

theorem tendsto_suzukiTriangleSmoothC (t u : ℝ) :
    Tendsto (fun n : ℕ ↦ suzukiTriangleSmoothC t n u) atTop
      (nhds (suzukiTriangleTest t u : ℂ)) := by
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_suzukiTriangleSmooth t u)

theorem tendsto_suzukiTriangleSmoothC_zero {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ suzukiTriangleSmoothC t n 0) atTop (nhds (t : ℂ)) := by
  simpa [suzukiTriangleTest_zero ht] using tendsto_suzukiTriangleSmoothC t 0

theorem norm_suzukiTriangleSmoothC_sub_zero_le (t : ℝ) (n : ℕ) (u : ℝ) :
    ‖suzukiTriangleSmoothC t n u - suzukiTriangleSmoothC t n 0‖ ≤ |u| := by
  rw [suzukiTriangleSmoothC, suzukiTriangleSmoothC,
    ← Complex.ofReal_sub, Complex.norm_real]
  exact suzukiTriangleSmooth_sub_zero_le t n u

/-- Zeta23's checked `C²_c` explicit formula, applied to every smooth
triangular approximant. -/
theorem suzukiTriangleSmooth_explicitFormula {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier ↦
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (suzukiTriangleSmoothC t n) (Zeta23.gammaOf ρ)) ∧
    ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
          Zeta23.paperFT (suzukiTriangleSmoothC t n) (Zeta23.gammaOf ρ) =
      Zeta23.EF.literatureRHS (suzukiTriangleSmoothC t n) := by
  exact Zeta23.WeilEF.EF_lit_zetaZeroConfig
    (suzukiTriangleSmoothC t n) (contDiff_suzukiTriangleSmoothC t n)
      (hasCompactSupport_suzukiTriangleSmoothC ht n)

/-! ## Fourier transform of the limiting triangular test -/

theorem paperFT_suzukiTriangleTest_eq_intervals {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z =
      (∫ u in (-t)..0, ((t + u : ℝ) : ℂ) *
          Complex.exp (Complex.I * z * (u : ℂ))) +
      ∫ u in 0..t, ((t - u : ℝ) : ℂ) *
          Complex.exp (Complex.I * z * (u : ℂ)) := by
  let F : ℝ → ℂ := fun u ↦
    (suzukiTriangleTest t u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))
  have hsupp : Function.support F ⊆ Set.Ioc (-t) t := by
    intro u hu
    have htri : suzukiTriangleTest t u ≠ 0 := by
      intro hzero
      apply hu
      simp [F, hzero]
    have hpos : 0 < suzukiTriangleTest t u :=
      lt_of_le_of_ne (suzukiTriangleTest_nonneg t u) (Ne.symm htri)
    have habs : |u| < t := by
      simpa [suzukiTriangleTest, max_eq_left (sub_nonneg.mpr (le_of_lt (by
        by_contra hnot
        have : t ≤ |u| := le_of_not_gt hnot
        rw [suzukiTriangleTest_eq_zero_of_le_abs this] at hpos
        exact lt_irrefl 0 hpos)))] using hpos
    exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩
  have hFc : Continuous F := by
    dsimp [F]
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (continuous_suzukiTriangleTest t)
    · fun_prop
  have hleft : IntervalIntegrable F volume (-t) 0 := hFc.intervalIntegrable _ _
  have hright : IntervalIntegrable F volume 0 t := hFc.intervalIntegrable _ _
  rw [Zeta23.paperFT, ← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (-t) 0 := by
      simpa [Set.uIcc_of_le (by linarith : -t ≤ (0 : ℝ))] using hu
    have hnonpos : u ≤ 0 := hu'.2
    have hnonneg : 0 ≤ t + u := by linarith [hu'.1]
    simp [F, suzukiTriangleTest, abs_of_nonpos hnonpos, max_eq_left hnonneg]
  · apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc 0 t := by
      simpa [Set.uIcc_of_le ht] using hu
    have hnonneg : 0 ≤ u := hu'.1
    have hsub : 0 ≤ t - u := sub_nonneg.mpr hu'.2
    simp [F, suzukiTriangleTest, abs_of_nonneg hnonneg, max_eq_left hsub]

private theorem integral_linear_mul_cexp {c : ℂ} (hc : c ≠ 0)
    (A B : ℂ) (a b : ℝ) :
    (∫ u in a..b, (A + B * (u : ℂ)) * Complex.exp (c * (u : ℂ))) =
      Complex.exp (c * (b : ℂ)) *
          ((A + B * (b : ℂ)) / c - B / c ^ 2) -
        Complex.exp (c * (a : ℂ)) *
          ((A + B * (a : ℂ)) / c - B / c ^ 2) := by
  let P : ℝ → ℂ := fun u ↦
    Complex.exp (c * (u : ℂ)) *
      ((A + B * (u : ℂ)) / c - B / c ^ 2)
  have hderiv : ∀ x : ℝ,
      HasDerivAt P ((A + B * (x : ℂ)) * Complex.exp (c * (x : ℂ))) x := by
    intro x
    have hlin : HasDerivAt (fun u : ℝ ↦ c * (u : ℂ)) c x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul c)
    have hexp : HasDerivAt (fun u : ℝ ↦ Complex.exp (c * (u : ℂ)))
        (c * Complex.exp (c * (x : ℂ))) x := by
      simpa [mul_comm] using hlin.cexp
    have haff : HasDerivAt
        (fun u : ℝ ↦ (A + B * (u : ℂ)) / c - B / c ^ 2)
        (B / c) x := by
      have hbase : HasDerivAt (fun u : ℝ ↦ A + B * (u : ℂ)) B x := by
        simpa using ((hasDerivAt_id x).ofReal_comp.const_mul B).const_add A
      simpa using (hbase.div_const c).sub_const (B / c ^ 2)
    dsimp only [P]
    exact (hexp.mul haff).congr_deriv (by
      field_simp [hc]
      ring)
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ (A + B * (u : ℂ)) * Complex.exp (c * (u : ℂ))) volume a b := by
    exact (by fun_prop : Continuous
      (fun u : ℝ ↦ (A + B * (u : ℂ)) * Complex.exp (c * (u : ℂ)))).intervalIntegrable _ _
  simpa only [P] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x) hint)

theorem paperFT_suzukiTriangleTest_exp {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z =
      (Complex.exp (Complex.I * z * (t : ℂ)) +
          Complex.exp (-Complex.I * z * (t : ℂ)) - 2) /
        (Complex.I * z) ^ 2 := by
  let c : ℂ := Complex.I * z
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hneg := integral_linear_mul_cexp hc (t : ℂ) 1 (-t) 0
  have hpos := integral_linear_mul_cexp hc (t : ℂ) (-1) 0 t
  dsimp [c] at hneg hpos
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hneg hpos
  rw [paperFT_suzukiTriangleTest_eq_intervals ht]
  simp_rw [Complex.ofReal_add, Complex.ofReal_sub]
  rw [hneg, hpos]
  push_cast
  field_simp [Complex.I_ne_zero, hz]
  simp
  ring

theorem paperFT_suzukiTriangleTest_of_ne {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z =
      2 * (1 - Complex.cos (z * (t : ℂ))) / z ^ 2 := by
  rw [paperFT_suzukiTriangleTest_exp ht hz]
  rw [Complex.cos]
  field_simp [Complex.I_ne_zero, hz]
  rw [Complex.I_sq]
  ring

@[simp] theorem paperFT_suzukiTriangleTest_zero {t : ℝ} (ht : 0 ≤ t) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) 0 = (t : ℂ) ^ 2 := by
  rw [paperFT_suzukiTriangleTest_eq_intervals ht]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hneg : (∫ u in (-t)..0, t + u) = t ^ 2 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ ↦ t) volume (-t) 0 :=
      continuous_const.intervalIntegrable _ _
    have hi : IntervalIntegrable (fun u : ℝ ↦ u) volume (-t) 0 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_add hc hi, integral_id]
    simp
    ring
  have hpos : (∫ u in 0..t, t - u) = t ^ 2 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ ↦ t) volume 0 t :=
      continuous_const.intervalIntegrable _ _
    have hi : IntervalIntegrable (fun u : ℝ ↦ u) volume 0 t :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hc hi, integral_id]
    simp
    ring
  rw [hneg, hpos]
  push_cast
  ring

theorem zeta23_gammaOf_ne_zero
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.gammaOf (ρ : ℂ) ≠ 0 := by
  intro hγ
  have hρ : (ρ : ℂ) = (1 / 2 : ℂ) := by
    have hsub : (ρ : ℂ) - (1 / 2 : ℂ) = 0 := by
      simpa [Zeta23.gammaOf] using hγ
    exact sub_eq_zero.mp hsub
  apply riemannZeta_half_ne_zero
  rw [← hρ]
  exact ρ.property.1

/-- The exact tent transform has quadratic decay throughout the closed
spectral strip. -/
theorem norm_paperFT_suzukiTriangleTest_complex_le {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ≠ 0) (him : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z‖ ≤
      (2 * Real.exp (t / 2) + 2) / ‖z‖ ^ 2 := by
  rw [paperFT_suzukiTriangleTest_exp ht hz, norm_div, norm_pow,
    norm_mul, norm_I, one_mul]
  have hre₁ : (Complex.I * z * (t : ℂ)).re = -z.im * t := by
    simp [Complex.mul_re]
  have hre₂ : (-Complex.I * z * (t : ℂ)).re = z.im * t := by
    simp [Complex.mul_re]
  have hzt : |z.im| * t ≤ t / 2 := by
    nlinarith [abs_nonneg z.im]
  have h₁ : ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp (t / 2) := by
    rw [Complex.norm_exp, hre₁]
    apply Real.exp_le_exp.mpr
    calc
      -z.im * t ≤ |z.im| * t := by
        exact mul_le_mul_of_nonneg_right (neg_le_abs z.im) ht
      _ ≤ t / 2 := hzt
  have h₂ : ‖Complex.exp (-Complex.I * z * (t : ℂ))‖ ≤ Real.exp (t / 2) := by
    rw [Complex.norm_exp, hre₂]
    apply Real.exp_le_exp.mpr
    calc
      z.im * t ≤ |z.im| * t := by
        exact mul_le_mul_of_nonneg_right (le_abs_self z.im) ht
      _ ≤ t / 2 := hzt
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    ‖Complex.exp (Complex.I * z * (t : ℂ)) +
        Complex.exp (-Complex.I * z * (t : ℂ)) - 2‖ ≤
        ‖Complex.exp (Complex.I * z * (t : ℂ))‖ +
          ‖Complex.exp (-Complex.I * z * (t : ℂ))‖ + 2 := by
      calc
        _ ≤ ‖Complex.exp (Complex.I * z * (t : ℂ)) +
              Complex.exp (-Complex.I * z * (t : ℂ))‖ + ‖(2 : ℂ)‖ :=
          norm_sub_le _ _
        _ ≤ (‖Complex.exp (Complex.I * z * (t : ℂ))‖ +
              ‖Complex.exp (-Complex.I * z * (t : ℂ))‖) + ‖(2 : ℂ)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by norm_num
    _ ≤ 2 * Real.exp (t / 2) + 2 := by linarith

/-! ## Fourier factorization of the mollifications -/

def suzukiTriangleMollifierC (n : ℕ) (u : ℝ) : ℂ :=
  ((suzukiTriangleMollifier n).normed volume u : ℂ)

theorem continuous_suzukiTriangleMollifierC (n : ℕ) :
    Continuous (suzukiTriangleMollifierC n) := by
  exact Complex.continuous_ofReal.comp (suzukiTriangleMollifier n).continuous_normed

theorem hasCompactSupport_suzukiTriangleMollifierC (n : ℕ) :
    HasCompactSupport (suzukiTriangleMollifierC n) :=
  (suzukiTriangleMollifier n).hasCompactSupport_normed.comp_left Complex.ofReal_zero

theorem continuous_suzukiTriangleTestC (t : ℝ) :
    Continuous (fun u ↦ (suzukiTriangleTest t u : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_suzukiTriangleTest t)

theorem hasCompactSupport_suzukiTriangleTestC {t : ℝ} (ht : 0 ≤ t) :
    HasCompactSupport (fun u ↦ (suzukiTriangleTest t u : ℂ)) :=
  (hasCompactSupport_suzukiTriangleTest ht).comp_left Complex.ofReal_zero

theorem Zeta23_tilde_suzukiTriangleTest (t : ℝ) :
    Zeta23.EF.tilde (fun u ↦ (suzukiTriangleTest t u : ℂ)) =
      (fun u ↦ (suzukiTriangleTest t u : ℂ)) := by
  funext u
  simp [Zeta23.EF.tilde]

theorem suzukiTriangleSmoothC_eq_weilTest (t : ℝ) (n : ℕ) :
    suzukiTriangleSmoothC t n =
      Zeta23.EF.weilTest (suzukiTriangleMollifierC n)
        (fun u ↦ (suzukiTriangleTest t u : ℂ)) := by
  funext u
  unfold suzukiTriangleSmoothC suzukiTriangleSmooth Zeta23.EF.weilTest
    suzukiTriangleMollifierC
  simp only [convolution_def, lsmul_apply, smul_eq_mul,
    ContinuousLinearMap.mul_apply']
  rw [Zeta23_tilde_suzukiTriangleTest]
  have heq :
      (fun x : ℝ ↦
        ((suzukiTriangleMollifier n).normed volume x : ℂ) *
          (suzukiTriangleTest t (u - x) : ℂ)) =
      (fun x : ℝ ↦ (((suzukiTriangleMollifier n).normed volume x *
        suzukiTriangleTest t (u - x) : ℝ) : ℂ)) := by
    funext x
    exact (Complex.ofReal_mul _ _).symm
  rw [heq]
  exact (integral_complex_ofReal
    (f := fun x : ℝ ↦ (suzukiTriangleMollifier n).normed volume x *
      suzukiTriangleTest t (u - x))).symm

theorem paperFT_suzukiTriangleSmoothC (t : ℝ) (ht : 0 ≤ t)
    (n : ℕ) (z : ℂ) :
    Zeta23.paperFT (suzukiTriangleSmoothC t n) z =
      Zeta23.paperFT (suzukiTriangleMollifierC n) z *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z := by
  rw [suzukiTriangleSmoothC_eq_weilTest]
  rw [Zeta23.EF.paperFT_weilTest
    (continuous_suzukiTriangleMollifierC n) (continuous_suzukiTriangleTestC t)
    (hasCompactSupport_suzukiTriangleMollifierC n)
    (hasCompactSupport_suzukiTriangleTestC ht)]
  rw [← Zeta23.EF.paperFT_tilde]
  rw [Zeta23_tilde_suzukiTriangleTest]

theorem integrable_suzukiTriangleMollifierC (n : ℕ) :
    Integrable (suzukiTriangleMollifierC n) := by
  exact Complex.ofRealCLM.integrable_comp (suzukiTriangleMollifier n).integrable_normed

theorem integral_norm_suzukiTriangleMollifierC (n : ℕ) :
    ∫ u : ℝ, ‖suzukiTriangleMollifierC n u‖ = 1 := by
  have hnonneg : ∀ u : ℝ, 0 ≤ (suzukiTriangleMollifier n).normed volume u :=
    (suzukiTriangleMollifier n).nonneg_normed
  calc
    (∫ u : ℝ, ‖suzukiTriangleMollifierC n u‖) =
        ∫ u : ℝ, (suzukiTriangleMollifier n).normed volume u := by
      apply integral_congr_ae
      filter_upwards with u
      simp [suzukiTriangleMollifierC, abs_of_nonneg (hnonneg u)]
    _ = 1 := (suzukiTriangleMollifier n).integral_normed

theorem norm_paperFT_suzukiTriangleMollifierC_le (n : ℕ) (z : ℂ) :
    ‖Zeta23.paperFT (suzukiTriangleMollifierC n) z‖ ≤
      Real.exp (|z.im| * (suzukiTriangleMollifier n).rOut) := by
  have hsupp : ∀ u : ℝ, suzukiTriangleMollifierC n u ≠ 0 →
      |u| ≤ (suzukiTriangleMollifier n).rOut := by
    intro u hu
    have humem : u ∈ Function.support ((suzukiTriangleMollifier n).normed volume) := by
      simpa [Function.mem_support, suzukiTriangleMollifierC] using hu
    have huball : u ∈ Metric.ball (0 : ℝ) (suzukiTriangleMollifier n).rOut := by
      simpa only [(suzukiTriangleMollifier n).support_normed_eq] using humem
    have hubound : |u| < (suzukiTriangleMollifier n).rOut := by
      simpa [Metric.mem_ball, Real.dist_eq] using huball
    exact hubound.le
  simpa [integral_norm_suzukiTriangleMollifierC] using
    (Zeta23.norm_paperFT_le (integrable_suzukiTriangleMollifierC n) hsupp z)

theorem tendsto_paperFT_suzukiTriangleMollifierC (z : ℂ) :
    Tendsto (fun n : ℕ ↦ Zeta23.paperFT (suzukiTriangleMollifierC n) z)
      atTop (nhds 1) := by
  let g : ℝ → ℂ := fun u ↦ Complex.exp (-Complex.I * z * (u : ℂ))
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
    (g := g) (μ := volume) tendsto_suzukiTriangleMollifier_rOut hg 0
  have heq : ∀ n : ℕ,
      ((suzukiTriangleMollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] g) 0 =
        Zeta23.paperFT (suzukiTriangleMollifierC n) z := by
    intro n
    unfold Zeta23.paperFT suzukiTriangleMollifierC
    simp only [convolution_def, lsmul_apply, smul_eq_mul, zero_sub]
    apply integral_congr_ae
    filter_upwards with u
    congr 1
    dsimp [g]
    congr 1
    push_cast
    ring
  have hconv' := hconv.congr' (Eventually.of_forall heq)
  simpa [g] using hconv'

theorem tendsto_paperFT_suzukiTriangleSmoothC (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    Tendsto (fun n : ℕ ↦ Zeta23.paperFT (suzukiTriangleSmoothC t n) z)
      atTop (nhds (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z)) := by
  simpa only [paperFT_suzukiTriangleSmoothC t ht, one_mul] using
    (tendsto_paperFT_suzukiTriangleMollifierC z).mul_const
      (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) z)

/-! ## The finite prime functional -/

/-- The von Mangoldt functional occurring in the literature-form zeta
explicit formula.  It is kept in the exact `Zeta23` normalization here; the
factor two coming from an even test is removed only when it is compared with
`suzukiPsiPrimeContribution`. -/
noncomputable def suzukiTrianglePrimeFunctional (k : ℝ → ℂ) : ℂ :=
  ∑' m : ℕ, ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
    (k (Real.log m) + k (-Real.log m))

theorem tsupport_suzukiTriangleSmoothC_subset {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    tsupport (suzukiTriangleSmoothC t n) ⊆ Set.Icc (-(t + 1)) (t + 1) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  apply support_suzukiTriangleSmooth_subset ht n
  simpa [Function.mem_support, suzukiTriangleSmoothC] using hu

theorem tsupport_suzukiTriangleTestC_subset {t : ℝ} (ht : 0 ≤ t) :
    tsupport (fun u ↦ (suzukiTriangleTest t u : ℂ)) ⊆
      Set.Icc (-(t + 1)) (t + 1) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hut : u ∈ Set.Icc (-t) t := by
    apply support_suzukiTriangleTest_subset ht
    simpa [Function.mem_support] using hu
  constructor <;> linarith [hut.1, hut.2]

theorem tsupport_suzukiTriangleTestC_subset_exact {t : ℝ} (ht : 0 ≤ t) :
    tsupport (fun u ↦ (suzukiTriangleTest t u : ℂ)) ⊆ Set.Icc (-t) t := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  apply support_suzukiTriangleTest_subset ht
  simpa [Function.mem_support] using hu

theorem suzukiTrianglePrimeFunctional_smooth_eq_sum {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) :
    suzukiTrianglePrimeFunctional (suzukiTriangleSmoothC t n) =
      ∑ m ∈ Finset.Ioc 0 ⌊Real.exp (t + 1)⌋₊,
        ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          (suzukiTriangleSmoothC t n (Real.log m) +
            suzukiTriangleSmoothC t n (-Real.log m)) := by
  unfold suzukiTrianglePrimeFunctional
  exact tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp (t + 1)⌋₊)
    (fun _ hm ↦ Zeta23.EF.prime_summand_eq_zero
      (tsupport_suzukiTriangleSmoothC_subset ht n) hm)

theorem suzukiTrianglePrimeFunctional_test_eq_sum {t : ℝ} (ht : 0 ≤ t) :
    suzukiTrianglePrimeFunctional (fun u ↦ (suzukiTriangleTest t u : ℂ)) =
      ∑ m ∈ Finset.Ioc 0 ⌊Real.exp (t + 1)⌋₊,
        ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          ((suzukiTriangleTest t (Real.log m) : ℂ) +
            (suzukiTriangleTest t (-Real.log m) : ℂ)) := by
  unfold suzukiTrianglePrimeFunctional
  exact tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp (t + 1)⌋₊)
    (fun _ hm ↦ Zeta23.EF.prime_summand_eq_zero
      (tsupport_suzukiTriangleTestC_subset ht) hm)

theorem tendsto_suzukiTriangle_primeSide {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun n : ℕ ↦ suzukiTrianglePrimeFunctional (suzukiTriangleSmoothC t n))
      atTop
      (nhds (suzukiTrianglePrimeFunctional
        (fun u ↦ (suzukiTriangleTest t u : ℂ)))) := by
  rw [suzukiTrianglePrimeFunctional_test_eq_sum ht]
  simp_rw [suzukiTrianglePrimeFunctional_smooth_eq_sum ht]
  apply tendsto_finsetSum
  intro m _
  exact Tendsto.const_mul _
    ((tendsto_suzukiTriangleSmoothC t (Real.log m)).add
      (tendsto_suzukiTriangleSmoothC t (-Real.log m)))

theorem suzukiTrianglePrimeFunctional_test_eq_two_primeContribution
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiTrianglePrimeFunctional (fun u ↦ (suzukiTriangleTest t u : ℂ)) =
      (2 * suzukiPsiPrimeContribution t : ℝ) := by
  unfold suzukiTrianglePrimeFunctional suzukiPsiPrimeContribution
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp t⌋₊)
    (fun _ hm ↦ Zeta23.EF.prime_summand_eq_zero
      (tsupport_suzukiTriangleTestC_subset_exact ht) hm)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hmt : Real.log m ≤ t := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast (Finset.mem_Ioc.mp hm).1)).mpr
    exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hm).2).trans
      (Nat.floor_le (Real.exp_pos t).le)
  rw [suzukiTriangleTest_neg]
  simp only [suzukiTriangleTest, abs_of_nonneg hlog,
    max_eq_left (sub_nonneg.mpr hmt)]
  push_cast
  ring

/-! ## A uniform Fourier majorant for the Gamma bracket -/

theorem integrable_suzukiTriangleTestC {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun u ↦ (suzukiTriangleTest t u : ℂ)) :=
  (continuous_suzukiTriangleTestC t).integrable_of_hasCompactSupport
    (hasCompactSupport_suzukiTriangleTestC ht)

theorem integral_norm_suzukiTriangleTestC {t : ℝ} (ht : 0 ≤ t) :
    (∫ u : ℝ, ‖(suzukiTriangleTest t u : ℂ)‖) = t ^ 2 := by
  have hzero := paperFT_suzukiTriangleTest_zero ht
  unfold Zeta23.paperFT at hzero
  simp at hzero
  have hreal : (∫ u : ℝ, suzukiTriangleTest t u) = t ^ 2 := by
    exact_mod_cast hzero
  calc
    (∫ u : ℝ, ‖(suzukiTriangleTest t u : ℂ)‖) =
        ∫ u : ℝ, suzukiTriangleTest t u := by
      apply integral_congr_ae
      filter_upwards with u
      simp [Real.norm_eq_abs, abs_of_nonneg (suzukiTriangleTest_nonneg t u)]
    _ = t ^ 2 := hreal

theorem norm_paperFT_suzukiTriangleTest_le_sq {t : ℝ} (ht : 0 ≤ t)
    (r : ℝ) :
    ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r‖ ≤ t ^ 2 := by
  have hsupp : ∀ u : ℝ, (suzukiTriangleTest t u : ℂ) ≠ 0 → |u| ≤ t := by
    intro u hu
    exact abs_le.mpr (support_suzukiTriangleTest_subset ht (by
      simpa [Function.mem_support] using hu))
  have h := Zeta23.norm_paperFT_le
    (integrable_suzukiTriangleTestC ht) hsupp (r : ℂ)
  rw [integral_norm_suzukiTriangleTestC ht] at h
  simpa using h

theorem norm_paperFT_suzukiTriangleTest_mul_sq_le_four {t : ℝ} (ht : 0 ≤ t)
    (r : ℝ) :
    ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r‖ * r ^ 2 ≤ 4 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [paperFT_suzukiTriangleTest_of_ne ht (by exact_mod_cast hr)]
  have hcos : ‖(1 : ℂ) - Complex.cos ((r : ℂ) * (t : ℂ))‖ ≤ 2 := by
    rw [show (r : ℂ) * (t : ℂ) = ((r * t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · linarith [Real.neg_one_le_cos (r * t), Real.cos_le_one (r * t)]
    · linarith [Real.cos_le_one (r * t)]
  rw [norm_div, norm_mul, norm_ofNat, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  field_simp
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.cos ((r : ℂ) * (t : ℂ)))]

theorem norm_paperFT_suzukiTriangleTest_le_decay {t : ℝ} (ht : 0 ≤ t)
    (r : ℝ) :
    ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r‖ ≤
      (t ^ 2 + 4) / (1 + r ^ 2) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + r ^ 2)]
  rw [mul_add, mul_one]
  exact add_le_add (norm_paperFT_suzukiTriangleTest_le_sq ht r)
    (norm_paperFT_suzukiTriangleTest_mul_sq_le_four ht r)

theorem continuous_gammaBracketC :
    Continuous (fun r : ℝ ↦ (Zeta23.EF.gammaBracket r : ℂ)) := by
  have hmu : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  have heq : (fun r : ℝ ↦ (Zeta23.EF.gammaBracket r : ℂ)) =
      fun r : ℝ ↦ ((2 * Real.pi * Zeta23.mu r : ℝ) : ℂ) := by
    funext r
    unfold Zeta23.EF.gammaBracket Zeta23.mu
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  exact Complex.continuous_ofReal.comp
    ((continuous_const.mul hmu))

theorem gammaBracketC_growth :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ,
      ‖(Zeta23.EF.gammaBracket r : ℂ)‖ ≤ M * Real.log (2 + |r|) := by
  obtain ⟨C, hC, hdig⟩ := Zeta23.WeilEF.digamma_growth_strip
  let D : ℝ := |Real.log Real.pi| / Real.log 2
  refine ⟨C + D, add_nonneg hC.le
    (div_nonneg (abs_nonneg _) (Real.log_pos (by norm_num)).le), ?_⟩
  intro r
  have hψ := hdig (1 / 4 + Complex.I * (r : ℂ) / 2) (by simp) (by norm_num)
  have him : |(1 / 4 + Complex.I * (r : ℂ) / 2 : ℂ).im| = |r| / 2 := by
    simp [abs_div]
  rw [him] at hψ
  have hlogs : Real.log (2 + |r| / 2) ≤ Real.log (2 + |r|) := by
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg r])
  have hlog0 : 0 ≤ Real.log (2 + |r|) :=
    Real.log_nonneg (by linarith [abs_nonneg r])
  have hψ' : ‖Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)‖ ≤
      C * Real.log (2 + |r|) :=
    hψ.trans (mul_le_mul_of_nonneg_left hlogs hC.le)
  have hlog2 : Real.log 2 ≤ Real.log (2 + |r|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg r])
  have hD0 : 0 ≤ D := div_nonneg (abs_nonneg _)
    (Real.log_pos (by norm_num)).le
  have hconst : |Real.log Real.pi| ≤ D * Real.log (2 + |r|) := by
    calc
      |Real.log Real.pi| = D * Real.log 2 := by
        dsimp [D]
        field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      _ ≤ D * Real.log (2 + |r|) := mul_le_mul_of_nonneg_left hlog2 hD0
  rw [Zeta23.EF.gammaBracket, Complex.norm_real, Real.norm_eq_abs]
  calc
    |(Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)).re -
        Real.log Real.pi| ≤
        ‖Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)‖ +
          |Real.log Real.pi| :=
      (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm _) le_rfl)
    _ ≤ C * Real.log (2 + |r|) + D * Real.log (2 + |r|) :=
      add_le_add hψ' hconst
    _ = (C + D) * Real.log (2 + |r|) := by ring

theorem integrable_suzukiTriangle_gammaSide {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun r : ℝ ↦
      Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r *
        (Zeta23.EF.gammaBracket r : ℂ)) := by
  obtain ⟨M, hM, hgamma⟩ := gammaBracketC_growth
  apply Zeta23.XiPrime.integrable_decay_mul_log
    ((Zeta23.WeilEF.differentiable_paperFT
      (continuous_suzukiTriangleTestC t)
      (hasCompactSupport_suzukiTriangleTestC ht)).continuous.comp
        Complex.continuous_ofReal)
    continuous_gammaBracketC
    (show 0 ≤ t ^ 2 + 4 by positivity)
    (norm_paperFT_suzukiTriangleTest_le_decay ht)
    hM hgamma

/-- The Gamma-bracket functional in the exact normalization of
`Zeta23.EF.literatureRHS`. -/
noncomputable def suzukiTriangleGammaFunctional (k : ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

theorem norm_paperFT_suzukiTriangleSmoothC_real_le (t : ℝ) (ht : 0 ≤ t)
    (n : ℕ) (r : ℝ) :
    ‖Zeta23.paperFT (suzukiTriangleSmoothC t n) r‖ ≤
      ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r‖ := by
  rw [paperFT_suzukiTriangleSmoothC t ht]
  have hm := norm_paperFT_suzukiTriangleMollifierC_le n (r : ℂ)
  have hm1 : ‖Zeta23.paperFT (suzukiTriangleMollifierC n) (r : ℂ)‖ ≤ 1 := by
    simpa using hm
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hm1 (norm_nonneg _)).trans_eq (one_mul _)

theorem tendsto_suzukiTriangle_gammaSide {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun n : ℕ ↦ suzukiTriangleGammaFunctional (suzukiTriangleSmoothC t n))
      atTop
      (nhds (suzukiTriangleGammaFunctional
        (fun u ↦ (suzukiTriangleTest t u : ℂ)))) := by
  let g : ℝ → ℝ := fun r ↦
    ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ)‖
  have hg : Integrable g := (integrable_suzukiTriangle_gammaSide ht).norm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun r : ℝ ↦ Zeta23.paperFT (suzukiTriangleSmoothC t n) r *
        (Zeta23.EF.gammaBracket r : ℂ)) := by
    intro n
    exact (((Zeta23.WeilEF.differentiable_paperFT
      (contDiff_suzukiTriangleSmoothC t n).continuous
      (hasCompactSupport_suzukiTriangleSmoothC ht n)).continuous.comp
        Complex.continuous_ofReal).mul continuous_gammaBracketC).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ r : ℝ ∂volume,
      ‖Zeta23.paperFT (suzukiTriangleSmoothC t n) r *
        (Zeta23.EF.gammaBracket r : ℂ)‖ ≤ g r := by
    intro n
    filter_upwards with r
    dsimp [g]
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_paperFT_suzukiTriangleSmoothC_real_le t ht n r) (norm_nonneg _)
  have hlim : ∀ᵐ r : ℝ ∂volume, Tendsto
      (fun n : ℕ ↦ Zeta23.paperFT (suzukiTriangleSmoothC t n) r *
        (Zeta23.EF.gammaBracket r : ℂ)) atTop
      (nhds (Zeta23.paperFT
        (fun u ↦ (suzukiTriangleTest t u : ℂ)) r *
          (Zeta23.EF.gammaBracket r : ℂ))) := by
    filter_upwards with r
    exact (tendsto_paperFT_suzukiTriangleSmoothC t ht r).mul_const _
  simpa [suzukiTriangleGammaFunctional] using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      g hmeas hg hbound hlim

/-! ## The structural right-hand-side limit -/

/-- The literature-form explicit-formula right-hand side evaluated at the
triangular test.  Keeping this structural form separates the approximation
argument from the later closed evaluation of its archimedean bracket. -/
noncomputable def suzukiTriangleLiteratureRHS (t : ℝ) : ℂ :=
  Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) (Complex.I / 2) +
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) (-Complex.I / 2) -
    suzukiTrianglePrimeFunctional (fun u ↦ (suzukiTriangleTest t u : ℂ)) +
    (1 / (2 * Real.pi) : ℂ) *
      suzukiTriangleGammaFunctional (fun u ↦ (suzukiTriangleTest t u : ℂ))

theorem Zeta23_literatureRHS_suzukiTriangleSmoothC (t : ℝ) (n : ℕ) :
    Zeta23.EF.literatureRHS (suzukiTriangleSmoothC t n) =
      Zeta23.paperFT (suzukiTriangleSmoothC t n) (Complex.I / 2) +
        Zeta23.paperFT (suzukiTriangleSmoothC t n) (-Complex.I / 2) -
        suzukiTrianglePrimeFunctional (suzukiTriangleSmoothC t n) +
        (1 / (2 * Real.pi) : ℂ) *
          suzukiTriangleGammaFunctional (suzukiTriangleSmoothC t n) := by
  rfl

theorem tendsto_suzukiTriangle_literatureRHS {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun n : ℕ ↦ Zeta23.EF.literatureRHS (suzukiTriangleSmoothC t n))
      atTop (nhds (suzukiTriangleLiteratureRHS t)) := by
  simp_rw [Zeta23_literatureRHS_suzukiTriangleSmoothC]
  unfold suzukiTriangleLiteratureRHS
  exact ((((tendsto_paperFT_suzukiTriangleSmoothC t ht (Complex.I / 2)).add
    (tendsto_paperFT_suzukiTriangleSmoothC t ht (-Complex.I / 2))).sub
      (tendsto_suzukiTriangle_primeSide ht)).add
        (Tendsto.const_mul _ (tendsto_suzukiTriangle_gammaSide ht)))

/-! ## The spectral-side limit -/

/-- Absolute convergence of the multiplicity-weighted tent transform over
the distinct nontrivial zeta zeros. -/
theorem summable_suzukiTriangle_zeroSide {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier ↦
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)) := by
  let D : ℝ := 2 * Real.exp (t / 2) + 2
  let C : ℝ := 2 * D
  have hbase : Summable (fun ρ : Zeta23.zetaZeroConfig.carrier ↦
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) /
        (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
    simpa [Zeta23.zetaZeroConfig] using
      Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam
  refine Summable.of_norm_bounded_eventually (hbase.mul_left C) ?_
  have hfin := Zeta23.zetaZeroConfig.finite_window (-1) 1
  have hSfin : ((fun ρ : Zeta23.zetaZeroConfig.carrier ↦ (ρ : ℂ)) ⁻¹'
      (Zeta23.zetaZeroConfig.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, Zeta23.ZeroConfig.window,
    Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Zeta23.zetaZeroConfig.carrier := ρ.property
  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hγ1 : 1 ≤ ‖Zeta23.gammaOf (ρ : ℂ)‖ :=
    him.trans (Zeta23.WeilEF.abs_im_le_norm_gammaOf _)
  have hstrip := Zeta23.zetaZeroConfig.strip _ hρmem
  have himγ : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    Zeta23.WeilEF.abs_gammaOf_im_le hstrip
  have hFT := norm_paperFT_suzukiTriangleTest_complex_le ht
    (zeta23_gammaOf_ne_zero ρ) himγ
  have hnsq : Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) =
      ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hinv : 1 / ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 ≤
      2 * (1 / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) := by
    rw [hnsq, div_le_iff₀ (by positivity)]
    have hpos : 0 < 1 + ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 := by positivity
    rw [show 2 * (1 / (1 + ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2)) *
        ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 =
          2 * ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 /
            (1 + ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2) by ring,
      le_div_iff₀ hpos]
    nlinarith
  rw [norm_mul, Complex.norm_natCast]
  have hm : (0 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  calc
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)‖ ≤
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
        (D / ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hFT hm
    _ = (Zeta23.zetaZeroConfig.mult ρ : ℝ) * D *
        (1 / ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2) := by ring
    _ ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) * D *
        (2 * (1 / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ))))) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg hm (by dsimp [D]; positivity))
    _ = C * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) /
        (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) := by
      dsimp [C]
      ring

/-- The zero side of Zeta23's smooth explicit formulas converges to the
ordinary, absolutely convergent tent-transform zero side. -/
theorem tendsto_suzukiTriangle_zeroSide {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun n : ℕ ↦ ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
          Zeta23.paperFT (suzukiTriangleSmoothC t n) (Zeta23.gammaOf ρ))
      atTop
      (nhds (∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
          Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
            (Zeta23.gammaOf ρ))) := by
  let bound : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ ↦
    Real.exp (1 / 2) *
      ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)‖
  have hbound : Summable bound :=
    (summable_suzukiTriangle_zeroSide ht).norm.mul_left (Real.exp (1 / 2))
  apply tendsto_tsum_of_dominated_convergence hbound
  · intro ρ
    exact Tendsto.const_mul _
      (tendsto_paperFT_suzukiTriangleSmoothC t ht (Zeta23.gammaOf ρ))
  · filter_upwards with n
    intro ρ
    rw [paperFT_suzukiTriangleSmoothC t ht]
    have hm := norm_paperFT_suzukiTriangleMollifierC_le n (Zeta23.gammaOf ρ)
    have him := Zeta23.WeilEF.abs_gammaOf_im_le
      (Zeta23.zetaZeroConfig.strip ρ ρ.property)
    have hr : (suzukiTriangleMollifier n).rOut ≤ 1 := by
      rw [suzukiTriangleMollifier_rOut]
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show (1 : ℝ) ≤ n + 1 by norm_num))
    have hexp : Real.exp (|(Zeta23.gammaOf (ρ : ℂ)).im| *
        (suzukiTriangleMollifier n).rOut) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg (Zeta23.gammaOf (ρ : ℂ)).im,
        (suzukiTriangleMollifier n).rOut_pos.le]
    dsimp [bound]
    simp only [norm_mul]
    calc
      ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ)‖ *
          (‖Zeta23.paperFT (suzukiTriangleMollifierC n) (Zeta23.gammaOf ρ)‖ *
            ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
              (Zeta23.gammaOf ρ)‖) ≤
        ‖(Zeta23.zetaZeroConfig.mult ρ : ℂ)‖ *
          (Real.exp (1 / 2) *
            ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
              (Zeta23.gammaOf ρ)‖) := by
        gcongr
        exact hm.trans hexp
      _ = Real.exp (1 / 2) *
          (‖(Zeta23.zetaZeroConfig.mult ρ : ℂ)‖ *
            ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
              (Zeta23.gammaOf ρ)‖) := by ring

/-- The Zeta23 distinct-zero carrier and RH Garden's xi-divisor support are
the same set, packaged as an equivalence so their two multiplicity
conventions can be transported transparently. -/
noncomputable def zeta23ZeroEquivXiZero :
    Zeta23.zetaZeroConfig.carrier ≃ XiZero where
  toFun ρ := ⟨ρ, by
    rw [mem_xiDivisor_support_iff_nontrivialZetaZero,
      isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo]
    exact ρ.property⟩
  invFun ρ := ⟨ρ, by
    exact (isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo ρ).mp
      ((mem_xiDivisor_support_iff_nontrivialZetaZero ρ).mp ρ.property)⟩
  left_inv ρ := by ext; rfl
  right_inv ρ := by ext; rfl

@[simp] theorem zeta23ZeroEquivXiZero_value
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    ((zeta23ZeroEquivXiZero ρ : XiZero) : ℂ) = (ρ : ℂ) := rfl

@[simp] theorem zeta23ZeroEquivXiZero_symm_value (ρ : XiZero) :
    ((zeta23ZeroEquivXiZero.symm ρ :
      Zeta23.zetaZeroConfig.carrier) : ℂ) = (ρ : ℂ) := rfl

theorem zeta23ZeroEquivXiZero_multiplicity
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zetaZeroConfig.mult ρ =
      xiMultiplicity (zeta23ZeroEquivXiZero ρ : XiZero) := by
  rw [xiMultiplicity_eq_zetaMultiplicity]
  · rfl
  · exact (mem_xiDivisor_support_iff_nontrivialZetaZero _).mp
      (zeta23ZeroEquivXiZero ρ).property

theorem zeta23_gammaOf_eq_neg_spectral
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.gammaOf (ρ : ℂ) =
      -Complex.I * ((zeta23ZeroEquivXiZero ρ : XiZero) - (1 / 2 : ℂ)) := by
  change ((ρ : ℂ) - 1 / 2) / Complex.I =
    -Complex.I * ((ρ : ℂ) - 1 / 2)
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The occurrence-indexed transform of the triangular test. -/
def suzukiTriangleOccurrenceTerm (t : ℝ) (a : XiZeroOccurrence) : ℂ :=
  Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
    (-xiSpectralParameter a)

theorem summable_suzukiTriangleOccurrenceTerm {t : ℝ} (ht : 0 ≤ t) :
    Summable (suzukiTriangleOccurrenceTerm t) := by
  have hmajorant := xiSpectral_reciprocal_sq_summable.mul_left
    (2 * Real.exp (t / 2) + 2)
  apply Summable.of_norm_bounded hmajorant
  intro a
  rw [suzukiTriangleOccurrenceTerm]
  have h := norm_paperFT_suzukiTriangleTest_complex_le ht
    (neg_ne_zero.mpr (xiSpectralParameter_ne_zero a))
    (by
      simpa only [Complex.neg_im, abs_neg] using
        abs_xiSpectralParameter_im_le_half a)
  simpa [norm_neg, div_eq_mul_inv] using h

theorem suzukiTriangleOccurrenceTerm_eq_add {t : ℝ} (ht : 0 ≤ t)
    (a : XiZeroOccurrence) :
    suzukiTriangleOccurrenceTerm t a =
      suzukiPsiZeroTerm t a + suzukiPsiZeroTerm (-t) a := by
  rw [suzukiTriangleOccurrenceTerm,
    paperFT_suzukiTriangleTest_of_ne ht
      (neg_ne_zero.mpr (xiSpectralParameter_ne_zero a))]
  unfold suzukiPsiZeroTerm
  rw [Complex.cos]
  push_cast
  field_simp [xiSpectralParameter_ne_zero a]
  ring

theorem tsum_suzukiTriangleOccurrenceTerm_eq_two_psi {t : ℝ} (ht : 0 ≤ t) :
    (∑' a : XiZeroOccurrence, suzukiTriangleOccurrenceTerm t a) =
      2 * suzukiPsiZero t := by
  calc
    (∑' a : XiZeroOccurrence, suzukiTriangleOccurrenceTerm t a) =
        ∑' a : XiZeroOccurrence,
          (suzukiPsiZeroTerm t a + suzukiPsiZeroTerm (-t) a) := by
      apply tsum_congr
      exact suzukiTriangleOccurrenceTerm_eq_add ht
    _ = (∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a) +
        ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm (-t) a :=
      (summable_suzukiPsiZero_term t).tsum_add
        (summable_suzukiPsiZero_term (-t))
    _ = suzukiPsiZero t + suzukiPsiZero (-t) := rfl
    _ = 2 * suzukiPsiZero t := by rw [suzukiPsiZero_neg]; ring

def suzukiTriangleXiZeroTerm (t : ℝ) (ρ : XiZero) : ℂ :=
  Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
    (-Complex.I * ((ρ : ℂ) - (1 / 2 : ℂ)))

@[simp] theorem suzukiTriangleXiZeroTerm_occurrence
    (t : ℝ) (a : XiZeroOccurrence) :
    suzukiTriangleXiZeroTerm t a.1 = suzukiTriangleOccurrenceTerm t a := by
  simp [suzukiTriangleXiZeroTerm, suzukiTriangleOccurrenceTerm,
    xiSpectralParameter, XiZeroOccurrence.value]

theorem tsum_suzukiTriangleOccurrenceTerm_eq_weighted {t : ℝ} (ht : 0 ≤ t) :
    (∑' a : XiZeroOccurrence, suzukiTriangleOccurrenceTerm t a) =
      ∑' ρ : XiZero, (xiMultiplicity (ρ : ℂ) : ℂ) *
        suzukiTriangleXiZeroTerm t ρ := by
  have hs := summable_suzukiTriangleOccurrenceTerm ht
  calc
    (∑' a : XiZeroOccurrence, suzukiTriangleOccurrenceTerm t a) =
        ∑' ρ : XiZero, ∑' i : Fin (xiMultiplicity (ρ : ℂ)),
          suzukiTriangleOccurrenceTerm t ⟨ρ, i⟩ := hs.tsum_sigma
    _ = ∑' ρ : XiZero, (xiMultiplicity (ρ : ℂ) : ℂ) *
        suzukiTriangleXiZeroTerm t ρ := by
      apply tsum_congr
      intro ρ
      simp [suzukiTriangleOccurrenceTerm, suzukiTriangleXiZeroTerm,
        xiSpectralParameter, XiZeroOccurrence.value, tsum_fintype,
        Finset.sum_const, nsmul_eq_mul]

theorem tsum_zeta23_suzukiTriangle_eq_occurrences {t : ℝ} (ht : 0 ≤ t) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)) =
      ∑' a : XiZeroOccurrence, suzukiTriangleOccurrenceTerm t a := by
  rw [tsum_suzukiTriangleOccurrenceTerm_eq_weighted ht]
  calc
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)) =
        ∑' ρ : Zeta23.zetaZeroConfig.carrier,
          (xiMultiplicity (zeta23ZeroEquivXiZero ρ : XiZero) : ℂ) *
            suzukiTriangleXiZeroTerm t (zeta23ZeroEquivXiZero ρ) := by
      apply tsum_congr
      intro ρ
      rw [zeta23ZeroEquivXiZero_multiplicity,
        suzukiTriangleXiZeroTerm, zeta23_gammaOf_eq_neg_spectral]
    _ = ∑' ρ : XiZero, (xiMultiplicity (ρ : ℂ) : ℂ) *
          suzukiTriangleXiZeroTerm t ρ :=
      zeta23ZeroEquivXiZero.tsum_eq
        (fun ρ : XiZero ↦ (xiMultiplicity (ρ : ℂ) : ℂ) *
          suzukiTriangleXiZeroTerm t ρ)

/-- The limiting Zeta23 spectral side is exactly twice Suzuki's zero-side
function.  The factor two is the Fourier transform of the full even tent. -/
theorem tsum_zeta23_suzukiTriangle_eq_two_psi {t : ℝ} (ht : 0 ≤ t) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
          (Zeta23.gammaOf ρ)) =
      2 * suzukiPsiZero t := by
  rw [tsum_zeta23_suzukiTriangle_eq_occurrences ht,
    tsum_suzukiTriangleOccurrenceTerm_eq_two_psi ht]

/-- Zeta23's `C²_c` formula extended to the triangular test, before the
closed evaluation of the archimedean bracket.  All limiting operations—zero
sum, finite prime sum, and Gamma integral—have already been justified in
this statement. -/
theorem weilExplicitFormula_suzukiTriangle_structural
    {t : ℝ} (ht : 0 ≤ t) :
    2 * suzukiPsiZero t = suzukiTriangleLiteratureRHS t := by
  have hzero := tendsto_suzukiTriangle_zeroSide ht
  rw [tsum_zeta23_suzukiTriangle_eq_two_psi ht] at hzero
  have hrhs := tendsto_suzukiTriangle_literatureRHS ht
  have heq : (fun n : ℕ ↦ ∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
        Zeta23.paperFT (suzukiTriangleSmoothC t n) (Zeta23.gammaOf ρ)) =
      fun n : ℕ ↦ Zeta23.EF.literatureRHS (suzukiTriangleSmoothC t n) := by
    funext n
    exact (suzukiTriangleSmooth_explicitFormula ht n).2
  rw [heq] at hzero
  exact tendsto_nhds_unique hzero hrhs

/-! ## Closed archimedean evaluation: elementary pole term -/

theorem paperFT_suzukiTriangleTest_I_half {t : ℝ} (ht : 0 ≤ t) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
        (Complex.I / 2) =
      (4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) : ℝ) := by
  rw [paperFT_suzukiTriangleTest_exp ht (by simp [Complex.I_ne_zero])]
  have h₁ : Complex.I * (Complex.I / 2) * (t : ℂ) = (-(t / 2 : ℝ) : ℂ) := by
    calc
      Complex.I * (Complex.I / 2) * (t : ℂ) =
          (Complex.I * Complex.I) * ((t : ℂ) / 2) := by ring
      _ = (-(t / 2 : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  have h₂ : -Complex.I * (Complex.I / 2) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) := by
    calc
      -Complex.I * (Complex.I / 2) * (t : ℂ) =
          -(Complex.I * Complex.I) * ((t : ℂ) / 2) := by ring
      _ = ((t / 2 : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  have hden : (Complex.I * (Complex.I / 2)) ^ 2 = (1 / 4 : ℂ) := by
    rw [show Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) by
      calc
        Complex.I * (Complex.I / 2) =
            (Complex.I * Complex.I) / 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [I_mul_I]; ring]
    norm_num
  rw [h₁, h₂, hden, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_exp]
  push_cast
  ring

theorem paperFT_suzukiTriangleTest_neg_I_half {t : ℝ} (ht : 0 ≤ t) :
    Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
        (-Complex.I / 2) =
      (4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) : ℝ) := by
  rw [paperFT_suzukiTriangleTest_exp ht (by simp [Complex.I_ne_zero])]
  have h₁ : Complex.I * (-Complex.I / 2) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) := by
    calc
      Complex.I * (-Complex.I / 2) * (t : ℂ) =
          -(Complex.I * Complex.I) * ((t : ℂ) / 2) := by ring
      _ = ((t / 2 : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  have h₂ : -Complex.I * (-Complex.I / 2) * (t : ℂ) = (-(t / 2 : ℝ) : ℂ) := by
    calc
      -Complex.I * (-Complex.I / 2) * (t : ℂ) =
          (Complex.I * Complex.I) * ((t : ℂ) / 2) := by ring
      _ = (-(t / 2 : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  have hden : (Complex.I * (-Complex.I / 2)) ^ 2 = (1 / 4 : ℂ) := by
    rw [show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
      calc
        Complex.I * (-Complex.I / 2) =
            -(Complex.I * Complex.I) / 2 := by ring
        _ = (1 / 2 : ℂ) := by rw [I_mul_I]; ring]
    norm_num
  rw [h₁, h₂, hden, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_exp]
  push_cast
  ring

theorem suzukiTriangle_poleTerm_eq {t : ℝ} (ht : 0 ≤ t) :
    (1 / 2 : ℂ) *
        (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
            (Complex.I / 2) +
          Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
            (-Complex.I / 2)) =
      (4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) : ℝ) := by
  rw [paperFT_suzukiTriangleTest_I_half ht,
    paperFT_suzukiTriangleTest_neg_I_half ht]
  push_cast
  ring

/-! ### A Cauchy-kernel Fourier integral -/

private theorem integral_re_C {f : ℝ → ℂ} (hf : Integrable f) :
    ∫ x, (f x).re = (∫ x, f x).re :=
  integral_re hf

/-- Fourier inversion in Zeta23's `paperFT` convention, restricted to the
real cosine identity needed below.  This is the generic argument used in
`Zeta23.Taper.Fourier`, stated locally so importing this lemma does not pull
the umbrella `Mathlib` import of that taper module into RH Garden. -/
private theorem integral_mul_cos_of_paperFT_eq
    {A G : ℝ → ℝ} (hA : Continuous A) (hAi : Integrable A)
    (hG : Integrable G)
    (hFT : ∀ r : ℝ, Zeta23.paperFT (fun u ↦ (A u : ℂ)) r = (G r : ℂ))
    (y : ℝ) :
    ∫ r, G r * Real.cos (r * y) = 2 * Real.pi * A y := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  let Ac : ℝ → ℂ := fun u ↦ (A u : ℂ)
  have hF' : ∀ ξ : ℝ, 𝓕 Ac ξ = (G (-(2 * Real.pi) * ξ) : ℂ) := by
    intro ξ
    rw [Zeta23.fourier_eq_paperFT, ← hFT]
    congr 1
    push_cast
    ring
  have hF : 𝓕 Ac = fun ξ : ℝ ↦ (G (-(2 * Real.pi) * ξ) : ℂ) := funext hF'
  have hFi : Integrable (𝓕 Ac) := by
    rw [hF]
    exact (hG.comp_mul_left' (by linarith : -(2 * Real.pi) ≠ 0)).ofReal
  have e1 : 𝓕⁻ (𝓕 Ac) y = Ac y :=
    hAi.ofReal.fourierInv_fourier_eq hFi
      (Complex.continuous_ofReal.comp hA).continuousAt
  let g : ℝ → ℂ := fun r ↦
    (G r : ℂ) * Complex.exp ((-(y * r) : ℝ) * Complex.I)
  have hgc : Continuous fun r : ℝ ↦
      Complex.exp ((-(y * r) : ℝ) * Complex.I) := by fun_prop
  have hgi : Integrable g := by
    refine (hG.ofReal (𝕜 := ℂ)).norm.mono'
      ((hG.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
        hgc.aestronglyMeasurable)
      (Eventually.of_forall fun r ↦ ?_)
    simp only [g, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  have e2 : 𝓕⁻ (𝓕 Ac) y = ∫ ξ, g (-(2 * Real.pi) * ξ) := by
    rw [Real.fourierInv_eq_fourier_neg, Zeta23.fourier_eq_paperFT,
      Zeta23.paperFT_def]
    congr 1 with ξ
    rw [hF']
    simp only [g]
    congr 2
    push_cast
    ring
  have e3 : (∫ r, g r).re = ∫ r, G r * Real.cos (r * y) := by
    rw [← integral_re_C hgi]
    congr 1 with r
    simp only [g, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg, mul_comm y r]
  have habs : |(-(2 * Real.pi))⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_inv, abs_neg, abs_of_pos hπ]
  have e2b : (∫ ξ, g (-(2 * Real.pi) * ξ)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ r, g r := by
    have h := Measure.integral_comp_mul_left g (-(2 * Real.pi))
    rw [habs] at h
    exact h
  have e4 : A y = (2 * Real.pi)⁻¹ * ∫ r, G r * Real.cos (r * y) := by
    have h := congrArg Complex.re (e1.symm.trans (e2.trans e2b))
    rw [Complex.smul_re, smul_eq_mul, e3] at h
    simpa [Ac] using h
  rw [e4, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]

private def cauchyFourierSeed (a x : ℝ) : ℝ :=
  Real.exp (-a * |x|)

private def cauchyFourierKernel (a r : ℝ) : ℝ :=
  2 * a / (a ^ 2 + r ^ 2)

private theorem continuous_cauchyFourierSeed (a : ℝ) :
    Continuous (cauchyFourierSeed a) := by
  unfold cauchyFourierSeed
  fun_prop

private theorem integrable_cauchyFourierSeed {a : ℝ} (ha : 0 < a) :
    Integrable (cauchyFourierSeed a) := by
  have hleft : IntegrableOn (cauchyFourierSeed a) (Set.Iic 0) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Iic).mpr
      (integrableOn_exp_mul_Iic ha 0)
    intro x hx
    rw [cauchyFourierSeed, abs_of_nonpos hx]
    congr 1
    ring
  have hright : IntegrableOn (cauchyFourierSeed a) (Set.Ioi 0) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0)
    intro x hx
    rw [cauchyFourierSeed, abs_of_pos hx]
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi, integrableOn_union]
  exact ⟨hleft, hright⟩

private theorem paperFT_cauchyFourierSeed {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Zeta23.paperFT (fun x ↦ (cauchyFourierSeed a x : ℂ)) r =
      (cauchyFourierKernel a r : ℝ) := by
  let F : ℝ → ℂ := fun x ↦
    (cauchyFourierSeed a x : ℂ) *
      Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))
  let cminus : ℂ := (a : ℂ) + Complex.I * (r : ℂ)
  let cplus : ℂ := -(a : ℂ) + Complex.I * (r : ℂ)
  have hcminus : 0 < cminus.re := by simp [cminus, ha]
  have hcplus : cplus.re < 0 := by simp [cplus, ha]
  have heqminus : Set.EqOn F (fun x : ℝ ↦ Complex.exp (cminus * (x : ℂ)))
      (Set.Iic 0) := by
    intro x hx
    dsimp [F, cminus, cauchyFourierSeed]
    rw [abs_of_nonpos hx, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heqplus : Set.EqOn F (fun x : ℝ ↦ Complex.exp (cplus * (x : ℂ)))
      (Set.Ioi 0) := by
    intro x hx
    dsimp [F, cplus, cauchyFourierSeed]
    rw [abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleft : IntegrableOn F (Set.Iic 0) :=
    (integrableOn_congr_fun heqminus measurableSet_Iic).mpr
      (integrableOn_exp_mul_complex_Iic hcminus 0)
  have hright : IntegrableOn F (Set.Ioi 0) :=
    (integrableOn_congr_fun heqplus measurableSet_Ioi).mpr
      (integrableOn_exp_mul_complex_Ioi hcplus 0)
  have hcminus_ne : (a : ℂ) + Complex.I * (r : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact ha.ne' hre
  have hcplus_ne : -(a : ℂ) + Complex.I * (r : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact ha.ne' hre
  have hden_ne : (a : ℂ) ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg r)).ne'
  rw [Zeta23.paperFT_def]
  change (∫ x : ℝ, F x) = (cauchyFourierKernel a r : ℝ)
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright,
    setIntegral_congr_fun measurableSet_Iic heqminus,
    setIntegral_congr_fun measurableSet_Ioi heqplus,
    integral_exp_mul_complex_Iic hcminus 0,
    integral_exp_mul_complex_Ioi hcplus 0]
  dsimp [cminus, cplus, cauchyFourierKernel]
  simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul, neg_div]
  push_cast
  field_simp [hcminus_ne, hcplus_ne]
  ring_nf
  rw [I_sq]
  ring

private theorem integrable_cauchyFourierKernel {a : ℝ} (ha : 0 < a) :
    Integrable (cauchyFourierKernel a) := by
  have hbase := integrable_inv_one_add_sq.comp_mul_left'
    (show (a⁻¹ : ℝ) ≠ 0 by exact inv_ne_zero ha.ne')
  have hmul : Integrable (fun r : ℝ ↦
      (2 / a) * (1 + (a⁻¹ * r) ^ 2)⁻¹) := hbase.const_mul _
  convert hmul using 1
  funext r
  unfold cauchyFourierKernel
  field_simp [ha.ne']

private theorem integral_cauchyKernel_mul_cos {a t : ℝ} (ha : 0 < a) :
    (∫ r : ℝ, cauchyFourierKernel a r * Real.cos (r * t)) =
      2 * Real.pi * Real.exp (-a * |t|) := by
  exact integral_mul_cos_of_paperFT_eq
    (continuous_cauchyFourierSeed a) (integrable_cauchyFourierSeed ha)
    (integrable_cauchyFourierKernel ha) (paperFT_cauchyFourierSeed ha) t

/-- The real Fourier integral needed term-by-term in the Gamma-bracket
evaluation. -/
theorem integral_one_sub_cos_div_sq_add_sq {a t : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ r : ℝ, (1 - Real.cos (r * t)) / (r ^ 2 + a ^ 2)) =
      Real.pi / a * (1 - Real.exp (-a * t)) := by
  have hzero := integral_cauchyKernel_mul_cos (a := a) (t := 0) ha
  have ht' := integral_cauchyKernel_mul_cos (a := a) (t := t) ha
  simp only [mul_zero, Real.cos_zero, mul_one, abs_zero, Real.exp_zero] at hzero
  rw [abs_of_nonneg ht] at ht'
  have hden : ∀ r : ℝ, r ^ 2 + a ^ 2 = a ^ 2 + r ^ 2 := by
    intro r
    ring
  have hkint := integrable_cauchyFourierKernel ha
  have hcosint : Integrable (fun r : ℝ ↦
      cauchyFourierKernel a r * Real.cos (r * t)) :=
    hkint.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun r ↦ by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (r * t))
  have hdiff : Integrable (fun r : ℝ ↦
      cauchyFourierKernel a r -
        cauchyFourierKernel a r * Real.cos (r * t)) :=
    hkint.sub hcosint
  have heq : (fun r : ℝ ↦
      cauchyFourierKernel a r -
        cauchyFourierKernel a r * Real.cos (r * t)) =
      fun r : ℝ ↦ 2 * a * ((1 - Real.cos (r * t)) /
        (r ^ 2 + a ^ 2)) := by
    funext r
    unfold cauchyFourierKernel
    rw [hden]
    ring
  have hcalc : 2 * a *
      (∫ r : ℝ, (1 - Real.cos (r * t)) / (r ^ 2 + a ^ 2)) =
      2 * Real.pi * (1 - Real.exp (-a * t)) := by
    rw [← integral_const_mul]
    rw [← heq, integral_sub hkint hcosint, hzero, ht']
    ring
  have htwoa : (2 * a : ℝ) ≠ 0 := by positivity
  rw [show Real.pi / a * (1 - Real.exp (-a * t)) =
      (2 * Real.pi * (1 - Real.exp (-a * t))) / (2 * a) by
    field_simp [ha.ne']]
  apply (eq_div_iff htwoa).2
  simpa [mul_comm] using hcalc

theorem integrable_one_sub_cos_div_sq_add_sq {a t : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ ↦
      (1 - Real.cos (r * t)) / (r ^ 2 + a ^ 2)) := by
  have hkint := integrable_cauchyFourierKernel ha
  have hcosint : Integrable (fun r : ℝ ↦
      cauchyFourierKernel a r * Real.cos (r * t)) :=
    hkint.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun r ↦ by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (r * t))
  have hdiff : Integrable (fun r : ℝ ↦
      cauchyFourierKernel a r -
        cauchyFourierKernel a r * Real.cos (r * t)) :=
    hkint.sub hcosint
  have htwoa : (2 * a : ℝ) ≠ 0 := by positivity
  have hscaled := hdiff.const_mul (2 * a)⁻¹
  refine hscaled.congr (Eventually.of_forall fun r ↦ ?_)
  unfold cauchyFourierKernel
  field_simp [ha.ne', htwoa]
  ring

/-! ### Real Fourier form of the tent -/

private noncomputable def suzukiTriangleFourierReal (t r : ℝ) : ℝ :=
  (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r).re

private theorem ofReal_suzukiTriangleFourierReal {t : ℝ} (ht : 0 ≤ t)
    (r : ℝ) :
    (suzukiTriangleFourierReal t r : ℂ) =
      Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r := by
  unfold suzukiTriangleFourierReal
  rcases eq_or_ne r 0 with rfl | hr
  · norm_num
    rw [paperFT_suzukiTriangleTest_zero ht]
    apply Complex.ext <;> simp [pow_two, Complex.mul_im]
  · rw [paperFT_suzukiTriangleTest_of_ne ht (by exact_mod_cast hr)]
    have hreal :
        2 * (1 - Complex.cos ((r : ℂ) * (t : ℂ))) / (r : ℂ) ^ 2 =
          ((2 * (1 - Real.cos (r * t)) / r ^ 2 : ℝ) : ℂ) := by
      rw [show (r : ℂ) * (t : ℂ) = ((r * t : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_cos]
      push_cast
      rfl
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im hreal
      have hz : (((2 * (1 - Real.cos (r * t)) / r ^ 2 : ℝ) : ℂ)).im = 0 := by
        exact Complex.ofReal_im _
      exact (him.trans hz).symm

private theorem continuous_suzukiTriangleFourierReal {t : ℝ} (ht : 0 ≤ t) :
    Continuous (suzukiTriangleFourierReal t) := by
  exact Complex.continuous_re.comp
    ((Zeta23.WeilEF.differentiable_paperFT
      (continuous_suzukiTriangleTestC t)
      (hasCompactSupport_suzukiTriangleTestC ht)).continuous.comp
        Complex.continuous_ofReal)

private theorem integrable_suzukiTriangleFourierReal {t : ℝ} (ht : 0 ≤ t) :
    Integrable (suzukiTriangleFourierReal t) := by
  have hdom : Integrable (fun r : ℝ ↦
      (t ^ 2 + 4) * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hdom.mono' (continuous_suzukiTriangleFourierReal ht).aestronglyMeasurable
    (Eventually.of_forall fun r ↦ ?_)
  rw [Real.norm_eq_abs]
  calc
    |suzukiTriangleFourierReal t r| ≤
        ‖Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r‖ :=
      (abs_re_le_norm _)
    _ ≤ (t ^ 2 + 4) / (1 + r ^ 2) :=
      norm_paperFT_suzukiTriangleTest_le_decay ht r
    _ = (t ^ 2 + 4) * (1 + r ^ 2)⁻¹ := by
      simp [div_eq_mul_inv]

private theorem integral_suzukiTriangleFourierReal {t : ℝ} (ht : 0 ≤ t) :
    (∫ r : ℝ, suzukiTriangleFourierReal t r) = 2 * Real.pi * t := by
  have h := integral_mul_cos_of_paperFT_eq
    (continuous_suzukiTriangleTest t)
    ((continuous_suzukiTriangleTest t).integrable_of_hasCompactSupport
      (hasCompactSupport_suzukiTriangleTest ht))
    (integrable_suzukiTriangleFourierReal ht)
    (fun r ↦ (ofReal_suzukiTriangleFourierReal ht r).symm) 0
  rw [suzukiTriangleTest_zero ht] at h
  simpa using h

private theorem suzukiTriangleFourierReal_of_ne {t r : ℝ}
    (ht : 0 ≤ t) (hr : r ≠ 0) :
    suzukiTriangleFourierReal t r =
      2 * (1 - Real.cos (r * t)) / r ^ 2 := by
  have hreal := ofReal_suzukiTriangleFourierReal ht r
  rw [paperFT_suzukiTriangleTest_of_ne ht (by exact_mod_cast hr)] at hreal
  have hz :
      2 * (1 - Complex.cos ((r : ℂ) * (t : ℂ))) / (r : ℂ) ^ 2 =
        ((2 * (1 - Real.cos (r * t)) / r ^ 2 : ℝ) : ℂ) := by
    rw [show (r : ℂ) * (t : ℂ) = ((r * t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos]
    push_cast
    rfl
  rw [hz] at hreal
  exact_mod_cast hreal

/-! ### The vertical digamma excess -/

/-- The positive summand in the real-part difference
`re ψ(1/4+ir/2) - ψ(1/4)`. -/
private def suzukiDigammaExcessTerm (r : ℝ) (n : ℕ) : ℝ :=
  let q : ℝ := n + 1 / 4
  (r / 2) ^ 2 / (q * (q ^ 2 + (r / 2) ^ 2))

private theorem summable_suzukiDigammaExcessTail (r : ℝ) :
    Summable (fun n : ℕ ↦ suzukiDigammaExcessTerm r (n + 1)) := by
  have hs₁ := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (r / 2)
  have hs₀ := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  refine (hs₁.sub hs₀).congr (fun n ↦ ?_)
  simp only [suzukiDigammaExcessTerm, Nat.cast_add, Nat.cast_one]
  have hq : (0 : ℝ) < n + 1 + 1 / 4 := by positivity
  field_simp [hq.ne']
  ring

private theorem summable_suzukiDigammaExcessTerm (r : ℝ) :
    Summable (suzukiDigammaExcessTerm r) := by
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_comm] using summable_suzukiDigammaExcessTail r

/-- The pinned digamma partial-fraction series, rearranged into a manifestly
nonnegative vertical-line excess series. -/
theorem re_digamma_quarter_vertical_sub_zero (r : ℝ) :
    (Complex.digamma (1 / 4 + Complex.I * (r : ℂ) / 2)).re -
        (Complex.digamma (1 / 4 : ℂ)).re =
      ∑' n : ℕ, suzukiDigammaExcessTerm r n := by
  have h₁ := Zeta23.MuFields.re_digamma_vertical
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (r / 2)
  have h₀ := Zeta23.MuFields.re_digamma_vertical
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  have hs₁ := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (r / 2)
  have hs₀ := Zeta23.MuFields.summable_re_terms
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 0
  have htail :
      (∑' n : ℕ, suzukiDigammaExcessTerm r (n + 1)) =
        (∑' n : ℕ, (
            (1 / ((n : ℝ) + 1) -
              ((n : ℝ) + 1 + 1 / 4) /
                (((n : ℝ) + 1 + 1 / 4) ^ 2 + (r / 2) ^ 2)) -
          (1 / ((n : ℝ) + 1) -
              ((n : ℝ) + 1 + 1 / 4) /
                (((n : ℝ) + 1 + 1 / 4) ^ 2 + 0 ^ 2)))) := by
    apply tsum_congr
    intro n
    simp only [suzukiDigammaExcessTerm, Nat.cast_add, Nat.cast_one]
    have hq : (0 : ℝ) < n + 1 + 1 / 4 := by positivity
    field_simp [hq.ne']
    ring
  have hz₁ : (1 / 4 : ℂ) + Complex.I * (r : ℂ) / 2 =
      ((1 / 4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hz₀ : (1 / 4 : ℂ) =
      ((1 / 4 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ) := by
    norm_num
  rw [hz₁, hz₀, h₁, h₀]
  rw [(summable_suzukiDigammaExcessTerm r).tsum_eq_zero_add, htail,
    hs₁.tsum_sub hs₀]
  simp only [suzukiDigammaExcessTerm, Nat.cast_zero, zero_add, zero_div,
    zero_pow, OfNat.ofNat_ne_zero, div_zero, add_zero]
  field_simp
  ring

/-! ### Termwise integration of the digamma excess -/

private def suzukiGammaSeriesIntegrand (t : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  suzukiTriangleFourierReal t r * suzukiDigammaExcessTerm r n

private theorem suzukiGammaSeriesIntegrand_eq {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) (r : ℝ) :
    suzukiGammaSeriesIntegrand t n r =
      (2 / ((n : ℝ) + 1 / 4)) *
        ((1 - Real.cos (r * t)) /
          (r ^ 2 + (2 * ((n : ℝ) + 1 / 4)) ^ 2)) := by
  have hq : (0 : ℝ) < n + 1 / 4 := by positivity
  rcases eq_or_ne r 0 with rfl | hr
  · simp [suzukiGammaSeriesIntegrand, suzukiDigammaExcessTerm]
  · rw [suzukiGammaSeriesIntegrand,
      suzukiTriangleFourierReal_of_ne ht hr]
    unfold suzukiDigammaExcessTerm
    field_simp [hr, hq.ne']
    ring

private theorem integrable_suzukiGammaSeriesIntegrand {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    Integrable (suzukiGammaSeriesIntegrand t n) := by
  have hq : (0 : ℝ) < n + 1 / 4 := by positivity
  have hi := (integrable_one_sub_cos_div_sq_add_sq
    (a := 2 * ((n : ℝ) + 1 / 4)) (t := t) (by positivity)).const_mul
      (2 / ((n : ℝ) + 1 / 4))
  refine hi.congr (Eventually.of_forall fun r ↦ ?_)
  exact (suzukiGammaSeriesIntegrand_eq ht n r).symm

private theorem integral_suzukiGammaSeriesIntegrand {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    (∫ r : ℝ, suzukiGammaSeriesIntegrand t n r) =
      Real.pi / ((n : ℝ) + 1 / 4) ^ 2 *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) := by
  have hq : (0 : ℝ) < n + 1 / 4 := by positivity
  rw [show suzukiGammaSeriesIntegrand t n = fun r : ℝ ↦
      (2 / ((n : ℝ) + 1 / 4)) *
        ((1 - Real.cos (r * t)) /
          (r ^ 2 + (2 * ((n : ℝ) + 1 / 4)) ^ 2)) from
    funext (suzukiGammaSeriesIntegrand_eq ht n)]
  rw [integral_const_mul,
    integral_one_sub_cos_div_sq_add_sq (show 0 <
      2 * ((n : ℝ) + 1 / 4) by positivity) ht]
  field_simp [hq.ne']

private theorem suzukiGammaSeriesIntegrand_nonneg {t : ℝ} (ht : 0 ≤ t)
    (n : ℕ) (r : ℝ) : 0 ≤ suzukiGammaSeriesIntegrand t n r := by
  rw [suzukiGammaSeriesIntegrand_eq ht]
  have hcos : 0 ≤ 1 - Real.cos (r * t) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hq : (0 : ℝ) < n + 1 / 4 := by positivity
  positivity

private theorem integral_norm_suzukiGammaSeriesIntegrand {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    (∫ r : ℝ, ‖suzukiGammaSeriesIntegrand t n r‖) =
      Real.pi / ((n : ℝ) + 1 / 4) ^ 2 *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) := by
  rw [show (fun r : ℝ ↦ ‖suzukiGammaSeriesIntegrand t n r‖) =
      suzukiGammaSeriesIntegrand t n from funext fun r ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (suzukiGammaSeriesIntegrand_nonneg ht n r)]]
  exact integral_suzukiGammaSeriesIntegrand ht n

private theorem summable_integral_norm_suzukiGammaSeriesIntegrand {t : ℝ}
    (ht : 0 ≤ t) :
    Summable (fun n : ℕ ↦
      ∫ r : ℝ, ‖suzukiGammaSeriesIntegrand t n r‖) := by
  have hs : Summable (fun n : ℕ ↦
      Real.pi * (1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ))) :=
    ((Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le
    (fun n ↦ integral_nonneg (fun r ↦ norm_nonneg _))
    (fun n ↦ by
      rw [integral_norm_suzukiGammaSeriesIntegrand ht]
      have hq : (0 : ℝ) < n + 1 / 4 := by positivity
      have hexp : Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) ht
      rw [abs_of_pos hq]
      have hpi : 0 ≤ Real.pi / ((n : ℝ) + 1 / 4) ^ 2 := by positivity
      calc
        Real.pi / ((n : ℝ) + 1 / 4) ^ 2 *
            (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) ≤
            Real.pi / ((n : ℝ) + 1 / 4) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left
            (by nlinarith [Real.exp_pos (-2 * ((n : ℝ) + 1 / 4) * t)]) hpi
        _ = Real.pi * (1 / ((n : ℝ) + 1 / 4) ^ (2 : ℝ)) := by
          norm_num [div_eq_mul_inv])
    hs

/-! ### Quarter-lattice and Lerch sums -/

private noncomputable def suzukiModFourOneReciprocalSq (n : ℕ) : ℝ :=
  1 / ((4 * n + 1 : ℕ) : ℝ) ^ 2

private noncomputable def suzukiModFourThreeReciprocalSq (n : ℕ) : ℝ :=
  1 / ((4 * n + 3 : ℕ) : ℝ) ^ 2

private noncomputable def suzukiOddReciprocalSq (n : ℕ) : ℝ :=
  1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2

private noncomputable def suzukiEvenReciprocalSq (n : ℕ) : ℝ :=
  1 / ((2 * n : ℕ) : ℝ) ^ 2

private theorem summable_suzukiOddReciprocalSq :
    Summable suzukiOddReciprocalSq :=
  hasSum_zeta_two.summable.comp_injective (fun _ _ h ↦ by omega)

private theorem summable_suzukiEvenReciprocalSq :
    Summable suzukiEvenReciprocalSq :=
  hasSum_zeta_two.summable.comp_injective (fun _ _ h ↦ by omega)

private theorem summable_suzukiModFourOneReciprocalSq :
    Summable suzukiModFourOneReciprocalSq := by
  exact (summable_suzukiOddReciprocalSq.comp_injective
      (i := fun n : ℕ ↦ 2 * n) (by intro a b h; simp only at h; omega)).congr
    (fun n ↦ by
      simp [suzukiModFourOneReciprocalSq, suzukiOddReciprocalSq]
      push_cast
      ring)

private theorem summable_suzukiModFourThreeReciprocalSq :
    Summable suzukiModFourThreeReciprocalSq := by
  exact (summable_suzukiOddReciprocalSq.comp_injective
      (i := fun n : ℕ ↦ 2 * n + 1) (by intro a b h; simp only at h; omega)).congr
    (fun n ↦ by
      simp [suzukiModFourThreeReciprocalSq, suzukiOddReciprocalSq]
      push_cast
      ring)

private theorem tsum_suzukiOddReciprocalSq :
    (∑' n, suzukiOddReciprocalSq n) = Real.pi ^ 2 / 8 := by
  have heven : (∑' n, suzukiEvenReciprocalSq n) = Real.pi ^ 2 / 24 := by
    rw [show suzukiEvenReciprocalSq =
        fun n : ℕ ↦ (1 / 4 : ℝ) * (1 / (n : ℝ) ^ 2) by
      funext n
      simp only [suzukiEvenReciprocalSq]
      push_cast
      ring]
    rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
    ring
  have hz := tsum_even_add_odd
    (f := fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2)
    summable_suzukiEvenReciprocalSq summable_suzukiOddReciprocalSq
  have hz' :
      (∑' n, suzukiEvenReciprocalSq n) +
          (∑' n, suzukiOddReciprocalSq n) =
        ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
    simpa only [suzukiEvenReciprocalSq, suzukiOddReciprocalSq,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hz
  rw [heven, hasSum_zeta_two.tsum_eq] at hz'
  linarith

private theorem tsum_suzukiModFour_add :
    (∑' n, suzukiModFourOneReciprocalSq n) +
        (∑' n, suzukiModFourThreeReciprocalSq n) =
      Real.pi ^ 2 / 8 := by
  rw [← tsum_suzukiOddReciprocalSq]
  have hAe : Summable (fun n : ℕ ↦ suzukiOddReciprocalSq (2 * n)) :=
    summable_suzukiOddReciprocalSq.comp_injective (fun _ _ h ↦ by omega)
  have hBo : Summable (fun n : ℕ ↦ suzukiOddReciprocalSq (2 * n + 1)) :=
    summable_suzukiOddReciprocalSq.comp_injective (fun _ _ h ↦ by omega)
  have h := tsum_even_add_odd (f := suzukiOddReciprocalSq) hAe hBo
  have hAe' : (∑' n : ℕ, suzukiOddReciprocalSq (2 * n)) =
      ∑' n, suzukiModFourOneReciprocalSq n := by
    apply tsum_congr
    intro n
    simp [suzukiOddReciprocalSq, suzukiModFourOneReciprocalSq]
    push_cast
    ring
  have hBo' : (∑' n : ℕ, suzukiOddReciprocalSq (2 * n + 1)) =
      ∑' n, suzukiModFourThreeReciprocalSq n := by
    apply tsum_congr
    intro n
    simp [suzukiOddReciprocalSq, suzukiModFourThreeReciprocalSq]
    push_cast
    ring
  rwa [hAe', hBo'] at h

private theorem tsum_suzukiModFour_sub :
    (∑' n, suzukiModFourOneReciprocalSq n) -
        (∑' n, suzukiModFourThreeReciprocalSq n) =
      suzukiCatalanConstant := by
  have hAlt : Summable (fun n : ℕ ↦
      (-1 : ℝ) ^ n * suzukiOddReciprocalSq n) :=
    summable_suzukiOddReciprocalSq.alternating
  have hsplit₀ := tsum_even_add_odd
    (f := fun n : ℕ ↦ (-1 : ℝ) ^ n * suzukiOddReciprocalSq n)
    (hAlt.comp_injective (fun _ _ h ↦ by omega))
    (hAlt.comp_injective (fun _ _ h ↦ by omega))
  have heven :
      (∑' n : ℕ, (-1 : ℝ) ^ (2 * n) *
          suzukiOddReciprocalSq (2 * n)) =
        ∑' n, suzukiModFourOneReciprocalSq n := by
    apply tsum_congr
    intro n
    rw [(show Even (2 * n) by exact ⟨n, by omega⟩).neg_one_pow]
    simp only [one_mul, suzukiModFourOneReciprocalSq,
      suzukiOddReciprocalSq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    congr 3 <;> ring
  have hodd :
      (∑' n : ℕ, (-1 : ℝ) ^ (2 * n + 1) *
          suzukiOddReciprocalSq (2 * n + 1)) =
        -(∑' n, suzukiModFourThreeReciprocalSq n) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [(show Odd (2 * n + 1) by exact ⟨n, by omega⟩).neg_one_pow]
    simp only [neg_one_mul, suzukiModFourThreeReciprocalSq,
      suzukiOddReciprocalSq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    congr 3 <;> ring
  have hsplit :
      (∑' n, suzukiModFourOneReciprocalSq n) +
          -(∑' n, suzukiModFourThreeReciprocalSq n) =
        ∑' n : ℕ, (-1 : ℝ) ^ n * suzukiOddReciprocalSq n := by
    rw [heven, hodd] at hsplit₀
    exact hsplit₀
  have hdef :
      (∑' n : ℕ, (-1 : ℝ) ^ n * suzukiOddReciprocalSq n) =
        suzukiCatalanConstant := by
    unfold suzukiCatalanConstant
    apply tsum_congr
    intro n
    simp only [suzukiOddReciprocalSq, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [← hdef, ← hsplit]
  ring

/-- The quarter-lattice reciprocal-square sum, expressed using the project's
series definition of Catalan's constant. -/
theorem tsum_quarter_reciprocal_sq :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1 / 4) ^ 2) =
      Real.pi ^ 2 + 8 * suzukiCatalanConstant := by
  have hscale :
      (∑' n : ℕ, 1 / ((n : ℝ) + 1 / 4) ^ 2) =
        16 * ∑' n, suzukiModFourOneReciprocalSq n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [suzukiModFourOneReciprocalSq]
    push_cast
    field_simp
    ring
  rw [hscale]
  linarith [tsum_suzukiModFour_add, tsum_suzukiModFour_sub]

/-- The weighted quarter-lattice sum occurring after termwise integration of
the vertical digamma excess. -/
theorem tsum_quarter_reciprocal_sq_one_sub_exp {t : ℝ} (ht : 0 ≤ t) :
    (∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) =
      Real.pi ^ 2 + 8 * suzukiCatalanConstant -
        Real.exp (-t / 2) *
          suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4) := by
  let b : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1 / 4) ^ 2
  let e : ℕ → ℝ := fun n ↦ Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)
  have hb : Summable b := by
    rw [show b = fun n : ℕ ↦
        1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ) by
      funext n
      simp [b, Real.rpow_two, sq_abs]]
    exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)
  have he_nonneg (n : ℕ) : 0 ≤ e n := by positivity
  have he_le (n : ℕ) : e n ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hq : (0 : ℝ) < n + 1 / 4 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) ht
  have hbe : Summable (fun n ↦ b n * e n) :=
    Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (by positivity) (he_nonneg n))
      (fun n ↦ by
        simpa using mul_le_of_le_one_right (by positivity : 0 ≤ b n) (he_le n))
      hb
  have hweighted :
      (∑' n, b n * e n) =
        Real.exp (-t / 2) *
          suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4) := by
    unfold suzukiLerchTwo
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hexp :
        e n = Real.exp (-t / 2) * (Real.exp (-2 * t)) ^ n := by
      unfold e
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    unfold b
    ring
  calc
    (∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) =
        ∑' n, (b n - b n * e n) := by
          apply tsum_congr
          intro n
          unfold b e
          ring
    _ = (∑' n, b n) - ∑' n, b n * e n := hb.tsum_sub hbe
    _ = Real.pi ^ 2 + 8 * suzukiCatalanConstant -
        Real.exp (-t / 2) *
          suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4) := by
      rw [show (∑' n, b n) =
          Real.pi ^ 2 + 8 * suzukiCatalanConstant by
        simpa only [b] using tsum_quarter_reciprocal_sq, hweighted]

/-! ### Evaluation of the complete Gamma bracket -/

private theorem gammaBracket_eq_quarter_const_add_tsum (r : ℝ) :
    Zeta23.EF.gammaBracket r =
      ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        ∑' n : ℕ, suzukiDigammaExcessTerm r n := by
  unfold Zeta23.EF.gammaBracket
  rw [← re_digamma_quarter_vertical_sub_zero r]
  ring

private theorem tsum_suzukiGammaSeriesIntegrand (t r : ℝ) :
    (∑' n : ℕ, suzukiGammaSeriesIntegrand t n r) =
      suzukiTriangleFourierReal t r *
        (∑' n : ℕ, suzukiDigammaExcessTerm r n) := by
  unfold suzukiGammaSeriesIntegrand
  rw [tsum_mul_left]

private theorem integral_tsum_suzukiGammaSeriesIntegrand {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ r : ℝ, ∑' n : ℕ, suzukiGammaSeriesIntegrand t n r) =
      Real.pi *
        (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
          Real.exp (-t / 2) *
            suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4)) := by
  calc
    (∫ r : ℝ, ∑' n : ℕ, suzukiGammaSeriesIntegrand t n r) =
        ∑' n : ℕ, ∫ r : ℝ, suzukiGammaSeriesIntegrand t n r :=
      (integral_tsum_of_summable_integral_norm
        (fun n ↦ integrable_suzukiGammaSeriesIntegrand ht n)
        (summable_integral_norm_suzukiGammaSeriesIntegrand ht)).symm
    _ = ∑' n : ℕ, Real.pi *
        ((1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) := by
      apply tsum_congr
      intro n
      rw [integral_suzukiGammaSeriesIntegrand ht]
      ring
    _ = Real.pi * ∑' n : ℕ,
        ((1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) :=
      tsum_mul_left
    _ = Real.pi *
        (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
          Real.exp (-t / 2) *
            suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4)) := by
      rw [tsum_quarter_reciprocal_sq_one_sub_exp ht]

private theorem integrable_suzukiTriangle_gammaSide_real {t : ℝ}
    (ht : 0 ≤ t) :
    Integrable (fun r : ℝ ↦
      suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r) := by
  have h := Complex.reCLM.integrable_comp
    (integrable_suzukiTriangle_gammaSide ht)
  refine h.congr (Eventually.of_forall fun r ↦ ?_)
  change (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ)).re =
    suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r
  rw [← ofReal_suzukiTriangleFourierReal ht r]
  simp

private theorem integral_suzukiTriangle_gammaSide_real {t : ℝ}
    (ht : 0 ≤ t) :
    (∫ r : ℝ,
      suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r) =
      2 * Real.pi * t *
          ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        Real.pi *
          (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
            Real.exp (-t / 2) *
              suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4)) := by
  let B : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
  let S : ℝ → ℝ := fun r ↦
    ∑' n : ℕ, suzukiGammaSeriesIntegrand t n r
  have hconst : Integrable (fun r : ℝ ↦ B * suzukiTriangleFourierReal t r) :=
    (integrable_suzukiTriangleFourierReal ht).const_mul B
  have hwhole := integrable_suzukiTriangle_gammaSide_real ht
  have hdecomp : (fun r : ℝ ↦
      suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r) =
      fun r ↦ B * suzukiTriangleFourierReal t r + S r := by
    funext r
    unfold B S
    rw [gammaBracket_eq_quarter_const_add_tsum,
      tsum_suzukiGammaSeriesIntegrand]
    ring
  have hseries : Integrable S := by
    have hdifference := hwhole.sub hconst
    refine hdifference.congr (Eventually.of_forall fun r ↦ ?_)
    have hr := congr_fun hdecomp r
    change suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r -
      B * suzukiTriangleFourierReal t r = S r
    rw [hr]
    ring
  rw [hdecomp, integral_add hconst hseries, integral_const_mul,
    integral_suzukiTriangleFourierReal ht]
  unfold B S
  rw [integral_tsum_suzukiGammaSeriesIntegrand ht]
  ring

private theorem suzukiTriangleGammaFunctional_eq_ofReal {t : ℝ}
    (ht : 0 ≤ t) :
    suzukiTriangleGammaFunctional
        (fun u ↦ (suzukiTriangleTest t u : ℂ)) =
      ((∫ r : ℝ,
        suzukiTriangleFourierReal t r * Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
  unfold suzukiTriangleGammaFunctional
  rw [show (fun r : ℝ ↦
      Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ)) r *
        (Zeta23.EF.gammaBracket r : ℂ)) =
      fun r ↦ ((suzukiTriangleFourierReal t r *
        Zeta23.EF.gammaBracket r : ℝ) : ℂ) by
    funext r
    rw [← ofReal_suzukiTriangleFourierReal ht r]
    push_cast
    ring]
  exact Complex.ofRealCLM.integral_comp_comm
    (integrable_suzukiTriangle_gammaSide_real ht)

/-! ## The closed Gamma-bracket evaluation -/

/-- The special-function integral left after extending Zeta23's explicit
formula to the tent. This is kept as a named project proposition so the
archimedean evaluation can also be reused independently. -/
def SuzukiTriangleGammaEvaluation : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (1 / (4 * Real.pi) : ℂ) *
        suzukiTriangleGammaFunctional
          (fun u ↦ (suzukiTriangleTest t u : ℂ)) =
      ((t / 2 *
          ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        1 / 4 *
          (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
            Real.exp (-t / 2) *
              suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4)) : ℝ) : ℂ)

/-- The Gamma-bracket evaluation completing Suzuki's archimedean term. -/
theorem suzukiTriangleGammaEvaluation : SuzukiTriangleGammaEvaluation := by
  intro t ht
  rw [suzukiTriangleGammaFunctional_eq_ofReal ht,
    integral_suzukiTriangle_gammaSide_real ht]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- Once the isolated Gamma integral is evaluated, the structural triangular
explicit formula is exactly Suzuki's prime-side formula on `t ≥ 0`. -/
theorem suzukiPsi_eq_primeSideNonneg_of_gammaEvaluation
    (hGamma : SuzukiTriangleGammaEvaluation)
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsi t = suzukiPsiPrimeSideNonneg t := by
  have hstruct := weilExplicitFormula_suzukiTriangle_structural ht
  have hpole := suzukiTriangle_poleTerm_eq ht
  have hgamma := hGamma t ht
  have hprime := suzukiTrianglePrimeFunctional_test_eq_two_primeContribution ht
  have hcomplex : (suzukiPsi t : ℂ) =
      (suzukiPsiPrimeSideNonneg t : ℂ) := by
    rw [ofReal_suzukiPsi]
    calc
      suzukiPsiZero t = (1 / 2 : ℂ) * (2 * suzukiPsiZero t) := by ring
      _ = (1 / 2 : ℂ) * suzukiTriangleLiteratureRHS t := by rw [hstruct]
      _ = (1 / 2 : ℂ) *
            (Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
                (Complex.I / 2) +
              Zeta23.paperFT (fun u ↦ (suzukiTriangleTest t u : ℂ))
                (-Complex.I / 2)) -
          (1 / 2 : ℂ) *
            suzukiTrianglePrimeFunctional
              (fun u ↦ (suzukiTriangleTest t u : ℂ)) +
          (1 / (4 * Real.pi) : ℂ) *
            suzukiTriangleGammaFunctional
              (fun u ↦ (suzukiTriangleTest t u : ℂ)) := by
        unfold suzukiTriangleLiteratureRHS
        ring
      _ = ((4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) -
            suzukiPsiPrimeContribution t +
            (t / 2 *
                ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
              1 / 4 *
                (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
                  Real.exp (-t / 2) *
                    suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4))) : ℝ) : ℂ) := by
        rw [hpole, hprime, hgamma]
        push_cast
        ring
      _ = (suzukiPsiPrimeSideNonneg t : ℂ) := by
        congr 1
        unfold suzukiPsiPrimeSideNonneg suzukiPsiArchimedean
        ring
  exact_mod_cast hcomplex

/-- The exact project bridge reduces to the single Gamma-bracket evaluation
above; evenness extends the nonnegative-axis formula to all real `t`. -/
theorem suzukiPsiPrimeSideFormula_of_gammaEvaluation
    (hGamma : SuzukiTriangleGammaEvaluation) :
    SuzukiPsiPrimeSideFormula := by
  intro t
  rw [suzukiPsiPrimeSide]
  have h := suzukiPsi_eq_primeSideNonneg_of_gammaEvaluation hGamma
    (t := |t|) (abs_nonneg t)
  have habs : suzukiPsi |t| = suzukiPsi t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, suzukiPsi_neg]
  rw [← habs]
  exact h

/-- Suzuki's equation (1.1): the occurrence-indexed zero expansion of `Psi`
equals its finite-prime and archimedean expression. -/
theorem suzukiPsi_eq_primeSide (t : ℝ) :
    suzukiPsi t = suzukiPsiPrimeSide t :=
  suzukiPsiPrimeSideFormula_of_gammaEvaluation
    suzukiTriangleGammaEvaluation t

/-- The project proposition for Suzuki's prime-side formula is discharged by
the triangular-test extension of the pinned Zeta23 explicit formula. -/
theorem suzukiPsiPrimeSideFormula : SuzukiPsiPrimeSideFormula :=
  suzukiPsi_eq_primeSide

/-- Before the first prime enters the triangular cutoff, Suzuki's formula is
purely archimedean. -/
theorem suzukiPsi_eq_archimedean_of_lt_log_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    suzukiPsi t = suzukiPsiArchimedean t := by
  rw [suzukiPsi_eq_primeSide t, suzukiPsiPrimeSide,
    abs_of_nonneg ht0,
    suzukiPsiPrimeSideNonneg_eq_archimedean_of_lt_log_two ht0 ht2]

end RHGarden
