import RHGarden.SuzukiPointwise
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

noncomputable section

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace RHGarden

/-! ## Suzuki's arithmetic expression for `Psi` -/

/-- Catalan's constant in the normalization used in Suzuki (1.1). -/
noncomputable def suzukiCatalanConstant : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ 2

/-- The elementary real specialization `Phi(q,2,a)` of the Lerch
transcendent needed in Suzuki (1.1).  Defining this specialization locally
avoids introducing a second general-purpose Lerch API. -/
noncomputable def suzukiLerchTwo (q a : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ n / (n + a) ^ 2

/-- The finite von Mangoldt contribution in Suzuki's prime-side formula. -/
noncomputable def suzukiPsiPrimeContribution (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊,
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * (t - Real.log n)

/-- The non-prime part of Suzuki's formula (1.1). -/
noncomputable def suzukiPsiArchimedean (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    t / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
    1 / 4 *
      (Real.pi ^ 2 + 8 * suzukiCatalanConstant -
        Real.exp (-t / 2) *
          suzukiLerchTwo (Real.exp (-2 * t)) (1 / 4))

/-- Suzuki's prime-side expression on the nonnegative real axis. -/
noncomputable def suzukiPsiPrimeSideNonneg (t : ℝ) : ℝ :=
  suzukiPsiArchimedean t - suzukiPsiPrimeContribution t

/-- The even extension of Suzuki's prime-side expression. -/
noncomputable def suzukiPsiPrimeSide (t : ℝ) : ℝ :=
  suzukiPsiPrimeSideNonneg |t|

@[simp] theorem suzukiPsiPrimeSide_neg (t : ℝ) :
    suzukiPsiPrimeSide (-t) = suzukiPsiPrimeSide t := by
  simp [suzukiPsiPrimeSide]

/-- The exact explicit-formula bridge asserted by Suzuki (1.1). It is
discharged in `RHGarden.SuzukiTriangle` by specializing the pinned `Zeta23`
Weil explicit formula from smooth tests to the triangular cutoff. -/
def SuzukiPsiPrimeSideFormula : Prop :=
  ∀ t : ℝ, suzukiPsi t = suzukiPsiPrimeSide t

/-- Before the first prime enters the cutoff, the finite Mangoldt term
vanishes identically. -/
theorem suzukiPsiPrimeContribution_eq_zero_of_lt_log_two
    {t : ℝ} (_ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    suzukiPsiPrimeContribution t = 0 := by
  classical
  rw [suzukiPsiPrimeContribution, Finset.sum_eq_zero]
  intro n hn
  have hnmem := (Finset.mem_Ioc.mp hn)
  have hnexp : (n : ℝ) ≤ Real.exp t :=
    (Nat.cast_le.mpr hnmem.2).trans (Nat.floor_le (Real.exp_pos t).le)
  have hexp2 : Real.exp t < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_lt_exp]
    exact ht2
  have hnlt : n < 2 := by
    exact_mod_cast (hnexp.trans_lt hexp2)
  have hn1 : n = 1 := by omega
  subst n
  simp [ArithmeticFunction.vonMangoldt_apply_one]

theorem suzukiPsiPrimeContribution_nonneg (t : ℝ) :
    0 ≤ suzukiPsiPrimeContribution t := by
  classical
  apply Finset.sum_nonneg
  intro n hn
  have hnmem := Finset.mem_Ioc.mp hn
  have hnlog : Real.log n ≤ t := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast hnmem.1)).mpr
    exact (Nat.cast_le.mpr hnmem.2).trans
      (Nat.floor_le (Real.exp_pos t).le)
  exact mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (sub_nonneg.mpr hnlog)

theorem suzukiPsiPrimeSideNonneg_eq_archimedean_of_lt_log_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    suzukiPsiPrimeSideNonneg t = suzukiPsiArchimedean t := by
  rw [suzukiPsiPrimeSideNonneg,
    suzukiPsiPrimeContribution_eq_zero_of_lt_log_two ht0 ht2, sub_zero]

theorem suzukiPsi_eq_archimedean_of_lt_log_two_of_formula
    (hEF : SuzukiPsiPrimeSideFormula) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    suzukiPsi t = suzukiPsiArchimedean t := by
  rw [hEF t, suzukiPsiPrimeSide, abs_of_nonneg ht0,
    suzukiPsiPrimeSideNonneg_eq_archimedean_of_lt_log_two ht0 ht2]

/-! ## Suzuki's shifted Volterra family -/

/-- Suzuki's shift operator, equation (11.1), extended evenly in its real
argument. -/
noncomputable def SuzukiShift (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  let x := |t|
  Real.exp (-ω * x) * f x +
    2 * ω * (∫ u in (0 : ℝ)..x, Real.exp (-ω * u) * f u) +
    ω ^ 2 *
      (∫ u in (0 : ℝ)..x, (x - u) * Real.exp (-ω * u) * f u)

/-- Suzuki's shifted xi screw function `Psi_ω`. -/
noncomputable def suzukiPsiShifted (ω t : ℝ) : ℝ :=
  SuzukiShift ω suzukiPsi t

@[simp] theorem SuzukiShift_neg (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    SuzukiShift ω f (-t) = SuzukiShift ω f t := by
  simp [SuzukiShift]

@[simp] theorem SuzukiShift_zero (ω : ℝ) (f : ℝ → ℝ) :
    SuzukiShift ω f 0 = f 0 := by
  simp [SuzukiShift]

theorem SuzukiShift_zero_parameter (f : ℝ → ℝ)
    (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    SuzukiShift 0 f t = f t := by
  simp only [SuzukiShift, zero_mul, neg_zero, Real.exp_zero, one_mul,
    mul_zero, add_zero]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul, add_zero]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos (le_of_not_ge ht), heven]

@[simp] theorem suzukiPsiShifted_zero_parameter (t : ℝ) :
    suzukiPsiShifted 0 t = suzukiPsi t := by
  exact SuzukiShift_zero_parameter suzukiPsi suzukiPsi_neg t

@[simp] theorem suzukiPsiShifted_zero (ω : ℝ) :
    suzukiPsiShifted ω 0 = 0 := by
  simp [suzukiPsiShifted]

@[simp] theorem suzukiPsiShifted_even (ω t : ℝ) :
    suzukiPsiShifted ω (-t) = suzukiPsiShifted ω t := by
  simp [suzukiPsiShifted]

/-- Every coefficient and Volterra kernel in a nonnegative Suzuki shift is
nonnegative. -/
theorem SuzukiShift_nonneg_of_nonneg {η : ℝ} (hη : 0 ≤ η)
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ u → 0 ≤ f u) (t : ℝ) :
    0 ≤ SuzukiShift η f t := by
  let x : ℝ := |t|
  have hx : 0 ≤ x := abs_nonneg t
  have hfirst : 0 ≤ Real.exp (-η * x) * f x :=
    mul_nonneg (Real.exp_pos _).le (hf x hx)
  have hI₁ : 0 ≤ ∫ u in (0 : ℝ)..x, Real.exp (-η * u) * f u := by
    apply intervalIntegral.integral_nonneg hx
    intro u hu
    exact mul_nonneg (Real.exp_pos _).le (hf u hu.1)
  have hI₂ :
      0 ≤ ∫ u in (0 : ℝ)..x, (x - u) * Real.exp (-η * u) * f u := by
    apply intervalIntegral.integral_nonneg hx
    intro u hu
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hu.2) (Real.exp_pos _).le)
      (hf u hu.1)
  change 0 ≤ Real.exp (-η * x) * f x + 2 * η *
      (∫ u in (0 : ℝ)..x, Real.exp (-η * u) * f u) + η ^ 2 *
      (∫ u in (0 : ℝ)..x, (x - u) * Real.exp (-η * u) * f u)
  positivity

theorem SuzukiShift_nonneg_of_global_nonneg {η : ℝ} (hη : 0 ≤ η)
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (t : ℝ) :
    0 ≤ SuzukiShift η f t :=
  SuzukiShift_nonneg_of_nonneg hη (fun u _ => hf u) t

/-- The Volterra formula preserves continuity. -/
theorem continuous_suzukiShift (ω : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (SuzukiShift ω f) := by
  let h : ℝ → ℝ := fun u => Real.exp (-ω * u) * f u
  have hh : Continuous h := by
    dsimp [h]
    fun_prop
  have huh : Continuous (fun u : ℝ => u * h u) := by fun_prop
  let H₀ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, h u
  let H₁ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, u * h u
  have hH₀ : Continuous H₀ :=
    (intervalIntegral.differentiable_integral_of_continuous hh).continuous
  have hH₁ : Continuous H₁ :=
    (intervalIntegral.differentiable_integral_of_continuous huh).continuous
  have hvolterra :
      (fun x : ℝ => ∫ u in (0 : ℝ)..x, (x - u) * h u) =
        (fun x => x * H₀ x - H₁ x) := by
    funext x
    have hx₀ : IntervalIntegrable (fun u => x * h u) volume 0 x :=
      (continuous_const.mul hh).intervalIntegrable 0 x
    have hx₁ : IntervalIntegrable (fun u => u * h u) volume 0 x :=
      huh.intervalIntegrable 0 x
    calc
      (∫ u in (0 : ℝ)..x, (x - u) * h u) =
          ∫ u in (0 : ℝ)..x, x * h u - u * h u := by
            apply intervalIntegral.integral_congr
            intro u _
            ring
      _ = (∫ u in (0 : ℝ)..x, x * h u) -
          ∫ u in (0 : ℝ)..x, u * h u :=
            intervalIntegral.integral_sub hx₀ hx₁
      _ = x * H₀ x - H₁ x := by
            rw [intervalIntegral.integral_const_mul]
  have hV : Continuous
      (fun x : ℝ => ∫ u in (0 : ℝ)..x, (x - u) * h u) := by
    rw [hvolterra]
    fun_prop
  have hmain : Continuous (fun t : ℝ =>
    Real.exp (-ω * |t|) * f |t| +
      2 * ω * H₀ |t| + ω ^ 2 *
        (∫ u in (0 : ℝ)..|t|, (|t| - u) * h u)) := by
    fun_prop
  apply hmain.congr
  intro t
  simp only [SuzukiShift, H₀, h]
  congr 2
  apply intervalIntegral.integral_congr
  intro u _
  ring

theorem continuous_suzukiPsiShifted (ω : ℝ) :
    Continuous (suzukiPsiShifted ω) := by
  exact continuous_suzukiShift ω continuous_suzukiPsi

/-- Global pointwise positivity for one member of Suzuki's shifted family. -/
def SuzukiPsiShiftedNonnegative (ω : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t

/-- The semigroup law for the Volterra shifts.  This is isolated because its
direct proof is a two-variable Fubini calculation, independent of xi. -/
def SuzukiShiftSemigroup : Prop :=
  ∀ (ω η : ℝ) (f : ℝ → ℝ), Continuous f → ∀ t : ℝ,
    SuzukiShift (ω + η) f t = SuzukiShift η (SuzukiShift ω f) t

theorem SuzukiShift_add_zero (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    SuzukiShift (ω + 0) f t = SuzukiShift 0 (SuzukiShift ω f) t := by
  rw [add_zero, SuzukiShift_zero_parameter]
  exact SuzukiShift_neg ω f

theorem SuzukiShift_zero_add (η : ℝ) (f : ℝ → ℝ)
    (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    SuzukiShift (0 + η) f t = SuzukiShift η (SuzukiShift 0 f) t := by
  rw [zero_add]
  congr 1
  funext u
  rw [SuzukiShift_zero_parameter f heven]

theorem suzukiPsiShifted_add_of_semigroup
    (hshift : SuzukiShiftSemigroup) (ω η t : ℝ) :
    suzukiPsiShifted (ω + η) t =
      SuzukiShift η (suzukiPsiShifted ω) t := by
  exact hshift ω η suzukiPsi continuous_suzukiPsi t

theorem suzukiPsiShifted_nonnegative_of_suzukiPsiNonnegative
    {ω : ℝ} (hω : 0 ≤ ω) (hPsi : SuzukiPsiNonnegative) :
    SuzukiPsiShiftedNonnegative ω := by
  intro t
  exact SuzukiShift_nonneg_of_global_nonneg hω hPsi t

/-- Eventual pointwise positivity for one member of Suzuki's shifted family. -/
def SuzukiPsiShiftedEventuallyNonnegative (ω : ℝ) : Prop :=
  ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → 0 ≤ suzukiPsiShifted ω t

def SuzukiShiftedPositivitySet : Set ℝ :=
  {ω | SuzukiPsiShiftedNonnegative ω}

def SuzukiShiftedEventualPositivitySet : Set ℝ :=
  {ω | SuzukiPsiShiftedEventuallyNonnegative ω}

theorem suzukiShiftedPositivitySet_upper_of_semigroup
    (hshift : SuzukiShiftSemigroup) {ω η : ℝ}
    (hω : ω ∈ SuzukiShiftedPositivitySet) (hωη : ω ≤ η) :
    η ∈ SuzukiShiftedPositivitySet := by
  intro t
  let δ := η - ω
  have hδ : 0 ≤ δ := sub_nonneg.mpr hωη
  have hadd : ω + δ = η := by dsimp [δ]; ring
  rw [← hadd, suzukiPsiShifted_add_of_semigroup hshift]
  exact SuzukiShift_nonneg_of_global_nonneg hδ hω t

theorem zero_mem_suzukiShiftedPositivitySet_iff :
    0 ∈ SuzukiShiftedPositivitySet ↔ SuzukiPsiNonnegative := by
  change (∀ t : ℝ, 0 ≤ suzukiPsiShifted 0 t) ↔
    ∀ t : ℝ, 0 ≤ suzukiPsi t
  simp only [suzukiPsiShifted_zero_parameter]

theorem nonneg_mem_suzukiShiftedPositivitySet_of_suzukiPsiNonnegative
    (hPsi : SuzukiPsiNonnegative) {ω : ℝ} (hω : 0 ≤ ω) :
    ω ∈ SuzukiShiftedPositivitySet :=
  suzukiPsiShifted_nonnegative_of_suzukiPsiNonnegative hω hPsi

theorem nonneg_mem_suzukiShiftedPositivitySet_of_XiTZerosReal
    (hXi : XiTZerosReal) {ω : ℝ} (hω : 0 ≤ ω) :
    ω ∈ SuzukiShiftedPositivitySet :=
  nonneg_mem_suzukiShiftedPositivitySet_of_suzukiPsiNonnegative
    (suzukiPsi_nonnegative_of_kernelPSD
      (riemannScrewKernel_psd_of_XiTZerosReal hXi)) hω

/-- The zero-free half-plane proposition represented by Suzuki's shifted
criterion. -/
def XiZeroFreeRightOf (ω : ℝ) : Prop :=
  ∀ s : ℂ, riemannXi s = 0 → s.re ≤ 1 / 2 + ω

theorem xiZeroFreeRightOf_mono {ω η : ℝ}
    (h : XiZeroFreeRightOf ω) (hωη : ω ≤ η) : XiZeroFreeRightOf η := by
  intro s hs
  exact (h s hs).trans (by linarith)

/-- The unconditional closed half-plane containing the critical strip. -/
theorem xiZeroFreeRightOf_half : XiZeroFreeRightOf (1 / 2) := by
  intro s hs
  have hstrip := riemannXi_zero_re_mem_Ioo hs
  linarith

theorem xiRiemannHypothesis_iff_xiZeroFreeRightOf_zero :
    XiRiemannHypothesis ↔ XiZeroFreeRightOf 0 := by
  constructor
  · intro h s hs
    simpa using (h s hs).le
  · intro h s hs
    have hle : s.re ≤ 1 / 2 := by simpa using h s hs
    have hreflect : riemannXi (1 - s) = 0 := by
      rw [riemannXi_one_sub, hs]
    have hge : 1 / 2 ≤ s.re := by
      have := h (1 - s) hreflect
      simp only [Complex.sub_re, Complex.one_re] at this
      linarith
    exact le_antisymm hle hge

theorem riemannHypothesis_iff_xiZeroFreeRightOf_zero :
    RiemannHypothesis ↔ XiZeroFreeRightOf 0 :=
  riemannHypothesis_iff_xiRiemannHypothesis.trans
    xiRiemannHypothesis_iff_xiZeroFreeRightOf_zero

/-- Suzuki's equation (11.2), isolated as the remaining one-variable
Fubini/Laplace calculation for the shifted family. -/
def SuzukiShiftedTransformFormula : Prop :=
  ∀ (ω : ℝ) (z : ℂ), 1 / 2 - ω < z.im →
    (∫ t : ℝ in Set.Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      -(1 / z ^ 2) *
        logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z)

/-- The project-facing shifted version of Suzuki's Theorem 11.1. -/
def SuzukiShiftedEventualCriterion : Prop :=
  ∀ ω : ℝ,
    XiZeroFreeRightOf ω ↔ SuzukiPsiShiftedEventuallyNonnegative ω

theorem xiZeroFreeRightOf_iff_shifted_eventually_nonnegative_of_criterion
    (hcrit : SuzukiShiftedEventualCriterion) (ω : ℝ) :
    XiZeroFreeRightOf ω ↔ SuzukiPsiShiftedEventuallyNonnegative ω :=
  hcrit ω

theorem riemannHypothesis_iff_zero_mem_shiftedPositivitySet :
    RiemannHypothesis ↔ 0 ∈ SuzukiShiftedPositivitySet := by
  rw [zero_mem_suzukiShiftedPositivitySet_iff,
    riemannHypothesis_iff_XiTZerosReal]
  constructor
  · intro h
    exact suzukiPsi_nonnegative_of_kernelPSD
      (riemannScrewKernel_psd_of_XiTZerosReal h)
  · exact XiTZerosReal_of_suzukiPsi_nonneg

end RHGarden
