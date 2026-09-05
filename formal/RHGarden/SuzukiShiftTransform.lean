import RHGarden.SuzukiShifted
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology
open scoped Interval

namespace RHGarden

/-- One-sided Fourier--Laplace transform with the `exp (i z t)` convention. -/
noncomputable def FourierPlus (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, f t * Complex.exp (Complex.I * z * (t : ℂ))

noncomputable def VolterraOne (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ in (0 : ℝ)..t, h u

noncomputable def VolterraTwo (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) * h u

theorem continuous_VolterraOne {h : ℝ → ℂ} (hh : Continuous h) :
    Continuous (VolterraOne h) := by
  unfold VolterraOne
  exact (intervalIntegral.differentiable_integral_of_continuous hh).continuous

private theorem hasDerivAt_VolterraOne {h : ℝ → ℂ}
    (hh : Continuous h) (t : ℝ) :
    HasDerivAt (VolterraOne h) (h t) t := by
  unfold VolterraOne
  exact intervalIntegral.integral_hasDerivAt_right
    (hh.intervalIntegrable 0 t)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt

private theorem VolterraTwo_eq_mul_sub {h : ℝ → ℂ}
    (hh : Continuous h) (t : ℝ) :
    VolterraTwo h t = (t : ℂ) * VolterraOne h t -
      VolterraOne (fun u => (u : ℂ) * h u) t := by
  unfold VolterraTwo VolterraOne
  have h₀ : IntervalIntegrable (fun u : ℝ => (t : ℂ) * h u) volume 0 t :=
    ((continuous_const.mul hh).intervalIntegrable 0 t)
  have h₁ : IntervalIntegrable (fun u : ℝ => (u : ℂ) * h u) volume 0 t :=
    ((Complex.continuous_ofReal.mul hh).intervalIntegrable 0 t)
  calc
    (∫ u : ℝ in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) * h u) =
        ∫ u : ℝ in (0 : ℝ)..t,
          (t : ℂ) * h u - (u : ℂ) * h u := by
      apply intervalIntegral.integral_congr
      intro u _
      push_cast
      ring
    _ = (∫ u : ℝ in (0 : ℝ)..t, (t : ℂ) * h u) -
        ∫ u : ℝ in (0 : ℝ)..t, (u : ℂ) * h u :=
      intervalIntegral.integral_sub h₀ h₁
    _ = (t : ℂ) * (∫ u : ℝ in (0 : ℝ)..t, h u) -
        ∫ u : ℝ in (0 : ℝ)..t, (u : ℂ) * h u := by
      rw [intervalIntegral.integral_const_mul]

theorem VolterraOne_VolterraOne {h : ℝ → ℂ}
    (hh : Continuous h) (t : ℝ) :
    VolterraOne (VolterraOne h) t = VolterraTwo h t := by
  let H : ℝ → ℂ := VolterraOne h
  let K : ℝ → ℂ := VolterraOne (fun u => (u : ℂ) * h u)
  let V : ℝ → ℂ := fun x => (x : ℂ) * H x - K x
  have hH : ∀ x : ℝ, HasDerivAt H (h x) x := fun x =>
    hasDerivAt_VolterraOne hh x
  have hK : ∀ x : ℝ, HasDerivAt K ((x : ℂ) * h x) x := fun x =>
    hasDerivAt_VolterraOne (Complex.continuous_ofReal.mul hh) x
  have hV : ∀ x : ℝ, HasDerivAt V (H x) x := by
    intro x
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
      Complex.ofRealCLM.hasDerivAt
    have h := (hx.mul (hH x)).sub (hK x)
    apply h.congr_deriv
    ring
  have hHcont : Continuous H := continuous_VolterraOne hh
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := V) (f' := H)
    (fun x _ => hV x) (hHcont.intervalIntegrable 0 t)
  change (∫ u : ℝ in (0 : ℝ)..t, H u) = _
  rw [hftc]
  have hV0 : V 0 = 0 := by simp [V, H, K, VolterraOne]
  rw [hV0, sub_zero]
  exact (VolterraTwo_eq_mul_sub hh t).symm

noncomputable def ExponentialWeight (ω : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(ω : ℂ) * (t : ℂ)) * f t

noncomputable def VolterraAdd (ω : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t + (ω : ℂ) * VolterraOne f t

theorem continuous_ExponentialWeight (ω : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) : Continuous (ExponentialWeight ω f) := by
  exact ((Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)).mul hf)

theorem continuous_VolterraAdd (ω : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) : Continuous (VolterraAdd ω f) := by
  exact hf.add (continuous_const.mul (continuous_VolterraOne hf))

private theorem VolterraOne_add {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    VolterraOne (fun u => f u + g u) t =
      VolterraOne f t + VolterraOne g t := by
  unfold VolterraOne
  exact intervalIntegral.integral_add
    (hf.intervalIntegrable 0 t) (hg.intervalIntegrable 0 t)

private theorem VolterraOne_const_mul (c : ℂ) {f : ℝ → ℂ}
    (t : ℝ) :
    VolterraOne (fun u => c * f u) t = c * VolterraOne f t := by
  unfold VolterraOne
  exact intervalIntegral.integral_const_mul c f

private theorem VolterraAdd_comm (ω η : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (t : ℝ) :
    VolterraAdd η (VolterraAdd ω f) t =
      VolterraAdd ω (VolterraAdd η f) t := by
  unfold VolterraAdd
  have hω : VolterraOne (fun u => f u + (ω : ℂ) * VolterraOne f u) t =
      VolterraOne f t + VolterraOne (fun u => (ω : ℂ) * VolterraOne f u) t :=
    VolterraOne_add hf
      ((continuous_const : Continuous (fun _ : ℝ => (ω : ℂ))).mul
        (continuous_VolterraOne hf)) t
  have hη : VolterraOne (fun u => f u + (η : ℂ) * VolterraOne f u) t =
      VolterraOne f t + VolterraOne (fun u => (η : ℂ) * VolterraOne f u) t :=
    VolterraOne_add hf
      ((continuous_const : Continuous (fun _ : ℝ => (η : ℂ))).mul
        (continuous_VolterraOne hf)) t
  rw [hω, hη, VolterraOne_const_mul, VolterraOne_const_mul]
  ring

noncomputable def SuzukiShiftComplexPositive
    (ω : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  let h := fun u : ℝ => Complex.exp (-(ω : ℂ) * (u : ℂ)) * f u
  h t + (2 * ω : ℝ) * VolterraOne h t +
    (ω ^ 2 : ℝ) * VolterraTwo h t

private theorem SuzukiShiftComplexPositive_eq_factor
    (ω : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    SuzukiShiftComplexPositive ω f t =
      VolterraAdd ω (VolterraAdd ω (ExponentialWeight ω f)) t := by
  let h : ℝ → ℂ := ExponentialWeight ω f
  have hh : Continuous h := continuous_ExponentialWeight ω hf
  unfold SuzukiShiftComplexPositive VolterraAdd
  change h t + (2 * ω : ℝ) * VolterraOne h t +
      (ω ^ 2 : ℝ) * VolterraTwo h t =
    h t + (ω : ℂ) * VolterraOne h t +
      (ω : ℂ) * VolterraOne
        (fun u => h u + (ω : ℂ) * VolterraOne h u) t
  have hadd : VolterraOne
      (fun u => h u + (ω : ℂ) * VolterraOne h u) t =
      VolterraOne h t +
        VolterraOne (fun u => (ω : ℂ) * VolterraOne h u) t := by
    have hmul : (fun u => (ω : ℂ) * VolterraOne h u) =
        (fun _ : ℝ => (ω : ℂ)) * VolterraOne h := by
      funext u
      rfl
    rw [hmul]
    exact VolterraOne_add hh
      ((continuous_const : Continuous (fun _ : ℝ => (ω : ℂ))).mul
        (continuous_VolterraOne hh)) t
  rw [hadd,
    VolterraOne_const_mul,
    VolterraOne_VolterraOne hh]
  push_cast
  ring

private theorem exponentialWeight_volterra_resolvent
    (η : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    ExponentialWeight η (VolterraOne f) t +
        (η : ℂ) * VolterraOne (ExponentialWeight η (VolterraOne f)) t =
      VolterraOne (ExponentialWeight η f) t := by
  let H : ℝ → ℂ := VolterraOne f
  let P : ℝ → ℂ := ExponentialWeight η H
  have hH : Continuous H := continuous_VolterraOne hf
  have hP : Continuous P := continuous_ExponentialWeight η hH
  have hderiv : ∀ x : ℝ, HasDerivAt P
      (ExponentialWeight η f x -
        (η : ℂ) * ExponentialWeight η H x) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => -(η : ℂ) * (y : ℂ)) (-(η : ℂ)) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul (-(η : ℂ)))
    have hexp : HasDerivAt
        (fun y : ℝ => Complex.exp (-(η : ℂ) * (y : ℂ)))
        (-(η : ℂ) * Complex.exp (-(η : ℂ) * (x : ℂ))) x := by
      simpa [mul_comm] using hlin.cexp
    have hmul := hexp.mul (hasDerivAt_VolterraOne hf x)
    apply hmul.congr_deriv
    simp only [H, ExponentialWeight]
    ring
  have hsub : Continuous (fun x => ExponentialWeight η f x -
      (η : ℂ) * ExponentialWeight η H x) :=
    (continuous_ExponentialWeight η hf).sub
      ((continuous_const : Continuous (fun _ : ℝ => (η : ℂ))).mul hP)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := P)
    (f' := fun x => ExponentialWeight η f x -
      (η : ℂ) * ExponentialWeight η H x)
    (fun x _ => hderiv x)
    (hsub.intervalIntegrable 0 t)
  have hP0 : P 0 = 0 := by simp [P, H, ExponentialWeight, VolterraOne]
  have hsplit :
      (∫ x in (0 : ℝ)..t, ExponentialWeight η f x -
          (η : ℂ) * ExponentialWeight η H x) =
        VolterraOne (ExponentialWeight η f) t -
          (η : ℂ) * VolterraOne (ExponentialWeight η H) t := by
    have hconst : Continuous (fun x =>
        (η : ℂ) * ExponentialWeight η H x) :=
      (continuous_const : Continuous (fun _ : ℝ => (η : ℂ))).mul hP
    rw [intervalIntegral.integral_sub
      ((continuous_ExponentialWeight η hf).intervalIntegrable 0 t)
      (hconst.intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul]
    rfl
  rw [hftc, hP0, sub_zero] at hsplit
  dsimp only [P, H] at hsplit ⊢
  rw [hsplit]
  ring

private theorem VolterraAdd_exponentialWeight_VolterraAdd
    (η ω : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    VolterraAdd η (ExponentialWeight η (VolterraAdd ω f)) =
      VolterraAdd (ω + η) (ExponentialWeight η f) := by
  funext t
  let h₀ : ℝ → ℂ := ExponentialWeight η f
  let h₁ : ℝ → ℂ := ExponentialWeight η (VolterraOne f)
  have hh₀ : Continuous h₀ := continuous_ExponentialWeight η hf
  have hh₁ : Continuous h₁ := continuous_ExponentialWeight η
    (continuous_VolterraOne hf)
  have hweight : ExponentialWeight η (VolterraAdd ω f) =
      fun u => h₀ u + (ω : ℂ) * h₁ u := by
    funext u
    simp only [ExponentialWeight, VolterraAdd, h₀, h₁]
    ring
  rw [hweight]
  unfold VolterraAdd
  have hadd : VolterraOne (fun u => h₀ u + (ω : ℂ) * h₁ u) t =
      VolterraOne h₀ t + VolterraOne (fun u => (ω : ℂ) * h₁ u) t := by
    exact VolterraOne_add hh₀
      ((continuous_const : Continuous (fun _ : ℝ => (ω : ℂ))).mul hh₁) t
  rw [hadd, VolterraOne_const_mul]
  change h₀ t + (ω : ℂ) * h₁ t +
      (η : ℂ) * (VolterraOne h₀ t +
        (ω : ℂ) * VolterraOne h₁ t) =
    h₀ t + ((ω + η : ℝ) : ℂ) * VolterraOne h₀ t
  have hres := exponentialWeight_volterra_resolvent η hf t
  change h₁ t + (η : ℂ) * VolterraOne h₁ t =
    VolterraOne h₀ t at hres
  rw [← hres]
  push_cast
  ring

private theorem ExponentialWeight_comp (η ω : ℝ) (f : ℝ → ℂ) :
    ExponentialWeight η (ExponentialWeight ω f) =
      ExponentialWeight (ω + η) f := by
  funext t
  unfold ExponentialWeight
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem SuzukiShiftComplexPositive_factor
    (ω : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    SuzukiShiftComplexPositive ω f =
      VolterraAdd ω (VolterraAdd ω (ExponentialWeight ω f)) := by
  funext t
  exact SuzukiShiftComplexPositive_eq_factor ω hf t

private theorem continuous_SuzukiShiftComplexPositive
    (ω : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (SuzukiShiftComplexPositive ω f) := by
  rw [SuzukiShiftComplexPositive_factor ω hf]
  exact continuous_VolterraAdd ω
    (continuous_VolterraAdd ω
      (continuous_ExponentialWeight ω hf))

private theorem VolterraAdd_comm_fun (ω η : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) :
    VolterraAdd η (VolterraAdd ω f) =
      VolterraAdd ω (VolterraAdd η f) := by
  funext t
  exact VolterraAdd_comm ω η hf t

theorem SuzukiShiftComplexPositive_semigroup
    (ω η : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    SuzukiShiftComplexPositive η (SuzukiShiftComplexPositive ω f) =
      SuzukiShiftComplexPositive (ω + η) f := by
  rw [SuzukiShiftComplexPositive_factor η
      (continuous_SuzukiShiftComplexPositive ω hf),
    SuzukiShiftComplexPositive_factor ω hf,
    VolterraAdd_exponentialWeight_VolterraAdd η ω
      (continuous_VolterraAdd ω
        (continuous_ExponentialWeight ω hf)),
    VolterraAdd_comm_fun (ω + η) η
      (continuous_ExponentialWeight η
        (continuous_VolterraAdd ω
          (continuous_ExponentialWeight ω hf))),
    VolterraAdd_exponentialWeight_VolterraAdd η ω
      (continuous_ExponentialWeight ω hf),
    ExponentialWeight_comp η ω f,
    ← SuzukiShiftComplexPositive_factor (ω + η) hf]

private theorem coe_SuzukiShift_of_nonneg
    (ω : ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (SuzukiShift ω f t : ℂ) =
      SuzukiShiftComplexPositive ω (fun u => (f u : ℂ)) t := by
  unfold SuzukiShift SuzukiShiftComplexPositive VolterraOne VolterraTwo
  rw [abs_of_nonneg ht]
  push_cast
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal]
  have h₁ :
      (∫ u : ℝ in (0 : ℝ)..t,
        ((Real.exp (-ω * u) * f u : ℝ) : ℂ)) =
      ∫ u : ℝ in (0 : ℝ)..t,
        Complex.exp (-(ω : ℂ) * (u : ℂ)) * (f u : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u _
    push_cast
    rfl
  have h₂ :
      (∫ u : ℝ in (0 : ℝ)..t,
        (((t - u) * Real.exp (-ω * u) * f u : ℝ) : ℂ)) =
      ∫ u : ℝ in (0 : ℝ)..t,
        ((t - u : ℝ) : ℂ) *
          (Complex.exp (-(ω : ℂ) * (u : ℂ)) * (f u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u _
    push_cast
    rw [show -(ω : ℂ) * (u : ℂ) = -((u : ℂ) * (ω : ℂ)) by ring]
    ring
  rw [h₁, h₂]
  push_cast
  rfl

private theorem coe_SuzukiShift
    (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    (SuzukiShift ω f t : ℂ) =
      SuzukiShiftComplexPositive ω (fun u => (f u : ℂ)) |t| := by
  calc
    (SuzukiShift ω f t : ℂ) = (SuzukiShift ω f |t| : ℂ) := by
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · have ht' : t < 0 := lt_of_not_ge ht
        rw [abs_of_neg ht', ← SuzukiShift_neg]
    _ = _ := coe_SuzukiShift_of_nonneg ω f (abs_nonneg t)

private theorem SuzukiShiftComplexPositive_congr_Icc
    (ω : ℝ) {f g : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hfg : ∀ u ∈ Icc (0 : ℝ) t, f u = g u) :
    SuzukiShiftComplexPositive ω f t =
      SuzukiShiftComplexPositive ω g t := by
  have hft : f t = g t := hfg t ⟨ht, le_rfl⟩
  simp only [SuzukiShiftComplexPositive]
  unfold VolterraOne VolterraTwo
  have h₁ :
      (∫ u in (0 : ℝ)..t,
        Complex.exp (-(ω : ℂ) * (u : ℂ)) * f u) =
      ∫ u in (0 : ℝ)..t,
        Complex.exp (-(ω : ℂ) * (u : ℂ)) * g u := by
    apply intervalIntegral.integral_congr
    intro u hu
    change Complex.exp (-(ω : ℂ) * (u : ℂ)) * f u = _
    have hu' : u ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le ht] using hu
    rw [hfg u hu']
  have h₂ :
      (∫ u in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) *
        (Complex.exp (-(ω : ℂ) * (u : ℂ)) * f u)) =
      ∫ u in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) *
        (Complex.exp (-(ω : ℂ) * (u : ℂ)) * g u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le ht] using hu
    change ((t - u : ℝ) : ℂ) *
      (Complex.exp (-(ω : ℂ) * (u : ℂ)) * f u) = _
    rw [hfg u hu']
  rw [hft, h₁, h₂]

theorem suzukiShift_semigroup
    (ω η : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    SuzukiShift (ω + η) f t =
      SuzukiShift η (SuzukiShift ω f) t := by
  let F : ℝ → ℂ := fun u => (f u : ℂ)
  let x : ℝ := |t|
  have hx : 0 ≤ x := abs_nonneg t
  have hF : Continuous F := Complex.continuous_ofReal.comp hf
  apply Complex.ofReal_injective
  rw [coe_SuzukiShift (ω + η) f t,
    coe_SuzukiShift η (SuzukiShift ω f) t]
  change SuzukiShiftComplexPositive (ω + η) F x =
    SuzukiShiftComplexPositive η
      (fun u => (SuzukiShift ω f u : ℂ)) x
  rw [← SuzukiShiftComplexPositive_semigroup ω η hF]
  apply SuzukiShiftComplexPositive_congr_Icc η hx
  intro u hu
  rw [coe_SuzukiShift_of_nonneg ω f hu.1]

theorem suzukiShiftSemigroup : SuzukiShiftSemigroup := by
  intro ω η f hf t
  exact suzukiShift_semigroup ω η f hf t

theorem suzukiPsiShifted_add (ω η t : ℝ) :
    suzukiPsiShifted (ω + η) t =
      SuzukiShift η (suzukiPsiShifted ω) t :=
  suzukiPsiShifted_add_of_semigroup suzukiShiftSemigroup ω η t

theorem suzukiPsiShifted_nonneg_of_nonneg_add
    {ω η : ℝ} (hη : 0 ≤ η)
    (h : ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t) :
    ∀ t : ℝ, 0 ≤ suzukiPsiShifted (ω + η) t := by
  intro t
  rw [suzukiPsiShifted_add]
  exact SuzukiShift_nonneg_of_global_nonneg hη h t

theorem suzukiShiftedPositivitySet_upper
    {ω η : ℝ} (hω : ω ∈ SuzukiShiftedPositivitySet) (hωη : ω ≤ η) :
    η ∈ SuzukiShiftedPositivitySet :=
  suzukiShiftedPositivitySet_upper_of_semigroup
    suzukiShiftSemigroup hω hωη

/-- Multiplication by a real exponential weight translates the one-sided
Fourier--Laplace frequency. -/
theorem FourierPlus_exp_neg_mul (ω : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    FourierPlus
        (fun t : ℝ => Complex.exp (-(ω : ℂ) * (t : ℂ)) * f t) z =
      FourierPlus f (z + Complex.I * (ω : ℂ)) := by
  unfold FourierPlus
  apply integral_congr_ae
  filter_upwards with t
  have he : Complex.exp (-(ω : ℂ) * (t : ℂ)) *
      Complex.exp (Complex.I * z * (t : ℂ)) =
      Complex.exp (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  rw [← he]
  ring

theorem integral_volterraOne_exp
    {h : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0)) :
    (∫ t : ℝ in Ioi 0,
        (∫ u : ℝ in (0 : ℝ)..t, h u) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      (Complex.I / z) *
        ∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hza : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
  have hexp : IntegrableOn (fun x : ℝ => Complex.exp (a * (x : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hconv := integral_posConvolution hh hexp (ContinuousLinearMap.mul ℝ ℂ)
  calc
    (∫ t : ℝ in Ioi 0,
        (∫ u : ℝ in (0 : ℝ)..t, h u) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          ∫ u : ℝ in (0 : ℝ)..t,
            (ContinuousLinearMap.mul ℝ ℂ)
              (h u * Complex.exp (a * (u : ℂ)))
              (Complex.exp (a * ((t - u : ℝ) : ℂ))) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [← intervalIntegral.integral_mul_const]
        apply intervalIntegral.integral_congr
        intro u _
        change h u * Complex.exp (Complex.I * z * (t : ℂ)) =
          (h u * Complex.exp (a * (u : ℂ))) *
            Complex.exp (a * ((t - u : ℝ) : ℂ))
        have he : Complex.exp (a * (u : ℂ)) *
            Complex.exp (a * ((t - u : ℝ) : ℂ)) =
            Complex.exp (Complex.I * z * (t : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          dsimp [a]
          push_cast
          ring
        rw [← he]
        ring
    _ = (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (a * (t : ℂ))) *
        (∫ t : ℝ in Ioi 0, Complex.exp (a * (t : ℂ))) := hconv
    _ = (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (a * (t : ℂ))) * (-1 / a) := by
        rw [integral_exp_mul_complex_Ioi ha]
        simp
    _ = (Complex.I / z) *
        ∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
        dsimp [a]
        field_simp
        rw [Complex.I_sq]
        simp

private theorem integrableOn_volterraOne_exp
    {h : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0)) :
    IntegrableOn
      (fun t : ℝ => VolterraOne h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hexp : IntegrableOn (fun x : ℝ => Complex.exp (a * (x : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hp : IntegrableOn
      (MeasureTheory.posConvolution
        (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
        (fun x : ℝ => Complex.exp (a * (x : ℂ)))
        (ContinuousLinearMap.mul ℝ ℂ)) (Ioi 0) :=
    (integrable_posConvolution hh hexp
      (ContinuousLinearMap.mul ℝ ℂ)).integrableOn
  change Integrable _ (volume.restrict (Ioi 0))
  apply hp.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [MeasureTheory.posConvolution, indicator_of_mem ht]
  unfold VolterraOne
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro u _
  change (h u * Complex.exp (Complex.I * z * (u : ℂ))) *
      Complex.exp (a * ((t - u : ℝ) : ℂ)) =
    h u * Complex.exp (Complex.I * z * (t : ℂ))
  have he : Complex.exp (a * (u : ℂ)) *
      Complex.exp (a * ((t - u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [a]
    push_cast
    ring
  rw [← he]
  ring

private theorem integrableOn_id_mul_cexp {a : ℂ} (ha : a.re < 0) :
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
      (fun x : ℝ => (y * x) * Real.exp (-(y * x))) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
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
      (volume.restrict (Ioi 0)) := by
    exact ((Complex.continuous_ofReal.mul
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

private theorem tendsto_id_mul_cexp {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ))) atTop (nhds 0) := by
  let y : ℝ := -a.re
  have hy : 0 < y := by dsimp [y]; linarith
  have hscale : Tendsto (fun x : ℝ => y * x) atTop atTop :=
    tendsto_id.const_mul_atTop hy
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hreal : Tendsto (fun x : ℝ => x * Real.exp (-y * x)) atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ => 1 / y) atTop (nhds (1 / y)) :=
      tendsto_const_nhds
    have hmul := hc.mul hbase
    have hmul' : Tendsto
        (fun x => 1 / y * ((y * x) ^ 1 * Real.exp (-(y * x))))
        atTop (nhds 0) := by simpa only [Function.comp_apply, mul_zero] using hmul
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

private theorem integral_id_mul_cexp {a : ℂ} (ha : a.re < 0) :
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
  have hlimexp : Tendsto (fun x : ℝ => Complex.exp (a * (x : ℂ))) atTop (nhds 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have hmul : Tendsto (fun x : ℝ => a.re * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg ha
    apply hmul.congr'
    filter_upwards with x
    simp [Complex.mul_re]
  have hlim : Tendsto F atTop (nhds 0) := by
    have hid := tendsto_id_mul_cexp ha
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
    (fun x _ => hderiv x) (integrableOn_id_mul_cexp ha) hlim]
  dsimp [F]
  field_simp [ha0]
  norm_num

theorem integral_volterraTwo_exp
    {h : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0)) :
    (∫ t : ℝ in Ioi 0,
        (∫ u : ℝ in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) * h u) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      -(1 / z ^ 2) *
        ∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hza : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
  have hg : IntegrableOn
      (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ))) (Ioi 0) :=
    integrableOn_id_mul_cexp ha
  have hconv := integral_posConvolution hh hg (ContinuousLinearMap.mul ℝ ℂ)
  calc
    (∫ t : ℝ in Ioi 0,
        (∫ u : ℝ in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) * h u) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          ∫ u : ℝ in (0 : ℝ)..t,
            (ContinuousLinearMap.mul ℝ ℂ)
              (h u * Complex.exp (a * (u : ℂ)))
              (((t - u : ℝ) : ℂ) *
                Complex.exp (a * ((t - u : ℝ) : ℂ))) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [← intervalIntegral.integral_mul_const]
        apply intervalIntegral.integral_congr
        intro u _
        change (((t - u : ℝ) : ℂ) * h u) *
            Complex.exp (Complex.I * z * (t : ℂ)) =
          (h u * Complex.exp (a * (u : ℂ))) *
            (((t - u : ℝ) : ℂ) *
              Complex.exp (a * ((t - u : ℝ) : ℂ)))
        have he : Complex.exp (a * (u : ℂ)) *
            Complex.exp (a * ((t - u : ℝ) : ℂ)) =
            Complex.exp (Complex.I * z * (t : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          dsimp [a]
          push_cast
          ring
        rw [← he]
        ring
    _ = (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (a * (t : ℂ))) *
        (∫ t : ℝ in Ioi 0,
          (t : ℂ) * Complex.exp (a * (t : ℂ))) := hconv
    _ = (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (a * (t : ℂ))) * (1 / a ^ 2) := by
        rw [integral_id_mul_cexp ha]
    _ = -(1 / z ^ 2) *
        ∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
        dsimp [a]
        rw [mul_pow, Complex.I_sq]
        field_simp

private theorem integrableOn_volterraTwo_exp
    {h : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0)) :
    IntegrableOn
      (fun t : ℝ => VolterraTwo h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  let a : ℂ := Complex.I * z
  have ha : a.re < 0 := by
    dsimp [a]
    simpa [Complex.mul_re] using neg_lt_zero.mpr hz
  have hg : IntegrableOn
      (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ))) (Ioi 0) :=
    integrableOn_id_mul_cexp ha
  have hp : IntegrableOn
      (MeasureTheory.posConvolution
        (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
        (fun x : ℝ => (x : ℂ) * Complex.exp (a * (x : ℂ)))
        (ContinuousLinearMap.mul ℝ ℂ)) (Ioi 0) :=
    (integrable_posConvolution hh hg
      (ContinuousLinearMap.mul ℝ ℂ)).integrableOn
  change Integrable _ (volume.restrict (Ioi 0))
  apply hp.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [MeasureTheory.posConvolution, indicator_of_mem ht]
  unfold VolterraTwo
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro u _
  change (h u * Complex.exp (Complex.I * z * (u : ℂ))) *
      (((t - u : ℝ) : ℂ) * Complex.exp (a * ((t - u : ℝ) : ℂ))) =
    (((t - u : ℝ) : ℂ) * h u) *
      Complex.exp (Complex.I * z * (t : ℂ))
  have he : Complex.exp (a * (u : ℂ)) *
      Complex.exp (a * ((t - u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [a]
    push_cast
    ring
  rw [← he]
  ring

theorem integral_SuzukiShiftComplexPositive_exp
    {ω : ℝ} {f : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hf : IntegrableOn
      (fun t : ℝ => f t * Complex.exp
        (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)))
      (Ioi 0)) :
    FourierPlus (SuzukiShiftComplexPositive ω f) z =
      ((z + Complex.I * (ω : ℂ)) ^ 2 / z ^ 2) *
        FourierPlus f (z + Complex.I * (ω : ℂ)) := by
  let h : ℝ → ℂ := fun t => Complex.exp (-(ω : ℂ) * (t : ℂ)) * f t
  have hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0) := by
    apply hf.congr
    filter_upwards with t
    dsimp [h]
    have he : Complex.exp (-(ω : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * z * (t : ℂ)) =
        Complex.exp
          (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [← he]
    ring
  have hV₁ := integrableOn_volterraOne_exp hz hh
  have hV₂ := integrableOn_volterraTwo_exp hz hh
  have h₁ : IntegrableOn
      (fun t : ℝ => ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    have hmul := hV₁.const_mul (((2 * ω : ℝ) : ℂ))
    apply hmul.congr
    filter_upwards with t
    ring
  have h₂ : IntegrableOn
      (fun t : ℝ => ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    have hmul := hV₂.const_mul (((ω ^ 2 : ℝ) : ℂ))
    apply hmul.congr
    filter_upwards with t
    ring
  have hshift : FourierPlus h z =
      FourierPlus f (z + Complex.I * (ω : ℂ)) :=
    FourierPlus_exp_neg_mul ω f z
  have hvol₁ := integral_volterraOne_exp hz hh
  have hvol₂ := integral_volterraTwo_exp hz hh
  have hvol₁' :
      (∫ t : ℝ in Ioi 0,
        VolterraOne h t * Complex.exp (Complex.I * z * (t : ℂ))) =
        (Complex.I / z) *
          ∫ t : ℝ in Ioi 0,
            h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
    simpa only [VolterraOne] using hvol₁
  have hvol₂' :
      (∫ t : ℝ in Ioi 0,
        VolterraTwo h t * Complex.exp (Complex.I * z * (t : ℂ))) =
        -(1 / z ^ 2) *
          ∫ t : ℝ in Ioi 0,
            h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
    simpa only [VolterraTwo] using hvol₂
  unfold FourierPlus at hshift hvol₁ hvol₂ ⊢
  rw [show SuzukiShiftComplexPositive ω f = fun t =>
      h t + ((2 * ω : ℝ) : ℂ) * VolterraOne h t +
        ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t by rfl]
  simp_rw [add_mul]
  change (∫ t : ℝ in Ioi 0,
      (h t * Complex.exp (Complex.I * z * (t : ℂ)) +
        ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
          Complex.exp (Complex.I * z * (t : ℂ))) +
        ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
          Complex.exp (Complex.I * z * (t : ℂ))) = _
  have hadd₁ :
      (∫ t : ℝ in Ioi 0,
        h t * Complex.exp (Complex.I * z * (t : ℂ)) +
          ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
            Complex.exp (Complex.I * z * (t : ℂ))) =
        (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ))) +
        ∫ t : ℝ in Ioi 0,
          ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
            Complex.exp (Complex.I * z * (t : ℂ)) :=
    integral_add hh h₁
  have hadd₂ :
      (∫ t : ℝ in Ioi 0,
        (h t * Complex.exp (Complex.I * z * (t : ℂ)) +
          ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
            Complex.exp (Complex.I * z * (t : ℂ))) +
          ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
            Complex.exp (Complex.I * z * (t : ℂ))) =
        (∫ t : ℝ in Ioi 0,
          h t * Complex.exp (Complex.I * z * (t : ℂ)) +
            ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
              Complex.exp (Complex.I * z * (t : ℂ))) +
        ∫ t : ℝ in Ioi 0,
          ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
            Complex.exp (Complex.I * z * (t : ℂ)) :=
    integral_add (hh.add h₁) h₂
  have hconst₁ :
      (∫ t : ℝ in Ioi 0,
        ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ((2 * ω : ℝ) : ℂ) *
          ∫ t : ℝ in Ioi 0,
            VolterraOne h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
    rw [show (fun t : ℝ => ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      (fun t : ℝ => ((2 * ω : ℝ) : ℂ) *
        (VolterraOne h t * Complex.exp (Complex.I * z * (t : ℂ)))) by
      funext t; ring]
    exact integral_const_mul _ _
  have hconst₂ :
      (∫ t : ℝ in Ioi 0,
        ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ((ω ^ 2 : ℝ) : ℂ) *
          ∫ t : ℝ in Ioi 0,
            VolterraTwo h t * Complex.exp (Complex.I * z * (t : ℂ)) := by
    rw [show (fun t : ℝ => ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
        Complex.exp (Complex.I * z * (t : ℂ))) =
      (fun t : ℝ => ((ω ^ 2 : ℝ) : ℂ) *
        (VolterraTwo h t * Complex.exp (Complex.I * z * (t : ℂ)))) by
      funext t; ring]
    exact integral_const_mul _ _
  rw [hadd₂, hadd₁]
  rw [hconst₁, hconst₂, hvol₁', hvol₂', hshift]
  let L : ℂ := ∫ t : ℝ in Ioi 0,
    f t * Complex.exp (Complex.I *
      (z + Complex.I * (ω : ℂ)) * (t : ℂ))
  change (L + ((2 * ω : ℝ) : ℂ) * (Complex.I / z * L)) +
      ((ω ^ 2 : ℝ) : ℂ) * (-(1 / z ^ 2) * L) =
    ((z + Complex.I * (ω : ℂ)) ^ 2 / z ^ 2) * L
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
  have hsquare : (z + Complex.I * (ω : ℂ)) ^ 2 =
      z ^ 2 + 2 * Complex.I * (ω : ℂ) * z - (ω : ℂ) ^ 2 := by
    calc
      (z + Complex.I * (ω : ℂ)) ^ 2 =
          z ^ 2 + 2 * Complex.I * (ω : ℂ) * z +
            (Complex.I * Complex.I) * ((ω : ℂ) ^ 2) := by ring
      _ = z ^ 2 + 2 * Complex.I * (ω : ℂ) * z - (ω : ℂ) ^ 2 := by
        rw [Complex.I_mul_I]
        ring
  rw [hsquare]
  field_simp [hz0]
  push_cast
  ring

private theorem integrableOn_SuzukiShiftComplexPositive_exp
    {ω : ℝ} {f : ℝ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hf : IntegrableOn
      (fun t : ℝ => f t * Complex.exp
        (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)))
      (Ioi 0)) :
    IntegrableOn
      (fun t : ℝ => SuzukiShiftComplexPositive ω f t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  let h : ℝ → ℂ := fun t =>
    Complex.exp (-(ω : ℂ) * (t : ℂ)) * f t
  have hh : IntegrableOn
      (fun t : ℝ => h t * Complex.exp (Complex.I * z * (t : ℂ)))
      (Ioi 0) := by
    apply hf.congr
    filter_upwards with t
    dsimp [h]
    have he : Complex.exp (-(ω : ℂ) * (t : ℂ)) *
        Complex.exp (Complex.I * z * (t : ℂ)) =
      Complex.exp
        (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [← he]
    ring
  have hV₁ := integrableOn_volterraOne_exp hz hh
  have hV₂ := integrableOn_volterraTwo_exp hz hh
  have h₁ : IntegrableOn
      (fun t : ℝ => ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    exact (hV₁.const_mul (((2 * ω : ℝ) : ℂ))).congr
      (by filter_upwards with t; ring)
  have h₂ : IntegrableOn
      (fun t : ℝ => ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
    change Integrable _ (volume.restrict (Ioi 0))
    exact (hV₂.const_mul (((ω ^ 2 : ℝ) : ℂ))).congr
      (by filter_upwards with t; ring)
  have hsum := (hh.add h₁).add h₂
  apply hsum.congr
  filter_upwards with t
  change (h t * Complex.exp (Complex.I * z * (t : ℂ)) +
      ((2 * ω : ℝ) : ℂ) * VolterraOne h t *
        Complex.exp (Complex.I * z * (t : ℂ))) +
      ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t *
        Complex.exp (Complex.I * z * (t : ℂ)) = _
  rw [show SuzukiShiftComplexPositive ω f t =
      h t + ((2 * ω : ℝ) : ℂ) * VolterraOne h t +
        ((ω ^ 2 : ℝ) : ℂ) * VolterraTwo h t by rfl]
  ring

/-- Generic one-sided Fourier--Laplace transform of Suzuki's real shift. -/
theorem integral_SuzukiShift_exp
    {ω : ℝ} {f : ℝ → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hf : IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp
        (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)))
      (Ioi 0)) :
    FourierPlus (fun t => (SuzukiShift ω f t : ℂ)) z =
      ((z + Complex.I * (ω : ℂ)) ^ 2 / z ^ 2) *
        FourierPlus (fun t => (f t : ℂ))
          (z + Complex.I * (ω : ℂ)) := by
  have hcoe : FourierPlus (fun t => (SuzukiShift ω f t : ℂ)) z =
      FourierPlus (SuzukiShiftComplexPositive ω (fun t => (f t : ℂ))) z := by
    unfold FourierPlus
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [coe_SuzukiShift_of_nonneg ω f (le_of_lt ht)]
  rw [hcoe]
  exact integral_SuzukiShiftComplexPositive_exp hz hf

theorem integrableOn_SuzukiShift_exp
    {ω : ℝ} {f : ℝ → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hf : IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp
        (Complex.I * (z + Complex.I * (ω : ℂ)) * (t : ℂ)))
      (Ioi 0)) :
    IntegrableOn
      (fun t : ℝ => (SuzukiShift ω f t : ℂ) *
        Complex.exp (Complex.I * z * (t : ℂ))) (Ioi 0) := by
  have hc := integrableOn_SuzukiShiftComplexPositive_exp
    (ω := ω) (f := fun t => (f t : ℂ)) (z := z) hz hf
  apply hc.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [coe_SuzukiShift_of_nonneg ω f (le_of_lt ht)]

/-- Applying two shifts multiplies the one-sided transform multipliers and
cancels the intermediate frequency factor. -/
theorem FourierPlus_SuzukiShift_comp
    {ω η : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hz : 0 < z.im)
    (hzη : 0 < (z + Complex.I * (η : ℂ)).im)
    (hf : IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp
        (Complex.I *
          (z + Complex.I * (η : ℂ) + Complex.I * (ω : ℂ)) * (t : ℂ)))
      (Ioi 0)) :
    FourierPlus
        (fun t => (SuzukiShift η (SuzukiShift ω f) t : ℂ)) z =
      ((z + Complex.I * (η : ℂ) + Complex.I * (ω : ℂ)) ^ 2 / z ^ 2) *
        FourierPlus (fun t => (f t : ℂ))
          (z + Complex.I * (η : ℂ) + Complex.I * (ω : ℂ)) := by
  let ζ : ℂ := z + Complex.I * (η : ℂ)
  have houter : IntegrableOn
      (fun t : ℝ => (SuzukiShift ω f t : ℂ) *
        Complex.exp (Complex.I * ζ * (t : ℂ))) (Ioi 0) := by
    apply integrableOn_SuzukiShift_exp (ω := ω) (z := ζ) hzη
    simpa only [ζ, add_assoc] using hf
  have hη := integral_SuzukiShift_exp
    (ω := η) (f := SuzukiShift ω f) (z := z) hz houter
  have hω := integral_SuzukiShift_exp
    (ω := ω) (f := f) (z := ζ) hzη
    (by simpa only [ζ, add_assoc] using hf)
  rw [hη, hω]
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have := congrArg Complex.im hzero
    simp only [Complex.zero_im] at this
    linarith
  let L := FourierPlus (fun t => (f t : ℂ))
    (z + Complex.I * (η : ℂ) + Complex.I * (ω : ℂ))
  change (ζ ^ 2 / z ^ 2) * (((ζ + Complex.I * (ω : ℂ)) ^ 2 / ζ ^ 2) * L) =
    ((ζ + Complex.I * (ω : ℂ)) ^ 2 / z ^ 2) * L
  field_simp [hz0, hζ0]

theorem integral_suzukiPsiShifted_exp_eq_logDeriv
    {ω : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hstrip : 1 / 2 - ω < z.im) :
    (∫ t : ℝ in Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      -(1 / z ^ 2) *
        logDeriv riemannXi
          (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) := by
  let ζ : ℂ := z + Complex.I * (ω : ℂ)
  have hζim : 1 / 2 < ζ.im := by
    dsimp [ζ]
    simp only [Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have := congrArg Complex.im hzero
    simp only [Complex.zero_im] at this
    linarith
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hint := integrableOn_suzukiPsi_exp hζim
  have hshift := integral_SuzukiShift_exp
    (ω := ω) (f := suzukiPsi) (z := z) hz hint
  have hbase : FourierPlus (fun t => (suzukiPsi t : ℂ)) ζ =
      (Complex.I / ζ ^ 2) * xiNevanlinnaQ ζ := by
    simpa only [FourierPlus] using
      (integral_suzukiPsi_exp_eq_xiNevanlinnaQ hζim)
  change FourierPlus (fun t => (SuzukiShift ω suzukiPsi t : ℂ)) z = _
  rw [hshift, hbase, xiNevanlinnaQ]
  have harg : (1 / 2 : ℂ) - Complex.I * ζ =
      (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) := by
    dsimp [ζ]
    rw [mul_add, ← mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  rw [harg]
  have hζ0' : z + Complex.I * (ω : ℂ) ≠ 0 := by
    exact hζ0
  dsimp [ζ]
  field_simp [hz0, hζ0']
  rw [Complex.I_sq]
  ring

/-- In Suzuki's primary parameter range, the strip inequality itself places
the frequency in the upper half-plane. -/
theorem integral_suzukiPsiShifted_exp_eq_logDeriv_of_le_half
    {ω : ℝ} (hω : ω ≤ 1 / 2) {z : ℂ}
    (hstrip : 1 / 2 - ω < z.im) :
    (∫ t : ℝ in Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      -(1 / z ^ 2) *
        logDeriv riemannXi
          (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) :=
  integral_suzukiPsiShifted_exp_eq_logDeriv (by linarith) hstrip

/-- The project-facing form of Suzuki's shifted transform equation (11.2). -/
theorem suzukiShiftedTransformFormula : SuzukiShiftedTransformFormula := by
  intro ω z hz hstrip
  exact integral_suzukiPsiShifted_exp_eq_logDeriv hz hstrip

end RHGarden
