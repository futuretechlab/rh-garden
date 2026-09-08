import RHGarden.SuzukiExplorer

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RHGarden

/-! ## Differential structure of the Suzuki shift -/

/-- On the positive half-line, differentiating Suzuki's two Volterra terms
once leaves a particularly small expression. -/
theorem hasDerivAt_SuzukiShift_of_pos
    (ω : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {t f' : ℝ} (ht : 0 < t)
    (hft : HasDerivAt f f' t) :
    HasDerivAt (SuzukiShift ω f)
      (Real.exp (-ω * t) * (f' + ω * f t) +
        ω ^ 2 * (∫ u in (0 : ℝ)..t, Real.exp (-ω * u) * f u)) t := by
  let h : ℝ → ℝ := fun u => Real.exp (-ω * u) * f u
  have hh : Continuous h := by
    dsimp [h]
    fun_prop
  have huh : Continuous (fun u : ℝ => u * h u) := by fun_prop
  let H₀ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, h u
  let H₁ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, u * h u
  have hH₀ : HasDerivAt H₀ (h t) t := by
    dsimp [H₀]
    exact intervalIntegral.integral_hasDerivAt_right
      (hh.intervalIntegrable 0 t)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have hH₁ : HasDerivAt H₁ (t * h t) t := by
    dsimp [H₁]
    exact intervalIntegral.integral_hasDerivAt_right
      (huh.intervalIntegrable 0 t)
      huh.aestronglyMeasurable.stronglyMeasurableAtFilter huh.continuousAt
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-ω * x))
      (-ω * Real.exp (-ω * t)) t := by
    convert (hasDerivAt_const_mul (-ω) (x := t)).exp using 1 <;> ring
  let G : ℝ → ℝ := fun x =>
    Real.exp (-ω * x) * f x + 2 * ω * H₀ x +
      ω ^ 2 * (x * H₀ x - H₁ x)
  have hG : HasDerivAt G
      (Real.exp (-ω * t) * (f' + ω * f t) + ω ^ 2 * H₀ t) t := by
    have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
    have hraw := (hexp.mul hft).add (hH₀.const_mul (2 * ω)) |>.add
      (((hid.mul hH₀).sub hH₁).const_mul (ω ^ 2))
    apply hraw.congr_deriv
    dsimp [h]
    ring
  apply hG.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with x hx
  simp only [SuzukiShift, abs_of_pos hx]
  dsimp [G, H₀, H₁, h]
  congr 2
  have hx₀ : IntervalIntegrable
      (fun u : ℝ => x * (Real.exp (-ω * u) * f u)) volume 0 x :=
    (continuous_const.mul hh).intervalIntegrable 0 x
  have hx₁ : IntervalIntegrable
      (fun u : ℝ => u * (Real.exp (-ω * u) * f u)) volume 0 x :=
    huh.intervalIntegrable 0 x
  calc
    (∫ u in (0 : ℝ)..x, (x - u) * Real.exp (-ω * u) * f u) =
        ∫ u in (0 : ℝ)..x,
          x * (Real.exp (-ω * u) * f u) -
            u * (Real.exp (-ω * u) * f u) := by
          apply intervalIntegral.integral_congr
          intro u _
          ring
    _ = (∫ u in (0 : ℝ)..x, x * (Real.exp (-ω * u) * f u)) -
        ∫ u in (0 : ℝ)..x, u * (Real.exp (-ω * u) * f u) :=
      intervalIntegral.integral_sub hx₀ hx₁
    _ = x * (∫ u in (0 : ℝ)..x, Real.exp (-ω * u) * f u) -
        ∫ u in (0 : ℝ)..x, u * (Real.exp (-ω * u) * f u) := by
      rw [intervalIntegral.integral_const_mul]

/-- The defining differential cancellation of Suzuki's shift.  At a
positive point where `f` is twice differentiable (and differentiable in a
neighborhood), every Volterra correction cancels from the second
derivative. -/
theorem hasDerivAt_deriv_SuzukiShift_of_pos
    (ω : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {t f'' : ℝ} (ht : 0 < t)
    (hft : HasDerivAt f (deriv f t) t)
    (hf2 : HasDerivAt (deriv f) f'' t)
    (hlocal : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x) :
    HasDerivAt (deriv (SuzukiShift ω f))
      (Real.exp (-ω * t) * f'') t := by
  let h : ℝ → ℝ := fun u => Real.exp (-ω * u) * f u
  have hh : Continuous h := by
    dsimp [h]
    fun_prop
  let H₀ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, h u
  have hH₀ : HasDerivAt H₀ (h t) t := by
    dsimp [H₀]
    exact intervalIntegral.integral_hasDerivAt_right
      (hh.intervalIntegrable 0 t)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-ω * x))
      (-ω * Real.exp (-ω * t)) t := by
    convert (hasDerivAt_const_mul (-ω) (x := t)).exp using 1 <;> ring
  let D : ℝ → ℝ := fun x =>
    Real.exp (-ω * x) * (deriv f x + ω * f x) + ω ^ 2 * H₀ x
  have hD : HasDerivAt D (Real.exp (-ω * t) * f'') t := by
    have hsum := hf2.add (hft.const_mul ω)
    have hraw := (hexp.mul hsum).add (hH₀.const_mul (ω ^ 2))
    apply hraw.congr_deriv
    dsimp [h]
    ring
  apply hD.congr_of_eventuallyEq
  filter_upwards [hlocal, eventually_gt_nhds ht] with x hfx hx
  exact (hasDerivAt_SuzukiShift_of_pos ω hf hx hfx.hasDerivAt).deriv

theorem secondDeriv_SuzukiShift
    (ω : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hft : DifferentiableAt ℝ f t)
    (hf2 : DifferentiableAt ℝ (deriv f) t)
    (hlocal : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x) :
    deriv (deriv (SuzukiShift ω f)) t =
      Real.exp (-ω * t) * deriv (deriv f) t :=
  (hasDerivAt_deriv_SuzukiShift_of_pos ω hf ht hft.hasDerivAt
    hf2.hasDerivAt hlocal).deriv

/-! ## The universal archimedean curvature -/

/-- Local derivative of `artanh` on its natural real domain.  The pinned
Mathlib defines `artanh` but does not package this derivative theorem. -/
theorem hasDerivAt_artanh_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    exact (hasDerivAt_id x).const_add 1
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    exact (hasDerivAt_id x).const_sub 1
  have hden0 : 1 - x ≠ 0 := by linarith [hx.2]
  have hnum0 : 1 + x ≠ 0 := by linarith [hx.1]
  have hsq0 : 1 - x ^ 2 ≠ 0 := by
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith [hx.2]) (by linarith [hx.1])
    nlinarith
  have hquot := hnum.div hden hden0
  have hlog := hquot.log (div_ne_zero hnum0 hden0)
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  change HasDerivAt (fun y : ℝ =>
      (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)))
    ((1 / 2 : ℝ) *
      ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2 /
        ((1 + x) / (1 - x)))) x at hhalf
  have hderiv : (1 / 2 : ℝ) *
      ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2 /
        ((1 + x) / (1 - x))) = 1 / (1 - x ^ 2) := by
    field_simp [hden0, hnum0, hsq0]
    ring
  rw [hderiv] at hhalf
  apply hhalf.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]

/-- The unsimplified derivative of Suzuki's prime-free first derivative. -/
noncomputable def suzukiPsiCurvatureRaw (t : ℝ) : ℝ :=
  let y := Real.exp (t / 2)
  let q := Real.exp (-t / 2)
  y + q - y / (2 * (1 + y ^ 2)) - q / (2 * (1 - q ^ 2))

/-- Closed form of the cell-independent curvature. -/
noncomputable def suzukiPsiCurvature (t : ℝ) : ℝ :=
  let y := Real.exp (t / 2)
  y + 1 / y - y ^ 3 / (y ^ 4 - 1)

theorem hasDerivAt_suzukiPsiPrimeFreeDerivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPsiPrimeFreeDerivative (suzukiPsiCurvatureRaw t) t := by
  let y := Real.exp (t / 2)
  let q := Real.exp (-t / 2)
  have hy : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (y / 2) t := by
    have hlin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t :=
      (hasDerivAt_id t).div_const 2
    simpa [y, div_eq_mul_inv, mul_comm] using hlin.exp
  have hq : HasDerivAt (fun x : ℝ => Real.exp (-x / 2)) (-q / 2) t := by
    have hlin : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) t :=
      (hasDerivAt_id t).neg.div_const 2
    simpa [q, div_eq_mul_inv, mul_comm] using hlin.exp
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hatan : HasDerivAt (fun x : ℝ => Real.arctan (Real.exp (x / 2)))
      ((y / 2) / (1 + y ^ 2)) t := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_arctan y).comp t hy
  have hartanh : HasDerivAt (fun x : ℝ => Real.artanh (Real.exp (-x / 2)))
      ((-q / 2) / (1 - q ^ 2)) t := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_artanh_of_mem_Ioo ⟨by linarith, hq1⟩).comp t hq
  have hraw := ((hy.sub hq).const_mul 2).add_const suzukiPsiDerivativeConstant
    |>.sub hatan |>.add hartanh
  apply hraw.congr_deriv
  dsimp [suzukiPsiCurvatureRaw, y, q]
  field_simp [show 1 + Real.exp (t / 2) ^ 2 ≠ 0 by positivity,
    show 1 - Real.exp (-t / 2) ^ 2 ≠ 0 by
      have : Real.exp (-t / 2) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      nlinarith]
  ring

theorem suzukiPsiCurvatureRaw_eq_curvature {t : ℝ} (ht : 0 < t) :
    suzukiPsiCurvatureRaw t = suzukiPsiCurvature t := by
  let y := Real.exp (t / 2)
  have hy0 : y ≠ 0 := by dsimp [y]; positivity
  have hygt : 1 < y := by
    dsimp [y]
    rw [← Real.exp_zero, Real.exp_lt_exp]
    linarith
  have hy1 : y ≠ 1 := ne_of_gt hygt
  have hy2gt : 1 < y ^ 2 := by
    have hp : 0 < (y - 1) * (y + 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hy2 : y ^ 2 ≠ 1 := ne_of_gt hy2gt
  have hy4gt : 1 < y ^ 4 := by
    have hp : 0 < (y ^ 2 - 1) * (y ^ 2 + 1) :=
      mul_pos (by linarith) (by positivity)
    nlinarith [show (y ^ 2) ^ 2 = y ^ 4 by ring]
  have hy4 : y ^ 4 ≠ 1 := ne_of_gt hy4gt
  have hq : Real.exp (-t / 2) = 1 / y := by
    dsimp [y]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  change y + Real.exp (-t / 2) - y / (2 * (1 + y ^ 2)) -
      Real.exp (-t / 2) / (2 * (1 - Real.exp (-t / 2) ^ 2)) =
    y + 1 / y - y ^ 3 / (y ^ 4 - 1)
  rw [hq]
  field_simp [hy0, hy2, hy4]
  ring

theorem hasDerivAt_deriv_suzukiPsiArchimedean {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv suzukiPsiArchimedean) (suzukiPsiCurvature t) t := by
  have hcurv := hasDerivAt_suzukiPsiPrimeFreeDerivative ht
  rw [suzukiPsiCurvatureRaw_eq_curvature ht] at hcurv
  apply hcurv.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with x hx
  exact (hasDerivAt_suzukiPsiArchimedean_of_pos hx).deriv

theorem secondDeriv_suzukiPsiArchimedean {t : ℝ} (ht : 0 < t) :
    deriv (deriv suzukiPsiArchimedean) t = suzukiPsiCurvature t :=
  (hasDerivAt_deriv_suzukiPsiArchimedean ht).deriv

/-! ## Affine prime terms and cellwise curvature -/

/-- The constant first-derivative contribution of the primes active in the
`n`th cell. -/
noncomputable def suzukiPrimeCellSlope (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 n,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k

private theorem hasDerivAt_fixedPrimeContribution (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∑ k ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (y - Real.log k))
      (suzukiPrimeCellSlope n) t := by
  unfold suzukiPrimeCellSlope
  apply HasDerivAt.fun_sum
  intro k hk
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id t).sub_const (Real.log k)).const_mul
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k)

theorem hasDerivAt_suzukiPsiPrimeContribution_on_cell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    HasDerivAt suzukiPsiPrimeContribution (suzukiPrimeCellSlope n) t := by
  apply (hasDerivAt_fixedPrimeContribution n t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with y hy hy'
  exact suzukiPsiPrimeContribution_eq_fixed_sum_on_cell hn ⟨hy.le, hy'⟩

/-- Within a prime cell the entire Mangoldt contribution is affine, so its
second derivative vanishes identically. -/
theorem secondDeriv_primeContribution_eq_zero_on_cell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    deriv (deriv suzukiPsiPrimeContribution) t = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => suzukiPrimeCellSlope n) 0 t :=
    hasDerivAt_const t _
  apply (hconst.congr_of_eventuallyEq ?_).deriv
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with y hy hy'
  exact (hasDerivAt_suzukiPsiPrimeContribution_on_cell hn ⟨hy, hy'⟩).deriv

theorem hasDerivAt_suzukiPsi_on_primeCell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    HasDerivAt suzukiPsi
      (suzukiPsiPrimeFreeDerivative t - suzukiPrimeCellSlope n) t := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht0 : 0 < t := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) ht.1
  have h := (hasDerivAt_suzukiPsiArchimedean_of_pos ht0).sub
    (hasDerivAt_suzukiPsiPrimeContribution_on_cell hn ht)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht0, eventually_gt_nhds ht.1,
      eventually_lt_nhds ht.2] with y hy0 hy hy'
  rw [suzukiPsi_eq_primeSide, suzukiPsiPrimeSide, abs_of_pos hy0,
    suzukiPsiPrimeSideNonneg]
  rfl

theorem hasDerivAt_deriv_suzukiPsi_on_primeCell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    HasDerivAt (deriv suzukiPsi) (suzukiPsiCurvature t) t := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht0 : 0 < t := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) ht.1
  have h := (hasDerivAt_deriv_suzukiPsiArchimedean ht0).sub_const
    (suzukiPrimeCellSlope n)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with y hy hy'
  have hy0 : 0 < y := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) hy
  rw [(hasDerivAt_suzukiPsiArchimedean_of_pos hy0).deriv]
  exact (hasDerivAt_suzukiPsi_on_primeCell hn ⟨hy, hy'⟩).deriv

theorem secondDeriv_suzukiPsi_eq_exp_formula
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    deriv (deriv suzukiPsi) t =
      let y := Real.exp (t / 2)
      y + 1 / y - y ^ 3 / (y ^ 4 - 1) := by
  simpa only [suzukiPsiCurvature] using
    (hasDerivAt_deriv_suzukiPsi_on_primeCell hn ht).deriv

theorem secondDeriv_suzukiPsi_eq_archimedean_on_cell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    deriv (deriv suzukiPsi) t =
      deriv (deriv suzukiPsiArchimedean) t := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht0 : 0 < t := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) ht.1
  rw [secondDeriv_suzukiPsiArchimedean ht0]
  exact (hasDerivAt_deriv_suzukiPsi_on_primeCell hn ht).deriv

/-! ## A uniform positive lower bound -/

/-- Elementary lower bound for the rational-exponential curvature
expression.  The deliberately coarse constant `1` is enough for strong
convexity certificates. -/
theorem exp_formula_ge_one_of_sqrt_two_le {y : ℝ}
    (hy : Real.sqrt 2 ≤ y) :
    1 ≤ y + 1 / y - y ^ 3 / (y ^ 4 - 1) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hy0 : 0 < y := hspos.trans_le hy
  have hs7 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith
  have hy7 : (7 / 5 : ℝ) ≤ y := hs7.trans hy
  have hy2 : (2 : ℝ) ≤ y ^ 2 := by
    have hp : 0 ≤ (y - Real.sqrt 2) * (y + Real.sqrt 2) :=
      mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hy0.le hs0)
    nlinarith
  have hy3 : (14 / 5 : ℝ) ≤ y ^ 3 := by
    calc
      (14 / 5 : ℝ) = (7 / 5 : ℝ) * 2 := by norm_num
      _ ≤ y * y ^ 2 := mul_le_mul hy7 hy2 (by norm_num) hy0.le
      _ = y ^ 3 := by ring
  have hym1 : (2 / 5 : ℝ) ≤ y - 1 := by linarith
  have hprod : (28 / 25 : ℝ) ≤ (y - 1) * y ^ 3 := by
    calc
      (28 / 25 : ℝ) = (2 / 5 : ℝ) * (14 / 5 : ℝ) := by norm_num
      _ ≤ (y - 1) * y ^ 3 :=
        mul_le_mul hym1 hy3 (by norm_num) (by linarith)
  have hpoly : y ^ 3 ≤ y ^ 4 - 1 := by
    nlinarith
  have hy3pos : 0 < y ^ 3 := pow_pos hy0 3
  have hden : 0 < y ^ 4 - 1 := lt_of_lt_of_le hy3pos hpoly
  have hratio : y ^ 3 / (y ^ 4 - 1) ≤ 1 :=
    (div_le_one hden).2 hpoly
  have hsqdiv : 0 ≤ (y - 1) ^ 2 / y :=
    div_nonneg (sq_nonneg _) hy0.le
  have hamgm : 2 ≤ y + 1 / y := by
    have heq : (y - 1) ^ 2 / y = y + 1 / y - 2 := by
      field_simp [ne_of_gt hy0]
      ring
    nlinarith
  linarith

private theorem sqrt_two_le_exp_half_of_log_two_le {t : ℝ}
    (ht : Real.log 2 ≤ t) :
    Real.sqrt 2 ≤ Real.exp (t / 2) := by
  let y := Real.exp (t / 2)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hexp : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hy2 : y ^ 2 = Real.exp t := by
    dsimp [y]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sqrt_le_iff]
  constructor
  · exact hy0
  · change (2 : ℝ) ≤ y ^ 2
    rw [hy2]
    exact hexp

/-- On every open prime cell at or beyond the first prime, the unshifted
Suzuki function has curvature at least one. -/
theorem one_le_secondDeriv_suzukiPsi_on_primeCell
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    1 ≤ deriv (deriv suzukiPsi) t := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [secondDeriv_suzukiPsi_eq_exp_formula hn0 ht]
  apply exp_formula_ge_one_of_sqrt_two_le
  apply sqrt_two_le_exp_half_of_log_two_le
  exact (Real.log_le_log (by norm_num) (by exact_mod_cast hn)).trans ht.1.le

private theorem eventually_differentiableAt_suzukiPsi_on_cell
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ suzukiPsi x := by
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with x hx hx'
  exact differentiableAt_suzukiPsi_primeCellInterior hn ⟨hx, hx'⟩

theorem hasDerivAt_deriv_suzukiPsiShifted_on_primeCell
    (ω : ℝ) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    HasDerivAt (deriv (suzukiPsiShifted ω))
      (Real.exp (-ω * t) * suzukiPsiCurvature t) t := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht0 : 0 < t := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) ht.1
  unfold suzukiPsiShifted
  exact hasDerivAt_deriv_SuzukiShift_of_pos ω continuous_suzukiPsi ht0
    (differentiableAt_suzukiPsi_primeCellInterior hn ht).hasDerivAt
    (hasDerivAt_deriv_suzukiPsi_on_primeCell hn ht)
    (eventually_differentiableAt_suzukiPsi_on_cell hn ht)

theorem secondDeriv_suzukiPsiShifted
    (ω : ℝ) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    deriv (deriv (suzukiPsiShifted ω)) t =
      Real.exp (-ω * t) * deriv (deriv suzukiPsi) t := by
  rw [(hasDerivAt_deriv_suzukiPsiShifted_on_primeCell ω hn ht).deriv,
    (hasDerivAt_deriv_suzukiPsi_on_primeCell hn ht).deriv]

/-- Strict positive curvature is preserved by every real Suzuki shift, not
only by rightward (nonnegative) shifts. -/
theorem secondDeriv_suzukiPsiShifted_pos_on_primeCell
    (ω : ℝ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    0 < deriv (deriv (suzukiPsiShifted ω)) t := by
  rw [secondDeriv_suzukiPsiShifted ω (lt_of_lt_of_le (by norm_num) hn) ht]
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one
    (one_le_secondDeriv_suzukiPsi_on_primeCell hn ht))

/-- The derivative of every shifted Suzuki function is strictly increasing
through each open prime cell `n ≥ 2`. -/
theorem strictMonoOn_deriv_suzukiPsiShifted_primeCell
    (ω : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (deriv (suzukiPsiShifted ω))
      (Ioo (Real.log n) (Real.log (n + 1))) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn (deriv (suzukiPsiShifted ω)) (Icc x y) := by
    intro z hz
    have hzcell : z ∈ Ioo (Real.log n) (Real.log (n + 1)) :=
      ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
    exact (hasDerivAt_deriv_suzukiPsiShifted_on_primeCell ω
      (lt_of_lt_of_le (by norm_num) hn) hzcell).continuousAt.continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc x y) hcont (fun z hz => by
    rw [interior_Icc] at hz
    have hzcell : z ∈ Ioo (Real.log n) (Real.log (n + 1)) :=
      ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    exact secondDeriv_suzukiPsiShifted_pos_on_primeCell ω hn hzcell)
  exact hmono ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy

/-- Equivalent geometric packaging: every closed prime cell `n ≥ 2` is a
strict-convexity domain for every real shift parameter. -/
theorem strictConvexOn_suzukiPsiShifted_primeCell
    (ω : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    StrictConvexOn ℝ (Icc (Real.log n) (Real.log (n + 1)))
      (suzukiPsiShifted ω) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
    (continuous_suzukiPsiShifted ω).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  change 0 < deriv (deriv (suzukiPsiShifted ω)) t
  exact secondDeriv_suzukiPsiShifted_pos_on_primeCell ω hn ht

/-- There is at most one interior critical point in each shifted prime
cell. -/
theorem unique_criticalPoint_suzukiPrimeCell
    (ω : ℝ) {n : ℕ} (hn : 2 ≤ n) {x y : ℝ}
    (hx : x ∈ Ioo (Real.log n) (Real.log (n + 1)))
    (hy : y ∈ Ioo (Real.log n) (Real.log (n + 1)))
    (hxc : deriv (suzukiPsiShifted ω) x = 0)
    (hyc : deriv (suzukiPsiShifted ω) y = 0) :
    x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hlt := strictMonoOn_deriv_suzukiPsiShifted_primeCell ω n hn hx hy hxy
    rw [hxc, hyc] at hlt
    exact (lt_irrefl 0 hlt).elim
  · exact hxy
  · have hlt := strictMonoOn_deriv_suzukiPsiShifted_primeCell ω n hn hy hx hxy
    rw [hxc, hyc] at hlt
    exact (lt_irrefl 0 hlt).elim

/-- An interior fold would require simultaneous vanishing of the first and
second derivatives.  Uniform positive curvature rules this out. -/
theorem no_interior_fold_suzukiPsiShifted_primeCell
    (ω : ℝ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (Real.log n) (Real.log (n + 1))) :
    ¬ (deriv (suzukiPsiShifted ω) t = 0 ∧
      deriv (deriv (suzukiPsiShifted ω)) t = 0) := by
  intro hfold
  exact (ne_of_gt (secondDeriv_suzukiPsiShifted_pos_on_primeCell ω hn ht))
    hfold.2

/-! ## Strong-convexity certificates -/

/-- A pointwise second-derivative lower bound gives a global lower bound
without locating the (generally transcendental) minimizer.  The correction
`f'(x)^2 / (2m)` is the exact minimum of the supporting quadratic. -/
theorem lower_bound_of_secondDeriv_ge
    {f : ℝ → ℝ} {a b x m : ℝ}
    (hab : a < b) (hm : 0 < m) (hx : x ∈ Ioo a b)
    (hcont : ContinuousOn f (Icc a b))
    (hfdiff : DifferentiableOn ℝ f (Ioo a b))
    (hf2diff : DifferentiableOn ℝ (deriv f) (Ioo a b))
    (hsecond : ∀ y ∈ Ioo a b, m ≤ deriv (deriv f) y) :
    ∀ y ∈ Icc a b,
      f x - (deriv f x) ^ 2 / (2 * m) ≤ f y := by
  let g : ℝ → ℝ := fun y => f y - m / 2 * y ^ 2
  let q : ℝ → ℝ := fun y => deriv f y - m * y
  let r : ℝ → ℝ := fun y => deriv (deriv f) y - m
  have hfirst : ∀ y ∈ Ioo a b, HasDerivAt g (q y) y := by
    intro y hy
    have hfy : DifferentiableAt ℝ f y :=
      (hfdiff y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have hsq := ((hasDerivAt_id y).pow 2).const_mul (m / 2)
    have hraw := hfy.hasDerivAt.sub hsq
    apply hraw.congr_deriv
    dsimp [q]
    ring
  have hsecond' : ∀ y ∈ Ioo a b, HasDerivAt q (r y) y := by
    intro y hy
    have hfy : DifferentiableAt ℝ (deriv f) y :=
      (hf2diff y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have hraw := hfy.hasDerivAt.sub ((hasDerivAt_id y).const_mul m)
    apply hraw.congr_deriv
    dsimp [r]
    ring
  have hgcont : ContinuousOn g (Icc a b) := by
    dsimp [g]
    fun_prop
  have hgconv : ConvexOn ℝ (Icc a b) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) hgcont
    · intro y hy
      rw [interior_Icc] at hy
      exact (hfirst y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hsecond' y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      dsimp [r]
      linarith [hsecond y hy]
  have hxcell : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hgx : HasDerivAt g (q x) x := hfirst x hx
  intro y hy
  have htangent : g x + q x * (y - x) ≤ g y := by
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have hs := hgconv.le_slope_of_hasDerivAt hxcell hy hxy hgx
      rw [slope_def_field] at hs
      have hmul := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
      linarith
    · subst y
      simp
    · have hs := hgconv.slope_le_of_hasDerivAt hy hxcell hxy hgx
      rw [slope_def_field] at hs
      have hmul := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
      nlinarith
  have hstrong :
      f x + deriv f x * (y - x) + m / 2 * (y - x) ^ 2 ≤ f y := by
    dsimp [g, q] at htangent
    nlinarith
  have hcomp : 0 ≤ (m * (y - x) + deriv f x) ^ 2 / (2 * m) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hid :
      f x + deriv f x * (y - x) + m / 2 * (y - x) ^ 2 -
          (f x - (deriv f x) ^ 2 / (2 * m)) =
        (m * (y - x) + deriv f x) ^ 2 / (2 * m) := by
    field_simp [ne_of_gt hm]
    ring
  linarith

/-- Exact, kernel-checkable strong-convexity certificate schema for one
Suzuki prime cell.  Numerical exploration may suggest the rational data,
but every analytic bound is an explicit proof field. -/
structure SuzukiStrongConvexCellCertificate where
  omega : ℚ
  cell : ℕ
  sampleX : ℚ
  curvatureLower : ℚ
  valueLower : ℚ
  derivAbsUpper : ℚ
  cell_ge_two : 2 ≤ cell
  sample_mem : (sampleX : ℝ) ∈
    Ioo (Real.log cell) (Real.log (cell + 1))
  curvature_pos : (0 : ℝ) < curvatureLower
  value_bound : (valueLower : ℝ) ≤
    suzukiPsiShifted (omega : ℝ) (sampleX : ℝ)
  deriv_bound :
    |deriv (suzukiPsiShifted (omega : ℝ)) (sampleX : ℝ)| ≤
      (derivAbsUpper : ℝ)
  curvature_bound : ∀ t ∈ Ioo (Real.log cell) (Real.log (cell + 1)),
    (curvatureLower : ℝ) ≤
      deriv (deriv (suzukiPsiShifted (omega : ℝ))) t
  certificate_positive :
    (0 : ℝ) < (valueLower : ℝ) -
      (derivAbsUpper : ℝ) ^ 2 / (2 * (curvatureLower : ℝ))

/-- A verified strong-convexity certificate proves strict positivity on its
entire closed prime cell. -/
theorem SuzukiStrongConvexCellCertificate.positive_on_cell
    (c : SuzukiStrongConvexCellCertificate) :
    ∀ t ∈ Icc (Real.log c.cell) (Real.log (c.cell + 1)),
      0 < suzukiPsiShifted (c.omega : ℝ) t := by
  have hlog : Real.log c.cell < Real.log (c.cell + 1) := by
    apply Real.log_lt_log
    · exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) c.cell_ge_two)
    · exact_mod_cast Nat.lt_succ_self c.cell
  have hbound := lower_bound_of_secondDeriv_ge
    (f := suzukiPsiShifted (c.omega : ℝ)) hlog c.curvature_pos c.sample_mem
    (continuous_suzukiPsiShifted (c.omega : ℝ)).continuousOn
    (differentiableOn_suzukiPsiShifted_primeCellInterior
      (c.omega : ℝ) c.cell (lt_of_lt_of_le (by norm_num) c.cell_ge_two))
    (fun t ht =>
      (hasDerivAt_deriv_suzukiPsiShifted_on_primeCell (c.omega : ℝ)
        (lt_of_lt_of_le (by norm_num) c.cell_ge_two) ht).differentiableAt.differentiableWithinAt)
    c.curvature_bound
  intro t ht
  have hsample := hbound t ht
  have hderivsq :
      (deriv (suzukiPsiShifted (c.omega : ℝ)) (c.sampleX : ℝ)) ^ 2 ≤
        (c.derivAbsUpper : ℝ) ^ 2 := by
    rw [← sq_abs]
    have hupper : 0 ≤ (c.derivAbsUpper : ℝ) :=
      (abs_nonneg _).trans c.deriv_bound
    exact (sq_le_sq₀ (abs_nonneg _) hupper).2 c.deriv_bound
  have hcorr :
      (deriv (suzukiPsiShifted (c.omega : ℝ)) (c.sampleX : ℝ)) ^ 2 /
          (2 * (c.curvatureLower : ℝ)) ≤
        (c.derivAbsUpper : ℝ) ^ 2 /
          (2 * (c.curvatureLower : ℝ)) := by
    exact div_le_div_of_nonneg_right hderivsq
      (mul_nonneg (by norm_num) c.curvature_pos.le)
  linarith [c.value_bound, c.certificate_positive]

end RHGarden
