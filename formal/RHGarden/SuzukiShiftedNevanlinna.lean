import RHGarden.SuzukiShiftedLandau

noncomputable section

open Complex Filter Set
open scoped Topology ComplexConjugate

namespace RHGarden

/-- The xi logarithmic derivative viewed from the shifted vertical line
`Re s = 1/2 + ω`. -/
noncomputable def xiNevanlinnaQShifted (ω : ℝ) (z : ℂ) : ℂ :=
  Complex.I *
    logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z)

/-- Shifting the vertical xi line amounts to translating the centered
Nevanlinna variable by `iω`. -/
theorem xiNevanlinnaQShifted_eq_translate (ω : ℝ) (z : ℂ) :
    xiNevanlinnaQShifted ω z =
      xiNevanlinnaQ (z + Complex.I * (ω : ℂ)) := by
  rw [xiNevanlinnaQShifted, xiNevanlinnaQ]
  apply congrArg (fun s : ℂ => Complex.I * logDeriv riemannXi s)
  push_cast
  rw [mul_add, ← mul_assoc, I_mul_I]
  ring

/-- A zero strictly sampled by the shifted upper half-plane would contradict
`XiZeroFreeRightOf ω`. -/
theorem riemannXi_shifted_center_ne_zero_of_zeroFreeRight
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im) :
    riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) ≠ 0 := by
  intro hxi
  have hle := hzero
    (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) hxi
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub] at hle
  linarith

/-- Zero-freeness to the right of the shifted line makes the shifted xi
logarithmic derivative analytic throughout the upper half-plane. -/
theorem analyticOnNhd_xiNevanlinnaQShifted_upper
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) :
    AnalyticOnNhd ℂ (xiNevanlinnaQShifted ω) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hne := riemannXi_shifted_center_ne_zero_of_zeroFreeRight hzero hz
  have hxi : AnalyticAt ℂ riemannXi
      (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) :=
    differentiable_riemannXi.analyticAt _
  have hld : AnalyticAt ℂ (logDeriv riemannXi)
      (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) := by
    rw [logDeriv]
    exact hxi.deriv.div hxi hne
  change AnalyticAt ℂ
    (fun w : ℂ => Complex.I *
      logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * w)) z
  have haff : AnalyticAt ℂ
      (fun w : ℂ => (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * w)) z := by
    fun_prop
  have hc : AnalyticAt ℂ
      ((logDeriv riemannXi) ∘
        (fun w : ℂ => (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * w))) z :=
    AnalyticAt.comp
      (g := logDeriv riemannXi)
      (f := fun w : ℂ => (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * w)) hld haff
  exact analyticAt_const.mul (by simpa [Function.comp_def] using hc)

/-- The spectral coordinate relative to the shifted vertical boundary. -/
noncomputable def xiSpectralParameterShifted
    (ω : ℝ) (a : XiZeroOccurrence) : ℂ :=
  xiSpectralParameter a - Complex.I * (ω : ℂ)

@[simp] theorem xiSpectralParameterShifted_im
    (ω : ℝ) (a : XiZeroOccurrence) :
    (xiSpectralParameterShifted ω a).im = a.value.re - 1 / 2 - ω := by
  simp [xiSpectralParameterShifted]

theorem xiZero_eq_shifted_center_sub_I_mul_spectral
    (ω : ℝ) (a : XiZeroOccurrence) :
    a.value = (((1 / 2 + ω : ℝ) : ℂ) -
      Complex.I * xiSpectralParameterShifted ω a) := by
  rw [xiSpectralParameterShifted, xiZero_eq_half_sub_I_mul_spectral]
  push_cast
  rw [mul_sub, ← mul_assoc, I_mul_I]
  ring

theorem xiSpectralParameterShifted_im_nonpos_of_zeroFreeRight
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) (a : XiZeroOccurrence) :
    (xiSpectralParameterShifted ω a).im ≤ 0 := by
  rw [xiSpectralParameterShifted_im]
  have hle := hzero a.value a.1.xi_eq_zero
  linarith

private theorem xiZero_multiplicity_pos_shifted (ρ : XiZero) :
    0 < xiMultiplicity (ρ : ℂ) := by
  have hne : xiDivisor (ρ : ℂ) ≠ 0 := ρ.property
  have hcast := xiMultiplicity_cast (ρ : ℂ)
  by_contra hnot
  have hz : xiMultiplicity (ρ : ℂ) = 0 := Nat.eq_zero_of_not_pos hnot
  apply hne
  rw [← hcast, hz]
  norm_num

/-- The shifted zero-free half-plane is exactly the assertion that every
shifted spectral parameter lies on or below the real axis. -/
theorem xiZeroFreeRightOf_iff_spectralParameterShifted_im_nonpos
    (ω : ℝ) :
    XiZeroFreeRightOf ω ↔
      ∀ a : XiZeroOccurrence,
        (xiSpectralParameterShifted ω a).im ≤ 0 := by
  constructor
  · exact fun hzero a =>
      xiSpectralParameterShifted_im_nonpos_of_zeroFreeRight hzero a
  · intro hspectral s hs
    let ρ : XiZero := ⟨s, by
      rw [mem_xiDivisor_support_iff]
      exact hs⟩
    let a : XiZeroOccurrence :=
      ⟨ρ, ⟨0, xiZero_multiplicity_pos_shifted ρ⟩⟩
    have ha := hspectral a
    rw [xiSpectralParameterShifted_im] at ha
    change s.re ≤ 1 / 2 + ω
    change s.re - 1 / 2 - ω ≤ 0 at ha
    linarith

/-- The shifted exact spectral partial fraction, still in its absolutely
convergent genus-one normalization. -/
theorem xiNevanlinnaQShifted_eq_spectral_sum
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im) :
    xiNevanlinnaQShifted ω z =
      ∑' a : XiZeroOccurrence,
        xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a := by
  rw [xiNevanlinnaQShifted_eq_translate]
  apply xiNevanlinnaQ_eq_spectral_sum
  have hne := riemannXi_shifted_center_ne_zero_of_zeroFreeRight hzero hz
  convert hne using 1
  push_cast
  rw [mul_add, ← mul_assoc, I_mul_I]
  ring

/-- A pole on or below the real axis contributes nonnegative imaginary part
when sampled in the open upper half-plane. -/
theorem im_one_div_sub_nonneg_of_im_nonpos
    {γ z : ℂ} (hγ : γ.im ≤ 0) (hz : 0 < z.im) :
    0 ≤ (1 / (γ - z)).im := by
  simp only [div_eq_mul_inv, one_mul, Complex.inv_im, Complex.sub_im]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg (γ - z))

/-- Pairing an occurrence with its functional-equation reflection cancels
the genus-one correction.  Both remaining shifted poles contribute
nonnegative imaginary part. -/
theorem im_xiSpectralCorrectedTerm_reflection_pair_nonneg
    {ω : ℝ} (hzero : XiZeroFreeRightOf ω) {z : ℂ} (hz : 0 < z.im)
    (a : XiZeroOccurrence) :
    0 ≤ (xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
      xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
        (xiOccurrenceOneSubEquiv a)).im := by
  have ha :=
    xiSpectralParameterShifted_im_nonpos_of_zeroFreeRight hzero a
  have har := xiSpectralParameterShifted_im_nonpos_of_zeroFreeRight hzero
    (xiOccurrenceOneSubEquiv a)
  have hrewrite :
      xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ)) a +
          xiSpectralCorrectedTerm (z + Complex.I * (ω : ℂ))
            (xiOccurrenceOneSubEquiv a) =
        1 / (xiSpectralParameterShifted ω a - z) +
          1 / (xiSpectralParameterShifted ω
            (xiOccurrenceOneSubEquiv a) - z) := by
    simp only [xiSpectralCorrectedTerm, xiSpectralParameterShifted,
      xiSpectralParameter_oneSubOccurrence, one_div, inv_neg]
    ring
  rw [hrewrite, Complex.add_im]
  exact add_nonneg
    (im_one_div_sub_nonneg_of_im_nonpos ha hz)
    (im_one_div_sub_nonneg_of_im_nonpos har hz)

/-- The shifted xi Nevanlinna property. -/
def XiShiftedNevanlinna (ω : ℝ) : Prop :=
  IsNevanlinnaUpper (xiNevanlinnaQShifted ω)

/-- A zero-free shifted right half-plane makes the translated xi logarithmic
derivative a Nevanlinna function.  The key summation step pairs `γ` with
`-γ`, cancelling the otherwise sign-indefinite genus-one correction. -/
theorem xiShiftedNevanlinna_of_zeroFreeRight
    (ω : ℝ) (hzero : XiZeroFreeRightOf ω) :
    XiShiftedNevanlinna ω := by
  refine ⟨analyticOnNhd_xiNevanlinnaQShifted_upper hzero, ?_⟩
  intro z hz
  let q : ℂ := z + Complex.I * (ω : ℂ)
  have hcenter : riemannXi ((1 / 2 : ℂ) - Complex.I * q) ≠ 0 := by
    have hne := riemannXi_shifted_center_ne_zero_of_zeroFreeRight hzero hz
    convert hne using 1
    dsimp [q]
    push_cast
    rw [mul_add, ← mul_assoc, I_mul_I]
    ring
  have hs : Summable (xiSpectralCorrectedTerm q) :=
    summable_xiSpectralCorrectedTerm hcenter
  have hsr : Summable
      (fun a : XiZeroOccurrence =>
        xiSpectralCorrectedTerm q (xiOccurrenceOneSubEquiv a)) :=
    hs.comp_injective xiOccurrenceOneSubEquiv.injective
  have hp : Summable
      (fun a : XiZeroOccurrence =>
        xiSpectralCorrectedTerm q a +
          xiSpectralCorrectedTerm q (xiOccurrenceOneSubEquiv a)) :=
    hs.add hsr
  have hpnonneg : 0 ≤
      (∑' a : XiZeroOccurrence,
        (xiSpectralCorrectedTerm q a +
          xiSpectralCorrectedTerm q (xiOccurrenceOneSubEquiv a))).im := by
    rw [Complex.im_tsum hp]
    exact tsum_nonneg fun a => by
      dsimp [q]
      exact im_xiSpectralCorrectedTerm_reflection_pair_nonneg hzero hz a
  rw [hs.tsum_add hsr,
    xiOccurrenceOneSubEquiv.tsum_eq (xiSpectralCorrectedTerm q)] at hpnonneg
  simp only [Complex.add_im] at hpnonneg
  have hq : xiNevanlinnaQShifted ω z =
      ∑' a : XiZeroOccurrence, xiSpectralCorrectedTerm q a := by
    simpa [q] using xiNevanlinnaQShifted_eq_spectral_sum hzero hz
  rw [hq]
  linarith

/-- Alias following the `xiNevanlinnaQShifted` spelling used by the shifted
Suzuki interface. -/
theorem xiNevanlinnaShifted_of_zeroFreeRight
    (ω : ℝ) : XiZeroFreeRightOf ω → XiShiftedNevanlinna ω :=
  xiShiftedNevanlinna_of_zeroFreeRight ω

private theorem not_analyticAt_logDeriv_riemannXi_of_zero_shifted {ρ : ℂ}
    (hρ : riemannXi ρ = 0) :
    ¬ AnalyticAt ℂ (logDeriv riemannXi) ρ := by
  intro hld
  exact not_tendsto_logDeriv_riemannXi_of_zero hρ _
    (hld.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

private theorem analyticAt_logDeriv_riemannXi_of_analyticAt_shiftedQ
    {ω : ℝ} {z : ℂ} (hQ : AnalyticAt ℂ (xiNevanlinnaQShifted ω) z) :
    AnalyticAt ℂ (logDeriv riemannXi)
      (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) := by
  let center : ℂ :=
    (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z)
  let invCoord : ℂ → ℂ := fun w =>
    Complex.I * (w - ((1 / 2 + ω : ℝ) : ℂ))
  have hcoord : invCoord center = z := by
    dsimp [invCoord, center]
    rw [show (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z -
        ((1 / 2 + ω : ℝ) : ℂ)) = -Complex.I * z by ring]
    simp [← mul_assoc]
  have hinv : AnalyticAt ℂ invCoord center := by
    dsimp [invCoord]
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w => -Complex.I * xiNevanlinnaQShifted ω (invCoord w))
      center := by
    exact analyticAt_const.mul (hQ.comp_of_eq hinv hcoord)
  have hfun :
      (fun w => -Complex.I * xiNevanlinnaQShifted ω (invCoord w)) =
        logDeriv riemannXi := by
    funext w
    rw [xiNevanlinnaQShifted]
    have harg : (((1 / 2 + ω : ℝ) : ℂ) -
        Complex.I * invCoord w) = w := by
      dsimp [invCoord]
      rw [← mul_assoc, I_mul_I]
      ring
    rw [harg]
    simp [← mul_assoc]
  rw [hfun] at hcomp
  exact hcomp

private theorem xiSpectralParameterShifted_im_nonpos_of_nevanlinna
    {ω : ℝ} (hN : XiShiftedNevanlinna ω) (a : XiZeroOccurrence) :
    (xiSpectralParameterShifted ω a).im ≤ 0 := by
  by_contra hnot
  have hpos : 0 < (xiSpectralParameterShifted ω a).im := lt_of_not_ge hnot
  have hQ : AnalyticAt ℂ (xiNevanlinnaQShifted ω)
      (xiSpectralParameterShifted ω a) :=
    hN.1 (xiSpectralParameterShifted ω a) hpos
  have hld :=
    analyticAt_logDeriv_riemannXi_of_analyticAt_shiftedQ hQ
  rw [← xiZero_eq_shifted_center_sub_I_mul_spectral ω a] at hld
  exact not_analyticAt_logDeriv_riemannXi_of_zero_shifted
    a.1.xi_eq_zero hld

/-- For the shifted xi family, the zero-free right half-plane and translated
Nevanlinna conditions are equivalent.  The reverse implication needs only
upper-half-plane analyticity: an upper shifted spectral zero would create a
genuine logarithmic-derivative pole. -/
theorem xiZeroFreeRightOf_iff_xiShiftedNevanlinna (ω : ℝ) :
    XiZeroFreeRightOf ω ↔ XiShiftedNevanlinna ω := by
  constructor
  · exact xiShiftedNevanlinna_of_zeroFreeRight ω
  · intro hN
    rw [xiZeroFreeRightOf_iff_spectralParameterShifted_im_nonpos]
    exact xiSpectralParameterShifted_im_nonpos_of_nevanlinna hN

theorem xiShiftedNevanlinna_half : XiShiftedNevanlinna (1 / 2) :=
  (xiZeroFreeRightOf_iff_xiShiftedNevanlinna (1 / 2)).mp
    xiZeroFreeRightOf_half

/-- Equation (11.2), normalized in terms of the shifted Nevanlinna function. -/
theorem integral_suzukiPsiShifted_exp_eq_xiNevanlinnaQShifted
    {ω : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hstrip : 1 / 2 - ω < z.im) :
    (∫ t : ℝ in Set.Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
      (Complex.I / z ^ 2) * xiNevanlinnaQShifted ω z := by
  rw [integral_suzukiPsiShifted_exp_eq_logDeriv hz hstrip,
    xiNevanlinnaQShifted]
  calc
    -(1 / z ^ 2) *
        logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) =
      ((Complex.I * Complex.I) / z ^ 2) *
        logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z) := by
          simp only [I_mul_I, neg_div]
    _ = (Complex.I / z ^ 2) *
        (Complex.I *
          logDeriv riemannXi
            (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * z)) := by ring

/-- The remaining shifted Herglotz-to-screw implication.  Suzuki obtains
the stronger global nonnegativity statement from the general
Nevanlinna/screw correspondence; RH Garden keeps that representation theorem
as one explicit formalization boundary. -/
def ShiftedNevanlinnaToPsiNonnegative : Prop :=
  ∀ ω : ℝ, XiShiftedNevanlinna ω →
    ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t

theorem xiZeroFreeRightOf_implies_shiftedEventuallyNonnegative_of_bridge
    (hbridge : ShiftedNevanlinnaToPsiNonnegative) (ω : ℝ) :
    XiZeroFreeRightOf ω → SuzukiPsiShiftedEventuallyNonnegative ω := by
  intro hzero
  refine ⟨0, ?_⟩
  intro t _ht
  exact hbridge ω (xiShiftedNevanlinna_of_zeroFreeRight ω hzero) t

theorem xiZeroFreeRightOf_iff_shiftedEventuallyNonnegative_of_bridge
    (hbridge : ShiftedNevanlinnaToPsiNonnegative) (ω : ℝ) :
    XiZeroFreeRightOf ω ↔ SuzukiPsiShiftedEventuallyNonnegative ω :=
  ⟨xiZeroFreeRightOf_implies_shiftedEventuallyNonnegative_of_bridge
      hbridge ω,
    xiZeroFreeRightOf_of_shifted_eventually_nonnegative ω⟩

theorem suzukiShiftedEventualCriterion_of_nevanlinna_bridge
    (hbridge : ShiftedNevanlinnaToPsiNonnegative) :
    SuzukiShiftedEventualCriterion :=
  fun ω => xiZeroFreeRightOf_iff_shiftedEventuallyNonnegative_of_bridge
    hbridge ω

end RHGarden
