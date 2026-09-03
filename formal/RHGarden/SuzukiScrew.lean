import RHGarden.LiWeilInfinite

noncomputable section

open Complex Filter Set
open scoped Topology ComplexConjugate

namespace RHGarden

/-- The zero coordinate used by Suzuki: if `ρ` is an xi zero, then
`ρ = 1/2 - I * γ`.  It is not assumed to be real. -/
noncomputable def xiSpectralParameter (a : XiZeroOccurrence) : ℂ :=
  Complex.I * (a.value - (1 / 2 : ℂ))

theorem xiZero_eq_half_sub_I_mul_spectral (a : XiZeroOccurrence) :
    a.value = (1 / 2 : ℂ) - Complex.I * xiSpectralParameter a := by
  rw [xiSpectralParameter]
  rw [← mul_assoc, I_mul_I]
  ring

theorem riemannXi_half_sub_I_mul_spectral_eq_zero
    (a : XiZeroOccurrence) :
    riemannXi ((1 / 2 : ℂ) - Complex.I * xiSpectralParameter a) = 0 := by
  rw [← xiZero_eq_half_sub_I_mul_spectral a]
  exact a.1.xi_eq_zero

/-- The local nonvanishing statement needed to interpret every Suzuki
denominator literally. It is discharged unconditionally in
`RHGarden.XiMidpoint`. -/
def XiMidpointNonzero : Prop :=
  riemannXi (1 / 2 : ℂ) ≠ 0

theorem xiSpectralParameter_ne_zero_iff_value_ne_half
    (a : XiZeroOccurrence) :
    xiSpectralParameter a ≠ 0 ↔ a.value ≠ (1 / 2 : ℂ) := by
  simp only [xiSpectralParameter, ne_eq, mul_eq_zero, I_ne_zero,
    false_or, sub_eq_zero]

theorem xiSpectralParameter_ne_zero_of_midpoint
    (hmid : XiMidpointNonzero) (a : XiZeroOccurrence) :
    xiSpectralParameter a ≠ 0 := by
  rw [xiSpectralParameter_ne_zero_iff_value_ne_half]
  intro ha
  apply hmid
  rw [← ha]
  exact a.1.xi_eq_zero

@[simp] theorem xiSpectralParameter_re (a : XiZeroOccurrence) :
    (xiSpectralParameter a).re = -a.value.im := by
  simp [xiSpectralParameter, Complex.mul_re]

@[simp] theorem xiSpectralParameter_im (a : XiZeroOccurrence) :
    (xiSpectralParameter a).im = a.value.re - 1 / 2 := by
  simp [xiSpectralParameter, Complex.mul_im]

theorem xiSpectralParameter_im_eq_zero_iff (a : XiZeroOccurrence) :
    (xiSpectralParameter a).im = 0 ↔ a.value.re = 1 / 2 := by
  rw [xiSpectralParameter_im]
  constructor <;> intro h <;> linarith

private theorem xiZero_multiplicity_pos (ρ : XiZero) :
    0 < xiMultiplicity (ρ : ℂ) := by
  have hne : xiDivisor (ρ : ℂ) ≠ 0 := ρ.property
  have hcast := xiMultiplicity_cast (ρ : ℂ)
  by_contra hnot
  have hz : xiMultiplicity (ρ : ℂ) = 0 := Nat.eq_zero_of_not_pos hnot
  apply hne
  rw [← hcast, hz]
  norm_num

/-- Reality of every Suzuki spectral parameter is exactly the existing
critical-line zero proposition. -/
theorem xiTZerosReal_iff_spectralParameters_real :
    XiTZerosReal ↔
      ∀ a : XiZeroOccurrence, (xiSpectralParameter a).im = 0 := by
  constructor
  · intro h a
    have ht : XiT (-xiSpectralParameter a) = 0 := by
      simpa [XiT, sub_eq_add_neg] using
        riemannXi_half_sub_I_mul_spectral_eq_zero a
    have him := h (-xiSpectralParameter a) ht
    simpa using neg_eq_zero.mp him
  · intro h t ht
    let ρ : XiZero :=
      ⟨(1 / 2 : ℂ) + Complex.I * t, by
        rw [mem_xiDivisor_support_iff]
        simpa only [XiT] using ht⟩
    let a : XiZeroOccurrence :=
      ⟨ρ, ⟨0, xiZero_multiplicity_pos ρ⟩⟩
    have ha := h a
    have hgamma : xiSpectralParameter a = -t := by
      change Complex.I * ((1 / 2 : ℂ) + Complex.I * t - 1 / 2) = -t
      rw [show (1 / 2 : ℂ) + Complex.I * t - 1 / 2 = Complex.I * t by ring]
      rw [← mul_assoc, I_mul_I]
      ring
    rw [hgamma] at ha
    simpa using ha

@[simp] theorem norm_xiSpectralParameter (a : XiZeroOccurrence) :
    ‖xiSpectralParameter a‖ = ‖a.value - (1 / 2 : ℂ)‖ := by
  rw [xiSpectralParameter, norm_mul, norm_I, one_mul]

theorem half_norm_value_le_norm_xiSpectralParameter
    (a : XiZeroOccurrence) (ha : 1 ≤ ‖a.value‖) :
    ‖a.value‖ / 2 ≤ ‖xiSpectralParameter a‖ := by
  rw [norm_xiSpectralParameter]
  have htri := norm_sub_norm_le a.value (1 / 2 : ℂ)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf] at htri
  linarith

/-- Reciprocal-square summability survives the affine spectral-coordinate
change.  The proof is a cofinite comparison with the already certified
occurrence reciprocal-square series, so it does not repeat zero counting. -/
theorem xiSpectral_reciprocal_sq_summable :
    Summable (fun a : XiZeroOccurrence =>
      1 / ‖xiSpectralParameter a‖ ^ 2) := by
  let u : XiZeroOccurrence → ℝ := fun a =>
    4 * (1 / ‖a.value‖ ^ 2)
  have hu : Summable u :=
    xiOccurrence_reciprocal_sq_summable.mul_left 4
  refine Summable.of_norm_bounded_eventually hu ?_
  have htend := xiOccurrence_reciprocal_sq_summable.tendsto_cofinite_zero
  have hevent : ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
      1 / ‖a.value‖ ^ 2 < (1 / 4 : ℝ) :=
    htend.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hevent] with a ha
  have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
  have haNorm : 2 ≤ ‖a.value‖ := by
    by_contra hnot
    have halt : ‖a.value‖ < 2 := lt_of_not_ge hnot
    have hsq : ‖a.value‖ ^ 2 < 4 := by
      nlinarith [sq_nonneg ‖a.value‖]
    have hinv : (1 / 4 : ℝ) < 1 / ‖a.value‖ ^ 2 :=
      one_div_lt_one_div_of_lt (sq_pos_of_pos hapos) hsq
    exact (not_lt_of_ge hinv.le) ha
  have hgamma : ‖a.value‖ / 2 ≤ ‖xiSpectralParameter a‖ :=
    half_norm_value_le_norm_xiSpectralParameter a (by linarith)
  have hgammaPos : 0 < ‖xiSpectralParameter a‖ :=
    lt_of_lt_of_le (div_pos hapos (by norm_num)) hgamma
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / ‖xiSpectralParameter a‖ ^ 2)]
  change 1 / ‖xiSpectralParameter a‖ ^ 2 ≤
    4 * (1 / ‖a.value‖ ^ 2)
  have hsq : (‖a.value‖ / 2) ^ 2 ≤ ‖xiSpectralParameter a‖ ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by norm_num)) hgamma 2
  calc
    1 / ‖xiSpectralParameter a‖ ^ 2 ≤ 1 / (‖a.value‖ / 2) ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hapos (by norm_num))) hsq
    _ = 4 * (1 / ‖a.value‖ ^ 2) := by
      field_simp [ne_of_gt hapos]
      norm_num
    _ = u a := rfl

theorem abs_xiSpectralParameter_im_le_half (a : XiZeroOccurrence) :
    |(xiSpectralParameter a).im| ≤ 1 / 2 := by
  rw [xiSpectralParameter_im]
  change |(a.1 : ℂ).re - 1 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith [a.1.re_mem_Ioo.1, a.1.re_mem_Ioo.2]

theorem norm_exp_I_mul_xiSpectralParameter_mul_real_le
    (a : XiZeroOccurrence) (t : ℝ) :
    ‖Complex.exp (Complex.I * xiSpectralParameter a * (t : ℂ))‖ ≤
      Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * xiSpectralParameter a * (t : ℂ)).re =
      -(xiSpectralParameter a).im * t := by
    simp [Complex.mul_re]
  rw [hre]
  calc
    -(xiSpectralParameter a).im * t ≤
        |-(xiSpectralParameter a).im * t| := le_abs_self _
    _ = |(xiSpectralParameter a).im| * |t| := by rw [abs_mul, abs_neg]
    _ ≤ (1 / 2) * |t| :=
      mul_le_mul_of_nonneg_right (abs_xiSpectralParameter_im_le_half a) (abs_nonneg t)
    _ = |t| / 2 := by ring

/-- One occurrence contribution to Suzuki's zero-side function. -/
def suzukiPsiZeroTerm (t : ℝ) (a : XiZeroOccurrence) : ℂ :=
  (1 - Complex.exp
      (Complex.I * xiSpectralParameter a * (t : ℂ))) /
    xiSpectralParameter a ^ 2

theorem norm_suzukiPsiZeroTerm_le (t : ℝ) (a : XiZeroOccurrence) :
    ‖suzukiPsiZeroTerm t a‖ ≤
      (1 + Real.exp (|t| / 2)) *
        (1 / ‖xiSpectralParameter a‖ ^ 2) := by
  rw [suzukiPsiZeroTerm, norm_div, norm_pow]
  have hnum : ‖(1 : ℂ) - Complex.exp
      (Complex.I * xiSpectralParameter a * (t : ℂ))‖ ≤
      1 + Real.exp (|t| / 2) := by
    calc
      ‖(1 : ℂ) - Complex.exp
          (Complex.I * xiSpectralParameter a * (t : ℂ))‖ ≤
          ‖(1 : ℂ)‖ + ‖Complex.exp
            (Complex.I * xiSpectralParameter a * (t : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 + Real.exp (|t| / 2) := by
        simpa using add_le_add_left
          (norm_exp_I_mul_xiSpectralParameter_mul_real_le a t) 1
  calc
    ‖(1 : ℂ) - Complex.exp
        (Complex.I * xiSpectralParameter a * (t : ℂ))‖ /
        ‖xiSpectralParameter a‖ ^ 2 ≤
      (1 + Real.exp (|t| / 2)) / ‖xiSpectralParameter a‖ ^ 2 := by
        exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (1 + Real.exp (|t| / 2)) *
        (1 / ‖xiSpectralParameter a‖ ^ 2) := by ring

theorem summable_suzukiPsiZero_term (t : ℝ) :
    Summable (suzukiPsiZeroTerm t) := by
  have hmajorant := xiSpectral_reciprocal_sq_summable.mul_left
    (1 + Real.exp (|t| / 2))
  exact Summable.of_norm_bounded hmajorant
    (norm_suzukiPsiZeroTerm_le t)

/-- Suzuki's occurrence-indexed zero expansion
`Σγ (1 - exp (i γ t)) / γ²`. -/
noncomputable def suzukiPsiZero (t : ℝ) : ℂ :=
  ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a

@[simp] theorem suzukiPsiZero_zero : suzukiPsiZero 0 = 0 := by
  simp [suzukiPsiZero, suzukiPsiZeroTerm]

private noncomputable def xiZeroConjEquiv : XiZero ≃ XiZero where
  toFun ρ := ⟨starRingEnd ℂ (ρ : ℂ), by
    rw [mem_xiDivisor_support_iff, riemannXi_conj, ρ.xi_eq_zero, map_zero]⟩
  invFun ρ := ⟨starRingEnd ℂ (ρ : ℂ), by
    rw [mem_xiDivisor_support_iff, riemannXi_conj, ρ.xi_eq_zero, map_zero]⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

private noncomputable def xiZeroOneSubEquiv : XiZero ≃ XiZero where
  toFun ρ := ⟨1 - (ρ : ℂ), by
    rw [mem_xiDivisor_support_iff, riemannXi_one_sub, ρ.xi_eq_zero]⟩
  invFun ρ := ⟨1 - (ρ : ℂ), by
    rw [mem_xiDivisor_support_iff, riemannXi_one_sub, ρ.xi_eq_zero]⟩
  left_inv ρ := by ext; simp
  right_inv ρ := by ext; simp

private noncomputable def xiOccurrenceConjEquiv :
    XiZeroOccurrence ≃ XiZeroOccurrence :=
  xiZeroConjEquiv.sigmaCongr fun ρ =>
    Equiv.cast (congrArg Fin (xiMultiplicity_conj (ρ : ℂ)).symm)

private noncomputable def xiOccurrenceOneSubEquiv :
    XiZeroOccurrence ≃ XiZeroOccurrence :=
  xiZeroOneSubEquiv.sigmaCongr fun ρ =>
    Equiv.cast (congrArg Fin (xiMultiplicity_one_sub (ρ : ℂ)).symm)

@[simp] private theorem xiOccurrenceConjEquiv_value (a : XiZeroOccurrence) :
    (xiOccurrenceConjEquiv a).value = starRingEnd ℂ a.value := rfl

@[simp] private theorem xiOccurrenceOneSubEquiv_value (a : XiZeroOccurrence) :
    (xiOccurrenceOneSubEquiv a).value = 1 - a.value := rfl

@[simp] theorem xiSpectralParameter_conjOccurrence (a : XiZeroOccurrence) :
    xiSpectralParameter (xiOccurrenceConjEquiv a) =
      -starRingEnd ℂ (xiSpectralParameter a) := by
  apply Complex.ext <;> simp

@[simp] theorem xiSpectralParameter_oneSubOccurrence (a : XiZeroOccurrence) :
    xiSpectralParameter (xiOccurrenceOneSubEquiv a) =
      -xiSpectralParameter a := by
  apply Complex.ext <;> simp
  linarith

private theorem conj_suzukiPsiZeroTerm (t : ℝ) (a : XiZeroOccurrence) :
    starRingEnd ℂ (suzukiPsiZeroTerm t a) =
      suzukiPsiZeroTerm t (xiOccurrenceConjEquiv a) := by
  rw [suzukiPsiZeroTerm, suzukiPsiZeroTerm, map_div₀, map_sub, map_one,
    map_pow, ← Complex.exp_conj, xiSpectralParameter_conjOccurrence]
  have hden : starRingEnd ℂ (xiSpectralParameter a) ^ 2 =
      (-starRingEnd ℂ (xiSpectralParameter a)) ^ 2 := by ring
  rw [← hden]
  congr 1
  simp

private theorem suzukiPsiZeroTerm_neg (t : ℝ) (a : XiZeroOccurrence) :
    suzukiPsiZeroTerm (-t) a =
      suzukiPsiZeroTerm t (xiOccurrenceOneSubEquiv a) := by
  rw [suzukiPsiZeroTerm, suzukiPsiZeroTerm,
    xiSpectralParameter_oneSubOccurrence]
  have hden : xiSpectralParameter a ^ 2 =
      (-xiSpectralParameter a) ^ 2 := by ring
  rw [← hden]
  congr 1
  push_cast
  ring

theorem suzukiPsiZero_conj (t : ℝ) :
    starRingEnd ℂ (suzukiPsiZero t) = suzukiPsiZero t := by
  rw [suzukiPsiZero, Complex.conj_tsum]
  calc
    ∑' a : XiZeroOccurrence, starRingEnd ℂ (suzukiPsiZeroTerm t a) =
        ∑' a : XiZeroOccurrence,
          suzukiPsiZeroTerm t (xiOccurrenceConjEquiv a) := by
            apply tsum_congr
            exact conj_suzukiPsiZeroTerm t
    _ = ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a :=
      xiOccurrenceConjEquiv.tsum_eq (suzukiPsiZeroTerm t)

theorem suzukiPsiZero_neg (t : ℝ) :
    suzukiPsiZero (-t) = suzukiPsiZero t := by
  rw [suzukiPsiZero, suzukiPsiZero]
  calc
    ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm (-t) a =
        ∑' a : XiZeroOccurrence,
          suzukiPsiZeroTerm t (xiOccurrenceOneSubEquiv a) := by
            apply tsum_congr
            exact suzukiPsiZeroTerm_neg t
    _ = ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a :=
      xiOccurrenceOneSubEquiv.tsum_eq (suzukiPsiZeroTerm t)

/-- The real-valued form of Suzuki's zero-side function. -/
noncomputable def suzukiPsi (t : ℝ) : ℝ :=
  (suzukiPsiZero t).re

theorem ofReal_suzukiPsi (t : ℝ) :
    (suzukiPsi t : ℂ) = suzukiPsiZero t := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact (Complex.conj_eq_iff_im.mp (suzukiPsiZero_conj t)).symm

@[simp] theorem suzukiPsi_zero : suzukiPsi 0 = 0 := by
  simp [suzukiPsi]

theorem suzukiPsi_neg (t : ℝ) : suzukiPsi (-t) = suzukiPsi t := by
  rw [suzukiPsi, suzukiPsi, suzukiPsiZero_neg]

/-- Suzuki's Riemann screw function, with the sign convention `g = -Ψ`. -/
noncomputable def riemannScrew (t : ℝ) : ℝ :=
  -suzukiPsi t

/-- The translation-difference kernel attached to the Riemann screw
function. -/
noncomputable def riemannScrewKernel (t u : ℝ) : ℂ :=
  (riemannScrew (t - u) : ℂ) - riemannScrew t -
    riemannScrew (-u) + riemannScrew 0

@[simp] theorem riemannScrew_zero : riemannScrew 0 = 0 := by
  simp [riemannScrew]

theorem riemannScrew_even (t : ℝ) : riemannScrew (-t) = riemannScrew t := by
  rw [riemannScrew, riemannScrew, suzukiPsi_neg]

theorem riemannScrewKernel_hermitian (t u : ℝ) :
    starRingEnd ℂ (riemannScrewKernel t u) =
      riemannScrewKernel u t := by
  have hsub : riemannScrew (t - u) = riemannScrew (u - t) := by
    rw [← riemannScrew_even (t - u)]
    congr 1
    ring
  have hsym : riemannScrewKernel t u = riemannScrewKernel u t := by
    rw [riemannScrewKernel, riemannScrewKernel, riemannScrew_even u,
      riemannScrew_even t, hsub]
    ring
  rw [← hsym]
  apply Complex.ext <;> simp [riemannScrewKernel]

/-- One spectral contribution to Suzuki's zero-side screw kernel. -/
def suzukiKernelTerm (t u : ℝ) (a : XiZeroOccurrence) : ℂ :=
  ((Complex.exp
      (Complex.I * xiSpectralParameter a * (t : ℂ)) - 1) *
    (Complex.exp
      (-Complex.I * xiSpectralParameter a * (u : ℂ)) - 1)) /
    xiSpectralParameter a ^ 2

private theorem exp_spectral_sub (a : XiZeroOccurrence) (t u : ℝ) :
    Complex.exp
        (Complex.I * xiSpectralParameter a * ((t - u : ℝ) : ℂ)) =
      Complex.exp
          (Complex.I * xiSpectralParameter a * (t : ℂ)) *
        Complex.exp
          (-Complex.I * xiSpectralParameter a * (u : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem suzukiKernelTerm_eq_psi_combination
    (t u : ℝ) (a : XiZeroOccurrence) :
    suzukiKernelTerm t u a =
      -suzukiPsiZeroTerm (t - u) a +
        suzukiPsiZeroTerm t a + suzukiPsiZeroTerm (-u) a := by
  rw [suzukiKernelTerm, suzukiPsiZeroTerm, suzukiPsiZeroTerm,
    suzukiPsiZeroTerm, exp_spectral_sub]
  have hneg : Complex.exp
      (Complex.I * xiSpectralParameter a * ((-u : ℝ) : ℂ)) =
      Complex.exp
        (-Complex.I * xiSpectralParameter a * (u : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hneg]
  ring

theorem summable_suzukiKernelTerm (t u : ℝ) :
    Summable (suzukiKernelTerm t u) := by
  have h := ((summable_suzukiPsiZero_term (t - u)).neg.add
    (summable_suzukiPsiZero_term t)).add
      (summable_suzukiPsiZero_term (-u))
  exact h.congr fun a => (suzukiKernelTerm_eq_psi_combination t u a).symm

/-- Suzuki's zero-side algebra (equation (1.9)), indexed by analytic
occurrences of xi zeros. `RHGarden.XiMidpoint` proves unconditionally that all
the spectral denominators occurring here are nonzero. -/
theorem riemannScrewKernel_eq_zero_sum (t u : ℝ) :
    riemannScrewKernel t u =
      ∑' a : XiZeroOccurrence, suzukiKernelTerm t u a := by
  rw [riemannScrewKernel, riemannScrew, riemannScrew, riemannScrew,
    riemannScrew]
  simp only [suzukiPsi_zero, neg_zero, ofReal_zero, add_zero]
  push_cast
  rw [ofReal_suzukiPsi, ofReal_suzukiPsi, ofReal_suzukiPsi,
    suzukiPsiZero, suzukiPsiZero, suzukiPsiZero]
  simp only [sub_neg_eq_add]
  rw [← tsum_neg]
  rw [← (summable_suzukiPsiZero_term (t - u)).neg.tsum_add
    (summable_suzukiPsiZero_term t)]
  rw [← ((summable_suzukiPsiZero_term (t - u)).neg.add
    (summable_suzukiPsiZero_term t)).tsum_add
      (summable_suzukiPsiZero_term (-u))]
  apply tsum_congr
  intro a
  exact (suzukiKernelTerm_eq_psi_combination t u a).symm

/-- The spectral feature whose outer products give the screw kernel when the
spectral coordinate is real. -/
def suzukiFeature (a : XiZeroOccurrence) (t : ℝ) : ℂ :=
  (Complex.exp
      (Complex.I * xiSpectralParameter a * (t : ℂ)) - 1) /
    xiSpectralParameter a

theorem xiSpectralParameter_star_eq_of_XiTZerosReal
    (hRH : XiTZerosReal) (a : XiZeroOccurrence) :
    starRingEnd ℂ (xiSpectralParameter a) = xiSpectralParameter a := by
  exact Complex.conj_eq_iff_im.mpr
    ((xiTZerosReal_iff_spectralParameters_real.mp hRH) a)

private theorem conj_suzukiFeature_of_XiTZerosReal
    (hRH : XiTZerosReal) (a : XiZeroOccurrence) (t : ℝ) :
    starRingEnd ℂ (suzukiFeature a t) =
      (Complex.exp
          (-Complex.I * xiSpectralParameter a * (t : ℂ)) - 1) /
        xiSpectralParameter a := by
  rw [suzukiFeature, map_div₀, map_sub, map_one, ← Complex.exp_conj,
    xiSpectralParameter_star_eq_of_XiTZerosReal hRH a]
  have hexp : starRingEnd ℂ
      (Complex.I * xiSpectralParameter a * (t : ℂ)) =
      -Complex.I * xiSpectralParameter a * (t : ℂ) := by
    rw [map_mul, map_mul,
      xiSpectralParameter_star_eq_of_XiTZerosReal hRH a]
    simp
  rw [hexp]

theorem suzukiKernelTerm_eq_feature_mul_conj_of_XiTZerosReal
    (hRH : XiTZerosReal) (t u : ℝ) (a : XiZeroOccurrence) :
    suzukiKernelTerm t u a =
      suzukiFeature a t * starRingEnd ℂ (suzukiFeature a u) := by
  rw [suzukiKernelTerm,
    conj_suzukiFeature_of_XiTZerosReal hRH, suzukiFeature]
  simp only [div_eq_mul_inv]
  ring

/-- On the critical line Suzuki's zero-side expansion is an explicit Gram
sum.  This is the unique point where the RH-side hypothesis enters. -/
theorem riemannScrewKernel_eq_gram_of_XiTZerosReal
    (hRH : XiTZerosReal) (t u : ℝ) :
    riemannScrewKernel t u =
      ∑' a : XiZeroOccurrence,
        suzukiFeature a t * starRingEnd ℂ (suzukiFeature a u) := by
  rw [riemannScrewKernel_eq_zero_sum]
  apply tsum_congr
  exact suzukiKernelTerm_eq_feature_mul_conj_of_XiTZerosReal hRH t u

/-- The finite-height truncation of Suzuki's zero-side kernel. -/
noncomputable def riemannScrewKernelHeight (T t u : ℝ) : ℂ :=
  ∑ a ∈ xiOccurrenceHeightFinset T, suzukiKernelTerm t u a

theorem riemannScrewKernelHeight_tendsto (t u : ℝ) :
    Tendsto (fun T : ℝ => riemannScrewKernelHeight T t u)
      atTop (nhds (riemannScrewKernel t u)) := by
  rw [riemannScrewKernel_eq_zero_sum]
  exact tendsto_heightCutoff_sum_of_summable
    (summable_suzukiKernelTerm t u)

/-- Positive semidefiniteness of all finite matrices sampled from a complex
kernel. -/
def KernelPSD (K : ℝ → ℝ → ℂ) : Prop :=
  ∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ),
    0 ≤ (∑ i, ∑ j,
      K (t i) (t j) * c i * starRingEnd ℂ (c j)).re

private theorem feature_double_sum_eq_normSq
    (a : XiZeroOccurrence) (N : ℕ)
    (t : Fin N → ℝ) (c : Fin N → ℂ) :
    (∑ i, ∑ j,
        (suzukiFeature a (t i) *
          starRingEnd ℂ (suzukiFeature a (t j))) *
          c i * starRingEnd ℂ (c j)) =
      (Complex.normSq
        (∑ i, suzukiFeature a (t i) * c i) : ℂ) := by
  rw [← Complex.mul_conj]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

private theorem feature_double_sum_re_nonneg
    (a : XiZeroOccurrence) (N : ℕ)
    (t : Fin N → ℝ) (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j,
        (suzukiFeature a (t i) *
          starRingEnd ℂ (suzukiFeature a (t j))) *
          c i * starRingEnd ℂ (c j)).re := by
  rw [feature_double_sum_eq_normSq]
  simp only [ofReal_re]
  exact Complex.normSq_nonneg _

private theorem kernelPSD_finset_sum
    {ι : Type*} (F : Finset ι) (K : ι → ℝ → ℝ → ℂ)
    (hK : ∀ a ∈ F, KernelPSD (K a)) :
    KernelPSD (fun t u => ∑ a ∈ F, K a t u) := by
  intro N t c
  have hrearrange :
      (∑ i, ∑ j,
          (∑ a ∈ F, K a (t i) (t j)) * c i *
            starRingEnd ℂ (c j)) =
        ∑ a ∈ F, ∑ i, ∑ j,
          K a (t i) (t j) * c i * starRingEnd ℂ (c j) := by
    simp_rw [Finset.sum_mul]
    calc
      (∑ i, ∑ j, ∑ a ∈ F,
          K a (t i) (t j) * c i * starRingEnd ℂ (c j)) =
          ∑ i, ∑ a ∈ F, ∑ j,
            K a (t i) (t j) * c i * starRingEnd ℂ (c j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
      _ = ∑ a ∈ F, ∑ i, ∑ j,
          K a (t i) (t j) * c i * starRingEnd ℂ (c j) := by
            rw [Finset.sum_comm]
  rw [hrearrange, Complex.re_sum]
  exact Finset.sum_nonneg fun a ha => hK a ha N t c

theorem riemannScrewKernelHeight_psd_of_XiTZerosReal
    (hRH : XiTZerosReal) (T : ℝ) :
    KernelPSD (riemannScrewKernelHeight T) := by
  unfold riemannScrewKernelHeight
  apply kernelPSD_finset_sum
  intro a ha N t c
  simp_rw [suzukiKernelTerm_eq_feature_mul_conj_of_XiTZerosReal hRH]
  exact feature_double_sum_re_nonneg a N t c

theorem riemannScrewKernel_psd_of_XiTZerosReal :
    XiTZerosReal → KernelPSD riemannScrewKernel := by
  intro hRH N t c
  have hcomplex : Tendsto
      (fun T : ℝ => ∑ i, ∑ j,
        riemannScrewKernelHeight T (t i) (t j) * c i *
          starRingEnd ℂ (c j))
      atTop
      (nhds (∑ i, ∑ j,
        riemannScrewKernel (t i) (t j) * c i *
          starRingEnd ℂ (c j))) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact ((riemannScrewKernelHeight_tendsto (t i) (t j)).mul
      tendsto_const_nhds).mul tendsto_const_nhds
  have hreal : Tendsto
      (fun T : ℝ => (∑ i, ∑ j,
        riemannScrewKernelHeight T (t i) (t j) * c i *
          starRingEnd ℂ (c j)).re)
      atTop
      (nhds (∑ i, ∑ j,
        riemannScrewKernel (t i) (t j) * c i *
          starRingEnd ℂ (c j)).re) :=
    (Complex.continuous_re.tendsto _).comp hcomplex
  exact ge_of_tendsto hreal (Filter.Eventually.of_forall fun T =>
    riemannScrewKernelHeight_psd_of_XiTZerosReal hRH T N t c)

end RHGarden
