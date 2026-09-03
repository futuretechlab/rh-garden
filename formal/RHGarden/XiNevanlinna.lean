import RHGarden.XiMidpoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Complex Filter Set
open scoped Topology ComplexConjugate

namespace RHGarden

/-- The Lagarias--Suzuki Nevanlinna function attached to the centered xi
function. -/
noncomputable def xiNevanlinnaQ (z : ℂ) : ℂ :=
  Complex.I * logDeriv riemannXi ((1 / 2 : ℂ) - Complex.I * z)

/-- The minimal upper-half-plane Nevanlinna property used in RH Garden. -/
def IsNevanlinnaUpper (Q : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ Q {z : ℂ | 0 < z.im} ∧
    ∀ z : ℂ, 0 < z.im → 0 ≤ (Q z).im

/-- The xi Nevanlinna criterion.  This is a representation proposition, not
an assertion of RH. -/
def XiNevanlinna : Prop := IsNevanlinnaUpper xiNevanlinnaQ

theorem deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hderiv := congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  have hcomp : deriv (fun z : ℂ => riemannXi (1 - z)) s =
      -deriv riemannXi (1 - s) := by
    change deriv (riemannXi ∘ fun z : ℂ => 1 - z) s = _
    rw [deriv_comp s differentiable_riemannXi.differentiableAt (by fun_prop)]
    simp
  rw [hcomp] at hderiv
  calc
    deriv riemannXi (1 - s) = -(-deriv riemannXi (1 - s)) := by ring
    _ = -deriv riemannXi s := congrArg Neg.neg hderiv

theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub,
    riemannXi_one_sub]
  ring

theorem logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv riemannXi (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv riemannXi s) := by
  have hder := iteratedDeriv_riemannXi_conj 1 s
  simp only [iteratedDeriv_one] at hder
  rw [logDeriv_apply, logDeriv_apply, hder, riemannXi_conj, map_div₀]

/-- The centered Nevanlinna function commutes with conjugation. -/
theorem xiNevanlinnaQ_conj (z : ℂ) :
    xiNevanlinnaQ (starRingEnd ℂ z) =
      starRingEnd ℂ (xiNevanlinnaQ z) := by
  rw [xiNevanlinnaQ, xiNevanlinnaQ, map_mul,
    ← logDeriv_riemannXi_conj]
  have harg : starRingEnd ℂ ((1 / 2 : ℂ) - Complex.I * z) =
      1 - ((1 / 2 : ℂ) - Complex.I * starRingEnd ℂ z) := by
    apply Complex.ext <;> norm_num <;> ring
  rw [harg, logDeriv_riemannXi_one_sub]
  have hcI : starRingEnd ℂ Complex.I = -Complex.I := by simp
  rw [hcI]
  ring

/-- The xi logarithmic derivative vanishes at the center of its functional
equation. -/
theorem logDeriv_riemannXi_half_eq_zero :
    logDeriv riemannXi (1 / 2 : ℂ) = 0 := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hderiv := congrArg (fun f : ℂ → ℂ => deriv f (1 / 2 : ℂ)) hfun
  have hcomp :
      deriv (fun z : ℂ => riemannXi (1 - z)) (1 / 2 : ℂ) =
        -deriv riemannXi (1 / 2 : ℂ) := by
    change deriv (riemannXi ∘ fun z : ℂ => 1 - z) (1 / 2 : ℂ) = _
    rw [deriv_comp (1 / 2 : ℂ) differentiable_riemannXi.differentiableAt
      (by fun_prop)]
    norm_num
  rw [hcomp] at hderiv
  have hd : deriv riemannXi (1 / 2 : ℂ) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hderiv
  rw [logDeriv_apply, hd, zero_div]

/-- The absolutely convergent centered spectral fraction. -/
def xiSpectralCorrectedTerm (z : ℂ) (a : XiZeroOccurrence) : ℂ :=
  1 / (xiSpectralParameter a - z) - 1 / xiSpectralParameter a

private def xiCenteredCorrectedTerm (s : ℂ) (a : XiZeroOccurrence) : ℂ :=
  1 / (s - a.value) + 1 / a.value

private theorem spectral_corrected_eq_centered_xi_fraction
    {z : ℂ} (a : XiZeroOccurrence)
    (hz : riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0) :
    xiSpectralCorrectedTerm z a =
      Complex.I *
        (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a -
          xiCenteredCorrectedTerm (1 / 2 : ℂ) a) := by
  have hγ : xiSpectralParameter a ≠ 0 := xiSpectralParameter_ne_zero a
  have hγz : xiSpectralParameter a - z ≠ 0 := by
    intro h
    have heq : z = xiSpectralParameter a := by
      exact (sub_eq_zero.mp h).symm
    apply hz
    rw [heq]
    exact riemannXi_half_sub_I_mul_spectral_eq_zero a
  rw [xiSpectralCorrectedTerm]
  simp only [xiCenteredCorrectedTerm]
  rw [xiZero_eq_half_sub_I_mul_spectral a]
  rw [show (1 / 2 : ℂ) - Complex.I * z -
      (1 / 2 - Complex.I * xiSpectralParameter a) =
        Complex.I * (xiSpectralParameter a - z) by ring]
  rw [show (1 / 2 : ℂ) -
      (1 / 2 - Complex.I * xiSpectralParameter a) =
        Complex.I * xiSpectralParameter a by ring]
  have hI : Complex.I ≠ 0 := I_ne_zero
  field_simp [hI, hγ, hγz]
  ring_nf

theorem summable_xiSpectralCorrectedTerm {z : ℂ}
    (hz : riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0) :
    Summable (xiSpectralCorrectedTerm z) := by
  have hs : Summable
      (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z)) := by
    have h := summable_logDeriv_xiOccurrencePrimaryFactor hz
    exact h.congr fun a => by
      rw [xiCenteredCorrectedTerm]
      exact logDeriv_xiOccurrencePrimaryFactor (by
      intro heq
      apply hz
      rw [heq]
      exact a.1.xi_eq_zero)
  have hh : Summable (xiCenteredCorrectedTerm (1 / 2 : ℂ)) := by
    have h := summable_logDeriv_xiOccurrencePrimaryFactor
      riemannXi_half_ne_zero
    exact h.congr fun a => by
      rw [xiCenteredCorrectedTerm]
      exact logDeriv_xiOccurrencePrimaryFactor (by
      intro heq
      apply riemannXi_half_ne_zero
      rw [heq]
      exact a.1.xi_eq_zero)
  exact ((hs.sub hh).mul_left Complex.I).congr fun a =>
    (spectral_corrected_eq_centered_xi_fraction a hz).symm

/-- The exact centered xi partial fraction.  The subtraction by `1/γ` is
essential: it is what makes the occurrence-indexed series absolutely
convergent. -/
theorem xiNevanlinnaQ_eq_spectral_sum {z : ℂ}
    (hz : riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0) :
    xiNevanlinnaQ z =
      ∑' a : XiZeroOccurrence, xiSpectralCorrectedTerm z a := by
  have hs : Summable
      (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z)) := by
    have hsum := summable_logDeriv_xiOccurrencePrimaryFactor hz
    exact hsum.congr fun a => by
      rw [xiCenteredCorrectedTerm]
      exact logDeriv_xiOccurrencePrimaryFactor (by
      intro heq
      apply hz
      rw [heq]
      exact a.1.xi_eq_zero)
  have hh : Summable (xiCenteredCorrectedTerm (1 / 2 : ℂ)) := by
    have hsum := summable_logDeriv_xiOccurrencePrimaryFactor
      riemannXi_half_ne_zero
    exact hsum.congr fun a => by
      rw [xiCenteredCorrectedTerm]
      exact logDeriv_xiOccurrencePrimaryFactor (by
      intro heq
      apply riemannXi_half_ne_zero
      rw [heq]
      exact a.1.xi_eq_zero)
  have hpfs := logDeriv_riemannXi_eq_zero_value_add_zero_sum hz
  have hpfh := logDeriv_riemannXi_eq_zero_value_add_zero_sum
    riemannXi_half_ne_zero
  change logDeriv riemannXi (1 / 2 - Complex.I * z) =
      logDeriv riemannXi 0 +
        ∑' a : XiZeroOccurrence,
          xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a at hpfs
  change logDeriv riemannXi (1 / 2 : ℂ) =
      logDeriv riemannXi 0 +
        ∑' a : XiZeroOccurrence, xiCenteredCorrectedTerm (1 / 2 : ℂ) a at hpfh
  have hdiff :
      logDeriv riemannXi ((1 / 2 : ℂ) - Complex.I * z) -
          logDeriv riemannXi (1 / 2 : ℂ) =
        ∑' a : XiZeroOccurrence,
          (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a -
            xiCenteredCorrectedTerm (1 / 2 : ℂ) a) := by
    calc
      logDeriv riemannXi ((1 / 2 : ℂ) - Complex.I * z) -
          logDeriv riemannXi (1 / 2 : ℂ) =
        (logDeriv riemannXi 0 +
            ∑' a : XiZeroOccurrence,
              xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a) -
          (logDeriv riemannXi 0 +
            ∑' a : XiZeroOccurrence,
              xiCenteredCorrectedTerm (1 / 2 : ℂ) a) :=
        congrArg₂ (· - ·) hpfs hpfh
      _ = (∑' a : XiZeroOccurrence,
              xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a) -
            ∑' a : XiZeroOccurrence,
              xiCenteredCorrectedTerm (1 / 2 : ℂ) a := by ring
      _ = ∑' a : XiZeroOccurrence,
          (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a -
            xiCenteredCorrectedTerm (1 / 2 : ℂ) a) :=
        (hs.tsum_sub hh).symm
  calc
    xiNevanlinnaQ z = Complex.I *
        (logDeriv riemannXi ((1 / 2 : ℂ) - Complex.I * z) -
          logDeriv riemannXi (1 / 2 : ℂ)) := by
            rw [xiNevanlinnaQ, logDeriv_riemannXi_half_eq_zero, sub_zero]
    _ = Complex.I * ∑' a : XiZeroOccurrence,
        (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a -
          xiCenteredCorrectedTerm (1 / 2 : ℂ) a) := congrArg _ hdiff
    _ = ∑' a : XiZeroOccurrence, Complex.I *
        (xiCenteredCorrectedTerm ((1 / 2 : ℂ) - Complex.I * z) a -
          xiCenteredCorrectedTerm (1 / 2 : ℂ) a) :=
          ((hs.sub hh).tsum_mul_left Complex.I).symm
    _ = ∑' a : XiZeroOccurrence, xiSpectralCorrectedTerm z a := by
      apply tsum_congr
      intro a
      exact (spectral_corrected_eq_centered_xi_fraction a hz).symm

private theorem riemannXi_centered_ne_zero_of_XiTZerosReal
    (hRH : XiTZerosReal) {z : ℂ} (hz : 0 < z.im) :
    riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0 := by
  intro hzero
  have ht : XiT (-z) = 0 := by
    simpa [XiT, sub_eq_add_neg] using hzero
  have him := hRH (-z) ht
  simp only [Complex.neg_im] at him
  linarith

private theorem analyticAt_xiNevanlinnaQ_of_centered_ne_zero {z : ℂ}
    (hz : riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0) :
    AnalyticAt ℂ xiNevanlinnaQ z := by
  have hxi : AnalyticAt ℂ riemannXi
      ((1 / 2 : ℂ) - Complex.I * z) :=
    differentiable_riemannXi.analyticAt _
  have hld : AnalyticAt ℂ (logDeriv riemannXi)
      ((1 / 2 : ℂ) - Complex.I * z) := by
    rw [logDeriv]
    exact hxi.deriv.div hxi hz
  change AnalyticAt ℂ
    (fun w : ℂ => Complex.I *
      logDeriv riemannXi ((1 / 2 : ℂ) - Complex.I * w)) z
  have haff : AnalyticAt ℂ
      (fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w) z := by
    fun_prop
  have hc : AnalyticAt ℂ
      ((logDeriv riemannXi) ∘
        (fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w)) z :=
    AnalyticAt.comp
      (g := logDeriv riemannXi)
      (f := fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w) hld haff
  exact analyticAt_const.mul (by simpa [Function.comp_def] using hc)

private theorem im_xiSpectralCorrectedTerm_nonneg_of_real
    {z γ : ℂ} (hz : 0 < z.im) (hγ : γ.im = 0) :
    0 ≤ (1 / (γ - z) - 1 / γ).im := by
  rw [Complex.sub_im]
  simp only [div_eq_mul_inv, one_mul]
  rw [Complex.inv_im, Complex.inv_im]
  simp only [Complex.sub_im, hγ, zero_sub, neg_neg]
  simpa using div_nonneg hz.le (Complex.normSq_nonneg (γ - z))

private instance countableXiZeroOccurrence : Countable XiZeroOccurrence := by
  rw [← Set.countable_univ_iff]
  have hs := xiSpectral_reciprocal_sq_summable.countable_support
  have heq : Function.support (fun a : XiZeroOccurrence =>
      1 / ‖xiSpectralParameter a‖ ^ 2) = Set.univ := by
    ext a
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact one_div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (xiSpectralParameter_ne_zero a)))
  rw [heq] at hs
  exact hs

/-- Critical-line reality makes every centered spectral fraction have
nonnegative imaginary part, hence makes `Qξ` a Nevanlinna function. -/
theorem xiNevanlinna_of_XiTZerosReal :
    XiTZerosReal → XiNevanlinna := by
  intro hRH
  constructor
  · intro z hz
    exact analyticAt_xiNevanlinnaQ_of_centered_ne_zero
      (riemannXi_centered_ne_zero_of_XiTZerosReal hRH hz)
  · intro z hz
    have hnonzero := riemannXi_centered_ne_zero_of_XiTZerosReal hRH hz
    rw [xiNevanlinnaQ_eq_spectral_sum hnonzero]
    rw [Complex.im_tsum (summable_xiSpectralCorrectedTerm hnonzero)]
    exact tsum_nonneg fun a =>
      im_xiSpectralCorrectedTerm_nonneg_of_real hz
        ((xiTZerosReal_iff_spectralParameters_real.mp hRH) a)

/-- A zero of xi is a genuine pole of its logarithmic derivative.  The proof
uses analytic order, so it does not assume that the zero is simple. -/
private theorem not_analyticAt_logDeriv_riemannXi_of_zero {ρ : ℂ}
    (hρ : riemannXi ρ = 0) :
    ¬ AnalyticAt ℂ (logDeriv riemannXi) ρ := by
  intro hld
  have htop := analyticOrderAt_riemannXi_ne_top ρ
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (analyticAt_riemannXi ρ).analyticOrderAt_ne_top.mp htop
  let n : ℕ := analyticOrderNatAt riemannXi ρ
  have hn : n ≠ 0 := by
    intro hn0
    have horder : analyticOrderAt riemannXi ρ = 0 := by
      rw [show analyticOrderAt riemannXi ρ = (n : ℕ∞) by
        exact (Nat.cast_analyticOrderNatAt htop).symm, hn0]
      simp
    exact (analyticAt_riemannXi ρ).analyticOrderAt_ne_zero.mpr hρ horder
  have hg_ne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 :=
    hg.continuousAt.eventually_ne hg0
  have hfactor : ∀ᶠ s in 𝓝 ρ,
      ∀ᶠ w in 𝓝 s, riemannXi w = (w - ρ) ^ n * g w := by
    simpa only [n, smul_eq_mul] using hfg.eventually_nhds
  have hg_an : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s :=
    hg.eventually_analyticAt
  have heq : ∀ᶠ s in 𝓝[≠] ρ,
      (s - ρ) * logDeriv riemannXi s =
        (n : ℂ) + (s - ρ) * logDeriv g s := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds hfactor,
      mem_nhdsWithin_of_mem_nhds hg_ne,
      mem_nhdsWithin_of_mem_nhds hg_an]
      with s hs hfs hgs hgas
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    have hlog : logDeriv riemannXi s =
        (n : ℂ) / (s - ρ) + logDeriv g s := by
      have hsame : logDeriv riemannXi s =
          logDeriv (fun w : ℂ => (w - ρ) ^ n * g w) s := by
        have hfs' : riemannXi =ᶠ[𝓝 s]
            fun w : ℂ => (w - ρ) ^ n * g w := hfs
        simp only [logDeriv_apply, hfs'.deriv_eq, hfs'.self_of_nhds]
      rw [hsame, logDeriv_mul
        (f := fun w : ℂ => (w - ρ) ^ n) (g := g) s
        (pow_ne_zero _ hsρ) hgs (by fun_prop) hgas.differentiableAt]
      have hpow : logDeriv (fun w : ℂ => (w - ρ) ^ n) s =
          (n : ℂ) / (s - ρ) := by
        rw [show (fun w : ℂ => (w - ρ) ^ n) =
            (fun x : ℂ => x ^ n) ∘ (fun w => w - ρ) from rfl,
          logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
        simp
      rw [hpow]
    rw [hlog]
    field_simp [hsρ]
  have hleft : Tendsto
      (fun s : ℂ => (s - ρ) * logDeriv riemannXi s)
      (𝓝[≠] ρ) (𝓝 0) := by
    have hc : ContinuousAt
        (fun s : ℂ => (s - ρ) * logDeriv riemannXi s) ρ :=
      (continuousAt_id.sub continuousAt_const).mul hld.continuousAt
    have hc0 : Tendsto
        (fun s : ℂ => (s - ρ) * logDeriv riemannXi s)
        (𝓝 ρ) (𝓝 0) := by simpa using hc.tendsto
    exact hc0.mono_left nhdsWithin_le_nhds
  have hglog : ContinuousAt (logDeriv g) ρ := by
    rw [logDeriv]
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have hright : Tendsto
      (fun s : ℂ => (n : ℂ) + (s - ρ) * logDeriv g s)
      (𝓝[≠] ρ) (𝓝 (n : ℂ)) := by
    have hc : ContinuousAt
        (fun s : ℂ => (n : ℂ) + (s - ρ) * logDeriv g s) ρ :=
      continuousAt_const.add
        ((continuousAt_id.sub continuousAt_const).mul hglog)
    have hcn : Tendsto
        (fun s : ℂ => (n : ℂ) + (s - ρ) * logDeriv g s)
        (𝓝 ρ) (𝓝 (n : ℂ)) := by simpa using hc.tendsto
    exact hcn.mono_left nhdsWithin_le_nhds
  have heq' :
      (fun s : ℂ => (s - ρ) * logDeriv riemannXi s) =ᶠ[𝓝[≠] ρ]
        (fun s : ℂ => (n : ℂ) + (s - ρ) * logDeriv g s) := heq
  have hright' : Tendsto
      (fun s : ℂ => (s - ρ) * logDeriv riemannXi s)
      (𝓝[≠] ρ) (𝓝 (n : ℂ)) := hright.congr' heq'.symm
  have hzero_n : (0 : ℂ) = n := tendsto_nhds_unique hleft hright'
  have hnzero : (n : ℂ) = 0 := hzero_n.symm
  exact hn (Nat.cast_eq_zero.mp hnzero)

private theorem analyticAt_logDeriv_riemannXi_of_analyticAt_xiNevanlinnaQ
    {z : ℂ} (hQ : AnalyticAt ℂ xiNevanlinnaQ z) :
    AnalyticAt ℂ (logDeriv riemannXi)
      ((1 / 2 : ℂ) - Complex.I * z) := by
  let center : ℂ := (1 / 2 : ℂ) - Complex.I * z
  let invCoord : ℂ → ℂ := fun w => Complex.I * (w - (1 / 2 : ℂ))
  have hcoord : invCoord center = z := by
    dsimp [invCoord, center]
    rw [show (1 / 2 : ℂ) - Complex.I * z - 1 / 2 =
      -Complex.I * z by ring]
    simp [← mul_assoc]
  have hinv : AnalyticAt ℂ invCoord center := by
    dsimp [invCoord]
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w => -Complex.I * xiNevanlinnaQ (invCoord w)) center := by
    exact analyticAt_const.mul (hQ.comp_of_eq hinv hcoord)
  have hfun : (fun w => -Complex.I * xiNevanlinnaQ (invCoord w)) =
      logDeriv riemannXi := by
    funext w
    rw [xiNevanlinnaQ]
    have harg : (1 / 2 : ℂ) - Complex.I * invCoord w = w := by
      dsimp [invCoord]
      simp [← mul_assoc]
    rw [harg]
    simp [← mul_assoc]
  rw [hfun] at hcomp
  exact hcomp

private theorem xiSpectralParameter_im_nonpos_of_xiNevanlinna
    (hN : XiNevanlinna) (a : XiZeroOccurrence) :
    (xiSpectralParameter a).im ≤ 0 := by
  by_contra hnot
  have hpos : 0 < (xiSpectralParameter a).im := lt_of_not_ge hnot
  have hQ : AnalyticAt ℂ xiNevanlinnaQ (xiSpectralParameter a) :=
    hN.1 (xiSpectralParameter a) hpos
  have hld :=
    analyticAt_logDeriv_riemannXi_of_analyticAt_xiNevanlinnaQ hQ
  exact not_analyticAt_logDeriv_riemannXi_of_zero
    (riemannXi_half_sub_I_mul_spectral_eq_zero a) hld

/-- Analyticity of `Qξ` on the whole upper half-plane excludes every
nonreal spectral zero.  Reflection `γ ↦ -γ` excludes the lower half-plane. -/
theorem XiTZerosReal_of_xiNevanlinna :
    XiNevanlinna → XiTZerosReal := by
  intro hN
  rw [xiTZerosReal_iff_spectralParameters_real]
  intro a
  have hupper := xiSpectralParameter_im_nonpos_of_xiNevanlinna hN a
  have hlower := xiSpectralParameter_im_nonpos_of_xiNevanlinna hN
    (xiOccurrenceOneSubEquiv a)
  rw [xiSpectralParameter_oneSubOccurrence] at hlower
  simp only [Complex.neg_im] at hlower
  linarith

/-- The Lagarias--Suzuki Nevanlinna criterion for xi. -/
theorem xiTZerosReal_iff_xiNevanlinna :
    XiTZerosReal ↔ XiNevanlinna :=
  ⟨xiNevanlinna_of_XiTZerosReal, XiTZerosReal_of_xiNevanlinna⟩

/-- The Suzuki zero series is normally summable on compact real intervals. -/
theorem suzukiPsiZero_summableLocallyUniformly :
    SummableLocallyUniformlyOn
      (fun a : XiZeroOccurrence => fun t : ℝ => suzukiPsiZeroTerm t a)
      Set.univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hKsub hK
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let u : XiZeroOccurrence → ℝ := fun a =>
    (1 + Real.exp (R / 2)) * (1 / ‖xiSpectralParameter a‖ ^ 2)
  have hu : Summable u :=
    xiSpectral_reciprocal_sq_summable.mul_left (1 + Real.exp (R / 2))
  refine ⟨u, hu, ?_⟩
  intro a t ht
  have htR : |t| ≤ R := by
    simpa [Real.norm_eq_abs] using hR t ht
  calc
    ‖suzukiPsiZeroTerm t a‖ ≤
        (1 + Real.exp (|t| / 2)) *
          (1 / ‖xiSpectralParameter a‖ ^ 2) :=
      norm_suzukiPsiZeroTerm_le t a
    _ ≤ (1 + Real.exp (R / 2)) *
          (1 / ‖xiSpectralParameter a‖ ^ 2) := by
      gcongr
    _ = u a := rfl

theorem continuous_suzukiPsiZero : Continuous suzukiPsiZero := by
  have hloc :=
    suzukiPsiZero_summableLocallyUniformly.hasSumLocallyUniformlyOn
  have hcont : ∀ F : Finset XiZeroOccurrence,
      Continuous (fun t : ℝ => ∑ a ∈ F, suzukiPsiZeroTerm t a) := by
    intro F
    apply continuous_finsetSum
    intro a ha
    unfold suzukiPsiZeroTerm
    fun_prop
  have hlim : ContinuousOn
      (fun t : ℝ => ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a)
      Set.univ :=
    hloc.continuousOn (Frequently.of_forall fun F => (hcont F).continuousOn)
  change Continuous (fun t : ℝ =>
    ∑' a : XiZeroOccurrence, suzukiPsiZeroTerm t a)
  exact continuousOn_univ.mp hlim

theorem continuous_suzukiPsi : Continuous suzukiPsi := by
  change Continuous (fun t => (suzukiPsiZero t).re)
  exact Complex.continuous_re.comp continuous_suzukiPsiZero

theorem continuous_riemannScrew : Continuous riemannScrew := by
  change Continuous (fun t => -suzukiPsi t)
  exact continuous_suzukiPsi.neg

/-- The translation-difference kernel of a complex-valued function. -/
def screwKernel (g : ℝ → ℂ) (t u : ℝ) : ℂ :=
  g (t - u) - g t - g (-u) + g 0

/-- Suzuki's elementary screw-function conditions, with positivity expressed
by finite sampled kernel matrices. -/
def IsScrewFunction (g : ℝ → ℂ) : Prop :=
  Continuous g ∧
    g 0 = 0 ∧
    (∀ t : ℝ, g (-t) = starRingEnd ℂ (g t)) ∧
    KernelPSD (screwKernel g)

private theorem screwKernel_riemannScrew :
    screwKernel (fun x => (riemannScrew x : ℂ)) =
      riemannScrewKernel := by
  funext t u
  rfl

/-- For the already normalized real-even Riemann screw function, the only
remaining screw-function condition is kernel positive semidefiniteness. -/
theorem riemannScrew_isScrew_iff_kernelPSD :
    IsScrewFunction (fun t => (riemannScrew t : ℂ)) ↔
      KernelPSD riemannScrewKernel := by
  constructor
  · intro h
    have hPSD := h.2.2.2
    rw [screwKernel_riemannScrew] at hPSD
    exact hPSD
  · intro hPSD
    refine ⟨Complex.continuous_ofReal.comp continuous_riemannScrew, ?_, ?_, ?_⟩
    · simp
    · intro t
      change (riemannScrew (-t) : ℂ) =
        starRingEnd ℂ (riemannScrew t : ℂ)
      rw [riemannScrew_even]
      simp
    · rw [screwKernel_riemannScrew]
      exact hPSD

/-- One occurrence contribution to the Fourier--Laplace transform of the
Riemann screw function. -/
def riemannScrewTransformTerm (z : ℂ) (a : XiZeroOccurrence) (t : ℝ) : ℂ :=
  (-suzukiPsiZeroTerm t a) *
    Complex.exp (Complex.I * z * (t : ℂ))

private theorem riemannScrewTransformTerm_eq_exp_sub
    (z : ℂ) (a : XiZeroOccurrence) (t : ℝ) :
    riemannScrewTransformTerm z a t =
      (xiSpectralParameter a ^ 2)⁻¹ *
        (Complex.exp
            (Complex.I * (xiSpectralParameter a + z) * (t : ℂ)) -
          Complex.exp (Complex.I * z * (t : ℂ))) := by
  rw [riemannScrewTransformTerm, suzukiPsiZeroTerm]
  rw [show Complex.exp
      (Complex.I * (xiSpectralParameter a + z) * (t : ℂ)) =
      Complex.exp
          (Complex.I * xiSpectralParameter a * (t : ℂ)) *
        Complex.exp (Complex.I * z * (t : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  simp only [div_eq_mul_inv]
  ring

private theorem spectral_add_im_pos {z : ℂ}
    (hz : 1 / 2 < z.im) (a : XiZeroOccurrence) :
    0 < (xiSpectralParameter a + z).im := by
  have ha := abs_xiSpectralParameter_im_le_half a
  rw [abs_le] at ha
  simp only [Complex.add_im]
  linarith

theorem integrableOn_riemannScrewTransformTerm {z : ℂ}
    (hz : 1 / 2 < z.im) (a : XiZeroOccurrence) :
    MeasureTheory.IntegrableOn (riemannScrewTransformTerm z a) (Set.Ioi 0) := by
  have hsum : (Complex.I * (xiSpectralParameter a + z)).re < 0 := by
    simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    exact neg_lt_zero.mpr (spectral_add_im_pos hz a)
  have hz' : (Complex.I * z).re < 0 := by
    simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    linarith
  have h1 := integrableOn_exp_mul_complex_Ioi hsum 0
  have h2 := integrableOn_exp_mul_complex_Ioi hz' 0
  have h := (h1.sub h2).const_mul (xiSpectralParameter a ^ 2)⁻¹
  apply h.congr
  filter_upwards with t
  exact (riemannScrewTransformTerm_eq_exp_sub z a t).symm

/-- The exact integral of one spectral screw contribution. -/
theorem integral_riemannScrewTransformTerm {z : ℂ}
    (hz : 1 / 2 < z.im) (a : XiZeroOccurrence) :
    ∫ t : ℝ in Set.Ioi 0, riemannScrewTransformTerm z a t =
      (Complex.I / z ^ 2) * xiSpectralCorrectedTerm (-z) a := by
  have hsum : (Complex.I * (xiSpectralParameter a + z)).re < 0 := by
    simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    exact neg_lt_zero.mpr (spectral_add_im_pos hz a)
  have hz' : (Complex.I * z).re < 0 := by
    simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hγ0 : xiSpectralParameter a ≠ 0 := xiSpectralParameter_ne_zero a
  have hγz0 : xiSpectralParameter a + z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at him
    exact (ne_of_gt (spectral_add_im_pos hz a)) him
  rw [show (∫ t : ℝ in Set.Ioi 0, riemannScrewTransformTerm z a t) =
      (xiSpectralParameter a ^ 2)⁻¹ *
        ((∫ t : ℝ in Set.Ioi 0,
            Complex.exp
              ((Complex.I * (xiSpectralParameter a + z)) * (t : ℂ))) -
          ∫ t : ℝ in Set.Ioi 0,
            Complex.exp ((Complex.I * z) * (t : ℂ))) by
    rw [← MeasureTheory.integral_sub,
      ← MeasureTheory.integral_const_mul]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      exact riemannScrewTransformTerm_eq_exp_sub z a t
    · exact integrableOn_exp_mul_complex_Ioi hsum 0
    · exact integrableOn_exp_mul_complex_Ioi hz' 0]
  rw [integral_exp_mul_complex_Ioi hsum 0,
    integral_exp_mul_complex_Ioi hz' 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
  rw [xiSpectralCorrectedTerm]
  field_simp [hz0, hγ0, hγz0, I_ne_zero]
  rw [I_sq]
  ring

private def screwTransformDecay (z : ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(z.im - 1 / 2) * t) + Real.exp (-z.im * t)

private theorem integrableOn_screwTransformDecay {z : ℂ}
    (hz : 1 / 2 < z.im) :
    MeasureTheory.IntegrableOn (screwTransformDecay z) (Set.Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (a := -(z.im - 1 / 2)) (by linarith) 0).add
    (integrableOn_exp_mul_Ioi (a := -z.im) (by linarith) 0)

private theorem integral_screwTransformDecay {z : ℂ}
    (hz : 1 / 2 < z.im) :
    ∫ t : ℝ in Set.Ioi 0, screwTransformDecay z t =
      1 / (z.im - 1 / 2) + 1 / z.im := by
  unfold screwTransformDecay
  rw [MeasureTheory.integral_add
    (integrableOn_exp_mul_Ioi (a := -(z.im - 1 / 2)) (by linarith) 0)
    (integrableOn_exp_mul_Ioi (a := -z.im) (by linarith) 0),
    integral_exp_mul_Ioi (a := -(z.im - 1 / 2)) (by linarith) 0,
    integral_exp_mul_Ioi (a := -z.im) (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_gt (by linarith : 0 < z.im - 1 / 2),
    ne_of_gt (by linarith : 0 < z.im)]

private theorem norm_riemannScrewTransformTerm_le {z : ℂ}
    (_hz : 1 / 2 < z.im) (a : XiZeroOccurrence) {t : ℝ} (ht : 0 < t) :
    ‖riemannScrewTransformTerm z a t‖ ≤
      (1 / ‖xiSpectralParameter a‖ ^ 2) * screwTransformDecay z t := by
  have haBounds := abs_xiSpectralParameter_im_le_half a
  rw [abs_le] at haBounds
  have hfirst :
      ‖Complex.exp
          (Complex.I * (xiSpectralParameter a + z) * (t : ℂ))‖ ≤
        Real.exp (-(z.im - 1 / 2) * t) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    nlinarith [mul_nonneg (by linarith :
      0 ≤ (xiSpectralParameter a).im + 1 / 2) ht.le]
  have hsecond :
      ‖Complex.exp (Complex.I * z * (t : ℂ))‖ =
        Real.exp (-z.im * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [riemannScrewTransformTerm_eq_exp_sub, norm_mul, norm_inv,
    norm_pow]
  calc
    (‖xiSpectralParameter a‖ ^ 2)⁻¹ *
        ‖Complex.exp
            (Complex.I * (xiSpectralParameter a + z) * (t : ℂ)) -
          Complex.exp (Complex.I * z * (t : ℂ))‖ ≤
      (‖xiSpectralParameter a‖ ^ 2)⁻¹ *
        (‖Complex.exp
            (Complex.I * (xiSpectralParameter a + z) * (t : ℂ))‖ +
          ‖Complex.exp (Complex.I * z * (t : ℂ))‖) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (‖xiSpectralParameter a‖ ^ 2)⁻¹ *
        (Real.exp (-(z.im - 1 / 2) * t) +
          Real.exp (-z.im * t)) := by
        gcongr
        exact hsecond.le
    _ = (1 / ‖xiSpectralParameter a‖ ^ 2) *
        screwTransformDecay z t := by
      unfold screwTransformDecay
      simp only [one_div]

private theorem summable_integral_norm_riemannScrewTransformTerm {z : ℂ}
    (hz : 1 / 2 < z.im) :
    Summable (fun a : XiZeroOccurrence =>
      ∫ t : ℝ in Set.Ioi 0, ‖riemannScrewTransformTerm z a t‖) := by
  let C : ℝ := 1 / (z.im - 1 / 2) + 1 / z.im
  let u : XiZeroOccurrence → ℝ := fun a =>
    C * (1 / ‖xiSpectralParameter a‖ ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hu : Summable u := by
    have h := xiSpectral_reciprocal_sq_summable.mul_left C
    exact h.congr fun a => by
      dsimp [u]
  refine Summable.of_norm_bounded hu ?_
  intro a
  have hterm := (integrableOn_riemannScrewTransformTerm hz a).norm
  have hdecay := integrableOn_screwTransformDecay hz
  have hmajorant : MeasureTheory.IntegrableOn
      (fun t : ℝ => (1 / ‖xiSpectralParameter a‖ ^ 2) *
        screwTransformDecay z t) (Set.Ioi 0) :=
    hdecay.const_mul _
  have hle :
      (∫ t : ℝ in Set.Ioi 0, ‖riemannScrewTransformTerm z a t‖) ≤
        ∫ t : ℝ in Set.Ioi 0,
          (1 / ‖xiSpectralParameter a‖ ^ 2) *
            screwTransformDecay z t := by
    apply MeasureTheory.integral_mono_ae hterm hmajorant
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_riemannScrewTransformTerm_le hz a ht
  have hnonneg : 0 ≤
      ∫ t : ℝ in Set.Ioi 0, ‖riemannScrewTransformTerm z a t‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    (∫ t : ℝ in Set.Ioi 0, ‖riemannScrewTransformTerm z a t‖) ≤
        ∫ t : ℝ in Set.Ioi 0,
          (1 / ‖xiSpectralParameter a‖ ^ 2) *
            screwTransformDecay z t := hle
    _ = (1 / ‖xiSpectralParameter a‖ ^ 2) * C := by
      rw [MeasureTheory.integral_const_mul, integral_screwTransformDecay hz]
    _ = u a := by
      dsimp [u]
      ring

private theorem ofReal_riemannScrew_eq_spectral_tsum (t : ℝ) :
    (riemannScrew t : ℂ) =
      ∑' a : XiZeroOccurrence, -suzukiPsiZeroTerm t a := by
  rw [riemannScrew]
  push_cast
  rw [ofReal_suzukiPsi, suzukiPsiZero, tsum_neg]

private theorem screw_transform_integrand_eq_tsum (z : ℂ) (t : ℝ) :
    (riemannScrew t : ℂ) *
        Complex.exp (Complex.I * z * (t : ℂ)) =
      ∑' a : XiZeroOccurrence, riemannScrewTransformTerm z a t := by
  rw [ofReal_riemannScrew_eq_spectral_tsum]
  have hsum := (summable_suzukiPsiZero_term t).neg
  rw [← hsum.tsum_mul_right
    (Complex.exp (Complex.I * z * (t : ℂ)))]
  apply tsum_congr
  intro a
  rfl

private theorem riemannXi_centered_neg_ne_zero_high_strip {z : ℂ}
    (hz : 1 / 2 < z.im) :
    riemannXi ((1 / 2 : ℂ) - Complex.I * (-z)) ≠ 0 := by
  intro hzero
  have hre := riemannXi_zero_re_mem_Ioo hzero
  norm_num [Complex.mul_re] at hre
  linarith

theorem integrableOn_riemannScrew_exp {z : ℂ}
    (hz : 1 / 2 < z.im) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (riemannScrew t : ℂ) *
        Complex.exp (Complex.I * z * (t : ℂ)))
      (Set.Ioi 0) := by
  let S : ℝ := ∑' a : XiZeroOccurrence,
    1 / ‖xiSpectralParameter a‖ ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hmajor : MeasureTheory.IntegrableOn
      (fun t : ℝ => S * screwTransformDecay z t) (Set.Ioi 0) :=
    (integrableOn_screwTransformDecay hz).const_mul S
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp continuous_riemannScrew).mul
      (Complex.continuous_exp.comp (by fun_prop))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [screw_transform_integrand_eq_tsum]
    have hterm : Summable (fun a : XiZeroOccurrence =>
        riemannScrewTransformTerm z a t) := by
      have h := (summable_suzukiPsiZero_term t).neg.mul_right
        (Complex.exp (Complex.I * z * (t : ℂ)))
      exact h.congr fun _ => rfl
    have hbound : Summable (fun a : XiZeroOccurrence =>
        (1 / ‖xiSpectralParameter a‖ ^ 2) *
          screwTransformDecay z t) :=
      xiSpectral_reciprocal_sq_summable.mul_right _
    calc
      ‖∑' a : XiZeroOccurrence, riemannScrewTransformTerm z a t‖ ≤
          ∑' a : XiZeroOccurrence,
            ‖riemannScrewTransformTerm z a t‖ :=
        norm_tsum_le_tsum_norm hterm.norm
      _ ≤ ∑' a : XiZeroOccurrence,
          (1 / ‖xiSpectralParameter a‖ ^ 2) *
            screwTransformDecay z t :=
        hterm.norm.tsum_le_tsum
          (fun a => norm_riemannScrewTransformTerm_le hz a ht) hbound
      _ = S * screwTransformDecay z t := by
        dsimp [S]
        exact xiSpectral_reciprocal_sq_summable.tsum_mul_right _

/-- The Fourier--Laplace transform dictated by RH Garden's spectral
coordinate `ρ = 1/2 - Iγ`.  Notice the argument `-z`: with the kernel
`exp (Iγt)` and transform kernel `exp (Izt)`, the two exponents add. -/
theorem integral_riemannScrew_exp_eq_xiNevanlinnaQ_neg
    {z : ℂ} (hz : 1 / 2 < z.im) :
    ∫ t : ℝ in Set.Ioi 0,
        (riemannScrew t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ)) =
      (Complex.I / z ^ 2) * xiNevanlinnaQ (-z) := by
  have hinterchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (fun a => integrableOn_riemannScrewTransformTerm hz a)
      (summable_integral_norm_riemannScrewTransformTerm hz)
  have hcenter := riemannXi_centered_neg_ne_zero_high_strip hz
  have hcorr := summable_xiSpectralCorrectedTerm hcenter
  calc
    (∫ t : ℝ in Set.Ioi 0,
        (riemannScrew t : ℂ) *
          Complex.exp (Complex.I * z * (t : ℂ))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' a : XiZeroOccurrence, riemannScrewTransformTerm z a t := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            exact screw_transform_integrand_eq_tsum z t
    _ = ∑' a : XiZeroOccurrence,
        ∫ t : ℝ in Set.Ioi 0, riemannScrewTransformTerm z a t :=
          hinterchange.symm
    _ = ∑' a : XiZeroOccurrence,
        (Complex.I / z ^ 2) * xiSpectralCorrectedTerm (-z) a := by
          apply tsum_congr
          exact integral_riemannScrewTransformTerm hz
    _ = (Complex.I / z ^ 2) *
        ∑' a : XiZeroOccurrence, xiSpectralCorrectedTerm (-z) a :=
          hcorr.tsum_mul_left _
    _ = (Complex.I / z ^ 2) * xiNevanlinnaQ (-z) := by
          rw [xiNevanlinnaQ_eq_spectral_sum hcenter]

/-- The remaining historical Krein--Langer step, isolated as one explicit
open formalization boundary. -/
def ScrewToNevanlinnaBridge : Prop :=
  KernelPSD riemannScrewKernel → XiNevanlinna

/-- The first finite-test consequence in the specialized Krein--Langer
direction: positive semidefiniteness forces the normalized real screw
function to be nonpositive.  Extending finite sampled tests to the noncompact
exponential integral tests is the remaining bridge. -/
theorem riemannScrew_nonpos_of_kernelPSD
    (hPSD : KernelPSD riemannScrewKernel) (t : ℝ) :
    riemannScrew t ≤ 0 := by
  have h := hPSD 1 (fun _ => t) (fun _ => 1)
  simp only [Fin.sum_univ_one, mul_one, map_one] at h
  rw [riemannScrewKernel, sub_self, riemannScrew_even,
    riemannScrew_zero] at h
  norm_num at h ⊢
  linarith

theorem riemannScrewKernel_psd_implies_XiTZerosReal_of_bridge
    (hbridge : ScrewToNevanlinnaBridge) :
    KernelPSD riemannScrewKernel → XiTZerosReal :=
  fun hPSD => XiTZerosReal_of_xiNevanlinna (hbridge hPSD)

theorem xiTZerosReal_iff_riemannScrewKernel_psd_of_bridge
    (hbridge : ScrewToNevanlinnaBridge) :
    XiTZerosReal ↔ KernelPSD riemannScrewKernel :=
  ⟨riemannScrewKernel_psd_of_XiTZerosReal,
    riemannScrewKernel_psd_implies_XiTZerosReal_of_bridge hbridge⟩

end RHGarden
