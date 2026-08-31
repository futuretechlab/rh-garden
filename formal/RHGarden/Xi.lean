import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section

open Complex
open Filter

namespace RHGarden

/-- The entire Riemann xi function, defined using mathlib's entire regularization
of the completed zeta function. -/
def riemannXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

@[simp] theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

@[simp] theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- `riemannXi` is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact ((differentiable_const (c := (1 : ℂ))).add
    ((differentiable_id.mul (differentiable_id.sub (differentiable_const (c := (1 : ℂ))))).mul
      differentiable_completedZeta₀)).div_const 2

/-- The xi functional equation, derived from mathlib's functional equation for
the entire regularized completed zeta function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  congr 1
  ring

/-- Away from the removable singularities, the entire definition agrees with
the classical expression `s (s - 1) Λ(s) / 2`. -/
theorem riemannXi_eq_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2) * s * (s - 1) * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

private theorem GammaR_conj (s : ℂ) :
    Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [show -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) by
      rw [map_div₀, map_neg, map_ofNat],
    show starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) by
      rw [map_div₀, map_ofNat],
    Complex.Gamma_conj]
  rw [Complex.cpow_conj]
  · simp
  · rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne

/-- The entire Riemann xi function commutes with complex conjugation. -/
@[simp] theorem riemannXi_conj (s : ℂ) :
    riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  let g : ℂ → ℂ := fun z ↦ starRingEnd ℂ (riemannXi (starRingEnd ℂ z))
  have hgdiff : Differentiable ℂ g := fun z ↦ by
    exact differentiableAt_conj_conj_iff.mpr differentiable_riemannXi.differentiableAt
  have hcompleted (z : ℂ) (hz : 1 < z.re) :
      completedRiemannZeta (starRingEnd ℂ z) =
        starRingEnd ℂ (completedRiemannZeta z) := by
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num at hz
    have hcz0 : starRingEnd ℂ z ≠ 0 := by simpa using hz0
    have hGamma : Complex.Gammaℝ z ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hGammaConj : Complex.Gammaℝ (starRingEnd ℂ z) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (lt_trans zero_lt_one hz))
    calc
      completedRiemannZeta (starRingEnd ℂ z) =
          riemannZeta (starRingEnd ℂ z) *
            Complex.Gammaℝ (starRingEnd ℂ z) :=
        ((eq_div_iff hGammaConj).mp
          (riemannZeta_def_of_ne_zero hcz0)).symm
      _ = starRingEnd ℂ (riemannZeta z) *
          starRingEnd ℂ (Complex.Gammaℝ z) := by
        rw [riemannZeta_conj, GammaR_conj]
      _ = starRingEnd ℂ (completedRiemannZeta z) := by
        rw [← map_mul]
        congr 1
        exact ((eq_div_iff hGamma).mp (riemannZeta_def_of_ne_zero hz0))
  have hlocal : g =ᶠ[nhds (2 : ℂ)] riemannXi := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const continuous_re
    apply eventuallyEq_of_mem
      (hopen.mem_nhds (by norm_num))
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    have hcz0 : starRingEnd ℂ z ≠ 0 := by simpa using hz0
    have hcz1 : starRingEnd ℂ z ≠ 1 := by
      simpa using (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hz1
    unfold g
    rw [riemannXi_eq_completedRiemannZeta hcz0 hcz1,
      riemannXi_eq_completedRiemannZeta hz0 hz1, hcompleted z hz]
    simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat,
      starRingEnd_self_apply]
  have hglobal : g = riemannXi :=
    (analyticOnNhd_univ_iff_differentiable.mpr hgdiff).eq_of_eventuallyEq
      (analyticOnNhd_univ_iff_differentiable.mpr differentiable_riemannXi) hlocal
  have hs := congrFun hglobal s
  simpa [g] using congrArg (starRingEnd ℂ) hs

end RHGarden
