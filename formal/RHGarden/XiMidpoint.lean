import RHGarden.SuzukiScrew
import Zeta23.FromPNTPlus.ZetaBounds

noncomputable section

open Complex MeasureTheory Set

namespace RHGarden

/-- The Euler--Maclaurin remainder in the `N = 1`, `s = 1/2` formula for
the Riemann zeta function. -/
private noncomputable def zetaHalfRemainder : ℂ :=
  ∫ x in Ioi (1 : ℝ),
    ((⌊x⌋ : ℂ) + 1 / 2 - x) /
      (x : ℂ) ^ ((1 / 2 : ℂ) + 1)

private theorem norm_zetaHalfRemainder_le_two :
    ‖zetaHalfRemainder‖ ≤ 2 := by
  simpa [zetaHalfRemainder] using
    (ZetaBnd_aux1b 1 le_rfl (σ := (1 / 2 : ℝ)) (t := 0) (by norm_num))

private theorem riemannZeta_half_eq :
    riemannZeta (1 / 2 : ℂ) =
      -(3 / 2 : ℂ) + (1 / 2 : ℂ) * zetaHalfRemainder := by
  have hsum :
      (∑ n ∈ Finset.range 2,
        ((n : ℂ) ^ (2 : ℂ)⁻¹)⁻¹) = 1 := by
    norm_num [Finset.sum_range_succ, Complex.zero_cpow]
  rw [← Zeta0EqZeta (N := 1) one_pos (s := (1 / 2 : ℂ))
    (by norm_num) (by norm_num)]
  simp [riemannZeta0, zetaHalfRemainder]
  rw [hsum]
  ring

/-- In fact the midpoint zeta value lies strictly in the left half-plane. -/
theorem riemannZeta_half_re_neg :
    (riemannZeta (1 / 2 : ℂ)).re < 0 := by
  rw [riemannZeta_half_eq]
  norm_num [Complex.mul_re]
  have hre : zetaHalfRemainder.re ≤ ‖zetaHalfRemainder‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  nlinarith [norm_zetaHalfRemainder_le_two]

/-- The Riemann zeta function does not vanish at the real midpoint.  The
proof uses the pinned Euler--Maclaurin formula with `N = 1`: its main term is
`-3/2`, while the remaining term has norm at most `1`. -/
theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  intro hz
  have hrepr := riemannZeta_half_eq
  rw [hz] at hrepr
  have hhalfRemainder :
      ‖(1 / 2 : ℂ) * zetaHalfRemainder‖ ≤ 1 := by
    rw [norm_mul]
    norm_num
    nlinarith [norm_zetaHalfRemainder_le_two]
  have heq : (3 / 2 : ℂ) = (1 / 2 : ℂ) * zetaHalfRemainder := by
    linear_combination hrepr
  rw [← heq] at hhalfRemainder
  norm_num at hhalfRemainder

/-- The completed Riemann xi function is nonzero at its symmetry midpoint. -/
theorem riemannXi_half_ne_zero :
    riemannXi (1 / 2 : ℂ) ≠ 0 := by
  intro hxi
  exact riemannZeta_half_ne_zero
    (riemannZeta_eq_zero_of_riemannXi_eq_zero
      (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num) hxi)

/-- The previously isolated midpoint input is now discharged unconditionally. -/
theorem xiMidpointNonzero : XiMidpointNonzero :=
  riemannXi_half_ne_zero

/-- Every Suzuki spectral denominator is genuinely nonzero. -/
theorem xiSpectralParameter_ne_zero (a : XiZeroOccurrence) :
    xiSpectralParameter a ≠ 0 :=
  xiSpectralParameter_ne_zero_of_midpoint xiMidpointNonzero a

end RHGarden
