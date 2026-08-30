import RHGarden.ZetaZeros

noncomputable section

open Complex

namespace RHGarden

/-- The entire critical-line coordinate, with a complex coordinate `t`. -/
def XiT (t : ℂ) : ℂ := riemannXi (1 / 2 + I * t)

theorem XiT_neg (t : ℂ) : XiT (-t) = XiT t := by
  rw [XiT, XiT, ← riemannXi_one_sub (1 / 2 + I * t)]
  congr 1
  ring

/-- Every zero of `XiT` has a real coordinate.  This remains an open
proposition; the theorems below prove equivalences, not this proposition. -/
def XiTZerosReal : Prop := ∀ t : ℂ, XiT t = 0 → t.im = 0

/-- The xi RH formulation is equivalent to reality of every zero coordinate
of `XiT`. -/
theorem xiRiemannHypothesis_iff_XiTZerosReal :
    XiRiemannHypothesis ↔ XiTZerosReal := by
  constructor
  · intro h t ht
    rw [XiT] at ht
    have hre := h (1 / 2 + I * t) ht
    norm_num [Complex.mul_re] at hre ⊢
    linarith
  · intro h s hxi
    let t : ℂ := -I * (s - 1 / 2)
    have hcoord : (1 / 2 : ℂ) + I * t = s := by
      dsimp [t]
      have hi : I * (-I) = (1 : ℂ) := by
        rw [mul_neg, I_mul_I]
        norm_num
      rw [← mul_assoc, hi, one_mul]
      ring
    have ht : XiT t = 0 := by
      rw [XiT, hcoord]
      exact hxi
    have him := h t ht
    dsimp [t] at him
    norm_num [Complex.mul_im] at him ⊢
    linarith

theorem riemannHypothesis_iff_XiTZerosReal :
    RiemannHypothesis ↔ XiTZerosReal :=
  riemannHypothesis_iff_xiRiemannHypothesis.trans
    xiRiemannHypothesis_iff_XiTZerosReal

end RHGarden
