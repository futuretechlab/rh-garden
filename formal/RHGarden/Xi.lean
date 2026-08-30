import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

open Complex

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

end RHGarden
