import RHGarden.LiHadamardInfinite

noncomputable section

open Complex

namespace RHGarden

/-- A fixed order strictly between one and two. Any such order makes the
Hadamard polynomial affine; `3 / 2` is a convenient concrete choice. -/
def xiGrowthOrder : ℝ := 3 / 2

theorem one_le_xiGrowthOrder : 1 ≤ xiGrowthOrder := by
  norm_num [xiGrowthOrder]

theorem xiGrowthOrder_lt_two : xiGrowthOrder < 2 := by
  norm_num [xiGrowthOrder]

theorem floor_xiGrowthOrder : Nat.floor xiGrowthOrder = 1 := by
  apply (Nat.floor_eq_iff (by norm_num [xiGrowthOrder] : 0 ≤ xiGrowthOrder)).2
  constructor <;> norm_num [xiGrowthOrder]

/-- The coarse global growth estimate needed from the analytic theory of the
completed zeta function. The exponent `3 / 2 + ε` is deliberately weaker than
the classical order-one estimate. Since `⌊3 / 2⌋ = 1`, it is still sufficient
to force the polynomial in Hadamard factorization to be affine. -/
def XiSubquadraticGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))

/-- The general quotient-polynomial principle still needed after constructing
RH Garden's intrinsic canonical product. It is deliberately stated for an
arbitrary zero-free entire function and is therefore not a disguised xi
factorization assumption. -/
def SubquadraticZeroFreeEntireIsExpAffine : Prop :=
  ∀ H : ℂ → ℂ,
    Differentiable ℂ H →
    (∀ z : ℂ, H z ≠ 0) →
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))) →
    ∃ A B : ℂ, ∀ z : ℂ, H z = Complex.exp (A + B * z)

/-- Opposite centered zeros cancel the exponential corrections in the two
genus-one primary factors. No assertion that `α` is a zero is needed. -/
theorem primaryFactorOne_mul_primaryFactorOne_neg (w α : ℂ) :
    primaryFactorOne (w / α) * primaryFactorOne (w / (-α)) =
      1 - (w / α) ^ 2 := by
  have hneg : w / (-α) = -(w / α) := by ring
  rw [hneg]
  simp only [primaryFactorOne]
  rw [show
    (1 - w / α) * Complex.exp (w / α) *
        ((1 - -(w / α)) * Complex.exp (-(w / α))) =
      ((1 - w / α) * (1 - -(w / α))) *
        (Complex.exp (w / α) * Complex.exp (-(w / α))) by ring]
  rw [← Complex.exp_add]
  simp
  ring

end RHGarden
