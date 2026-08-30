import RHGarden.Xi
import Mathlib.NumberTheory.LSeries.Nonvanishing

noncomputable section

namespace RHGarden

open Complex

/-- Exactly the side conditions used by mathlib's `RiemannHypothesis`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- The shifted Gamma factor in mathlib's pole-free zeta representation is
nonzero precisely under the trivial-zero exclusion used by RH. -/
theorem gamma_half_add_one_ne_zero_of_nontrivial {s : ℂ}
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    Complex.Gamma (s / 2 + 1) ≠ 0 := by
  intro hgamma
  obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff (s / 2 + 1)).mp hgamma
  apply htriv
  refine ⟨n, ?_⟩
  linear_combination 2 * hn

/-- The complete denominator in `riemannZeta_eq_mul_completedRiemannZeta₀`
is nonzero under the same exclusion. -/
theorem zetaXiDenominator_ne_zero_of_nontrivial {s : ℂ}
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_ne_zero (mul_ne_zero htwo hpi)
    (gamma_half_add_one_ne_zero_of_nontrivial htriv)

/-- The numerator of mathlib's pole-free completed-zeta representation. -/
def zetaXiNumerator (s : ℂ) : ℂ :=
  s * completedRiemannZeta₀ s - 1 - s / (1 - s)

theorem zetaXiNumerator_eq_zero_of_riemannZeta_eq_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    zetaXiNumerator s = 0 := by
  have hformula := riemannZeta_eq_mul_completedRiemannZeta₀ s
  rw [hz] at hformula
  have hdiv : zetaXiNumerator s /
      (2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) = 0 := by
    simpa only [zetaXiNumerator] using hformula.symm
  exact (div_eq_zero_iff.mp hdiv).resolve_right
    (zetaXiDenominator_ne_zero_of_nontrivial htriv)

/-- Pure algebra connecting the pole-free zeta numerator to the entire xi
definition. -/
theorem two_mul_riemannXi_eq_mul_zetaXiNumerator {s : ℂ} (hs1 : s ≠ 1) :
    2 * riemannXi s = (s - 1) * zetaXiNumerator s := by
  unfold riemannXi zetaXiNumerator
  field_simp [sub_ne_zero.mpr hs1.symm]
  ring

/-- Every nontrivial zeta zero in exactly mathlib's sense is an xi zero. -/
theorem riemannXi_eq_zero_of_nontrivial_riemannZeta_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    riemannXi s = 0 := by
  have hnum := zetaXiNumerator_eq_zero_of_riemannZeta_eq_zero hz htriv
  have hbridge := two_mul_riemannXi_eq_mul_zetaXiNumerator hs1
  rw [hnum, mul_zero] at hbridge
  exact (mul_eq_zero.mp hbridge).resolve_left (by norm_num)

theorem IsNontrivialZetaZero.riemannXi_eq_zero {s : ℂ}
    (h : IsNontrivialZetaZero s) : riemannXi s = 0 :=
  riemannXi_eq_zero_of_nontrivial_riemannZeta_zero h.1 h.2.1 h.2.2

/-- A typed restatement of mathlib's RH definition; this proves no instance of
RH and changes none of its mathematical content. -/
theorem riemannHypothesis_iff_nontrivialZero_re :
    RiemannHypothesis ↔
      ∀ s : ℂ, IsNontrivialZetaZero s → s.re = 1 / 2 := by
  constructor
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2
  · intro h s hz htriv hs1
    exact h s ⟨hz, htriv, hs1⟩

/-- The direction that does not require proving nonvanishing of the completed
gamma factor: away from `0` and `1`, every xi zero is a zeta zero. -/
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hxi : riemannXi s = 0) :
    riemannZeta s = 0 := by
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1] at hxi
  have hcompleted : completedRiemannZeta s = 0 := by
    have hfactor : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
    exact (mul_eq_zero.mp hxi).resolve_left hfactor
  rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]

/-- Nonvanishing of zeta forces nonvanishing of its completed numerator.  No
nonvanishing property of `Gammaℝ` is needed. -/
theorem completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hz : riemannZeta s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  intro hcompleted
  apply hz
  rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]

/-- Xi is nonzero at every positive odd integer `2n+3`. -/
theorem riemannXi_pos_odd_ne_zero (n : ℕ) :
    riemannXi (2 * (n : ℂ) + 3) ≠ 0 := by
  let u : ℂ := 2 * n + 3
  have hu0 : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [u] at hre
    norm_num at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hu1 : u ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [u] at hre
    norm_num at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hure : 1 ≤ u.re := by
    dsimp [u]
    norm_num
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hz : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re hure
  have hcompleted : completedRiemannZeta u ≠ 0 :=
    completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero hu0 hz
  rw [riemannXi_eq_completedRiemannZeta hu0 hu1]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hu0) (sub_ne_zero.mpr hu1)) hcompleted

/-- Xi is nonzero at every trivial-zero location of the Riemann zeta function. -/
theorem riemannXi_trivialZetaPoint_ne_zero (n : ℕ) :
    riemannXi (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  intro hxi
  apply riemannXi_pos_odd_ne_zero n
  have hcoord : (1 : ℂ) - (-2 * ((n : ℂ) + 1)) = 2 * n + 3 := by ring
  rw [← hcoord, riemannXi_one_sub]
  exact hxi

/-- Every xi zero is a nontrivial zeta zero, including all exceptional-point
exclusions. -/
theorem isNontrivialZetaZero_of_riemannXi_eq_zero {s : ℂ}
    (hxi : riemannXi s = 0) : IsNontrivialZetaZero s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannXi_zero] at hxi
    norm_num at hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    rw [riemannXi_one] at hxi
    norm_num at hxi
  refine ⟨riemannZeta_eq_zero_of_riemannXi_eq_zero hs0 hs1 hxi, ?_, hs1⟩
  rintro ⟨n, rfl⟩
  exact riemannXi_trivialZetaPoint_ne_zero n hxi

/-- The global zero-set correspondence between the entire xi function and
mathlib's exact notion of a nontrivial Riemann-zeta zero. -/
theorem riemannXi_eq_zero_iff_nontrivialZetaZero (s : ℂ) :
    riemannXi s = 0 ↔ IsNontrivialZetaZero s :=
  ⟨isNontrivialZetaZero_of_riemannXi_eq_zero,
    IsNontrivialZetaZero.riemannXi_eq_zero⟩

/-- The xi formulation of RH.  This is an open proposition, not a proof of RH. -/
def XiRiemannHypothesis : Prop :=
  ∀ s : ℂ, riemannXi s = 0 → s.re = 1 / 2

/-- Mathlib's RH proposition is equivalent to its entire-xi formulation. -/
theorem riemannHypothesis_iff_xiRiemannHypothesis :
    RiemannHypothesis ↔ XiRiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re]
  constructor
  · intro h s hxi
    exact h s ((riemannXi_eq_zero_iff_nontrivialZetaZero s).mp hxi)
  · intro h s hz
    exact h s ((riemannXi_eq_zero_iff_nontrivialZetaZero s).mpr hz)

end RHGarden
