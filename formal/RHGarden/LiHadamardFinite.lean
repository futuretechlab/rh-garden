import RHGarden.LiStarConvergence
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

noncomputable section

open Complex

namespace RHGarden

/-- The genus-one Weierstrass primary factor `E₁(w) = (1-w) exp(w)`. -/
def primaryFactorOne (w : ℂ) : ℂ := (1 - w) * Complex.exp w

/-- The finite genus-one product attached to a zero multiset. Multiplicity is
represented by repetition in the multiset. -/
def finitePrimaryProduct (Z : Multiset ℂ) (s : ℂ) : ℂ :=
  (Z.map fun ρ ↦ primaryFactorOne (s / ρ)).prod

theorem primaryFactorOne_ne_zero_iff (w : ℂ) :
    primaryFactorOne w ≠ 0 ↔ w ≠ 1 := by
  simp [primaryFactorOne]

/-- The logarithmic derivative of one genus-one factor. -/
theorem logDeriv_primaryFactorOne_div {ρ s : ℂ} (hρ : ρ ≠ 0)
    (hsρ : s ≠ ρ) :
    logDeriv (fun z : ℂ ↦ primaryFactorOne (z / ρ)) s =
      1 / (s - ρ) + 1 / ρ := by
  rw [logDeriv_apply]
  simp only [primaryFactorOne]
  have hfactor : 1 - s / ρ ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h ↦ hsρ (div_eq_one.mp h)
  have hexp : Complex.exp (s / ρ) ≠ 0 := Complex.exp_ne_zero _
  have hderiv :
      deriv (fun z : ℂ ↦ (1 - z / ρ) * Complex.exp (z / ρ)) s =
        (-1 / ρ) * Complex.exp (s / ρ) +
          (1 - s / ρ) * (Complex.exp (s / ρ) * (1 / ρ)) := by
    convert HasDerivAt.deriv
      (((hasDerivAt_const s 1).sub (hasDerivAt_id s).div_const ρ).mul
        (Complex.hasDerivAt_exp (s / ρ)).comp s ((hasDerivAt_id s).div_const ρ)) using 1 <;>
      ring
  rw [hderiv]
  field_simp
  ring

/-- Finite, convergence-free logarithmic-derivative identity for the genus-one
canonical factors. -/
theorem logDeriv_finitePrimaryProduct (Z : Multiset ℂ) {s : ℂ}
    (hZ0 : ∀ ρ ∈ Z, ρ ≠ 0) (hsZ : ∀ ρ ∈ Z, s ≠ ρ) :
    logDeriv (finitePrimaryProduct Z) s =
      (Z.map fun ρ ↦ (1 / (s - ρ) + 1 / ρ)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp [finitePrimaryProduct]
  | @cons ρ Z ih =>
      have hρ0 : ρ ≠ 0 := hZ0 ρ (by simp)
      have hsρ : s ≠ ρ := hsZ ρ (by simp)
      have htail0 : ∀ z ∈ Z, z ≠ 0 := by
        intro z hz
        exact hZ0 z (by simp [hz])
      have hsTail : ∀ z ∈ Z, s ≠ z := by
        intro z hz
        exact hsZ z (by simp [hz])
      have hhead : primaryFactorOne (s / ρ) ≠ 0 := by
        rw [primaryFactorOne_ne_zero_iff]
        exact fun h ↦ hsρ (div_eq_one.mp h)
      have htail : finitePrimaryProduct Z s ≠ 0 := by
        simp only [finitePrimaryProduct, Multiset.map_eq_map, Multiset.prod_ne_zero_iff]
        intro z hz
        rw [primaryFactorOne_ne_zero_iff]
        exact fun h ↦ hsTail z hz (div_eq_one.mp h)
      rw [show finitePrimaryProduct (ρ ::ₘ Z) = fun z ↦
          primaryFactorOne (z / ρ) * finitePrimaryProduct Z z by
        funext z
        simp [finitePrimaryProduct]]
      rw [logDeriv_mul s hhead htail (by fun_prop) (by fun_prop),
        logDeriv_primaryFactorOne_div hρ0 hsρ, ih htail0 hsTail]
      simp

/-- The finite Li functional written in terms of the Taylor jet at `s = 1`
of the compensated logarithmic derivative `Σρ 1 / (s - ρ)`.  The summand
with index `j` is its `(j-1)`-st normalized derivative. -/
def finiteLogDerivLiJet (Z : Multiset ℂ) (m : ℕ) : ℂ :=
  (Z.map fun ρ ↦ ∑ j ∈ Finset.Icc 1 m,
    (-1 : ℂ) ^ (j - 1) * Nat.choose m j / (1 - ρ) ^ j).sum

/-- Finite analogue of Lagarias's derivative/zero identity.  It has no
convergence input: the normalized log-derivative jet of a finite zero product
is exactly the negative-index finite Li zero sum. -/
theorem finiteLogDerivLiJet_eq_finiteLiZeroValue (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (m : ℕ) :
    finiteLogDerivLiJet Z m = finiteLiZeroValue Z (-(m : ℤ)) := by
  unfold finiteLogDerivLiJet finiteLiZeroValue
  congr 1
  apply Multiset.map_congr
  intro ρ hρ
  obtain ⟨hρ0, hρ1⟩ := hZ ρ hρ
  rw [weilLiTest_neg (m : ℤ) hρ0 hρ1,
    weilLiTest_nat_expansion m (sub_ne_zero.mpr hρ1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [show j + 1 = (j - 1) + 2 by omega, pow_add]
  norm_num
  ring

/-- The exact global analytic input still required to identify xi with its
genus-one divisor product.  No inhabitant is asserted here.  The nonzero
constant and linear exponential are the degree-at-most-one Hadamard quotient. -/
def XiGenusOneFactorization : Prop :=
  ∃ A B : ℂ, ∀ s : ℂ,
    riemannXi s = Complex.exp (A * s + B) *
      ∏' ρ : XiZero, primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ)

end RHGarden
