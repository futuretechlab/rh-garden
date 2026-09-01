import RHGarden.LiStarConvergence
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

noncomputable section

open Complex

namespace RHGarden

/-- The genus-one Weierstrass primary factor `E₁(w) = (1-w) exp(w)`. -/
def primaryFactorOne (w : ℂ) : ℂ := (1 - w) * Complex.exp w

@[simp] theorem primaryFactorOne_zero : primaryFactorOne 0 = 1 := by
  simp [primaryFactorOne]

theorem primaryFactorOne_eq_zero_iff (w : ℂ) :
    primaryFactorOne w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact (Complex.exp_ne_zero w h).elim
  · rintro rfl
    simp [primaryFactorOne]

theorem primaryFactorOne_ne_zero_iff (w : ℂ) :
    primaryFactorOne w ≠ 0 ↔ w ≠ 1 :=
  not_congr (primaryFactorOne_eq_zero_iff w)

/-- The finite genus-one product attached to a zero multiset. Multiplicity is
represented by repetition in the multiset. -/
def finitePrimaryProduct (Z : Multiset ℂ) (s : ℂ) : ℂ :=
  (Z.map fun ρ ↦ primaryFactorOne (s / ρ)).prod

@[simp] theorem finitePrimaryProduct_empty (s : ℂ) :
    finitePrimaryProduct 0 s = 1 := by
  simp [finitePrimaryProduct]

@[simp] theorem finitePrimaryProduct_cons (ρ : ℂ) (Z : Multiset ℂ) (s : ℂ) :
    finitePrimaryProduct (ρ ::ₘ Z) s =
      primaryFactorOne (s / ρ) * finitePrimaryProduct Z s := by
  simp [finitePrimaryProduct]

theorem differentiable_primaryFactorOne_div (ρ : ℂ) :
    Differentiable ℂ (fun s : ℂ ↦ primaryFactorOne (s / ρ)) := by
  unfold primaryFactorOne
  fun_prop

theorem differentiable_finitePrimaryProduct (Z : Multiset ℂ) :
    Differentiable ℂ (finitePrimaryProduct Z) := by
  induction Z using Multiset.induction_on with
  | empty =>
      change Differentiable ℂ (fun _ : ℂ ↦ 1)
      exact differentiable_const (𝕜 := ℂ) (E := ℂ) (1 : ℂ)
  | @cons ρ Z ih =>
      rw [show finitePrimaryProduct (ρ ::ₘ Z) = fun s ↦
          primaryFactorOne (s / ρ) * finitePrimaryProduct Z s by
        funext s
        exact finitePrimaryProduct_cons ρ Z s]
      exact (differentiable_primaryFactorOne_div ρ).mul ih

/-- The logarithmic derivative of one genus-one factor. -/
theorem logDeriv_primaryFactorOne_div {ρ s : ℂ} (hρ : ρ ≠ 0)
    (hsρ : s ≠ ρ) :
    logDeriv (fun z : ℂ ↦ primaryFactorOne (z / ρ)) s =
      1 / (s - ρ) + 1 / ρ := by
  have hdiv : HasDerivAt (fun z : ℂ ↦ z / ρ) (1 / ρ) s :=
    (hasDerivAt_id s).div_const ρ
  have hsub : HasDerivAt (fun z : ℂ ↦ 1 - z / ρ) (-1 / ρ) s := by
    have h := (hasDerivAt_const s (1 : ℂ)).sub hdiv
    change HasDerivAt (fun z : ℂ ↦ 1 - z / ρ) (0 - 1 / ρ) s at h
    convert h using 1 <;> ring
  have hexp : HasDerivAt (fun z : ℂ ↦ Complex.exp (z / ρ))
      (Complex.exp (s / ρ) * (1 / ρ)) s := hdiv.cexp
  have hprod := hsub.mul hexp
  have hderiv := hprod.deriv
  change deriv (fun z : ℂ ↦ (1 - z / ρ) * Complex.exp (z / ρ)) s =
      (-1 / ρ) * Complex.exp (s / ρ) +
        (1 - s / ρ) * (Complex.exp (s / ρ) * (1 / ρ)) at hderiv
  rw [logDeriv_apply]
  change deriv (fun z : ℂ ↦ (1 - z / ρ) * Complex.exp (z / ρ)) s /
      ((1 - s / ρ) * Complex.exp (s / ρ)) = _
  rw [hderiv]
  field_simp [hρ, sub_ne_zero.mpr hsρ, Complex.exp_ne_zero]
  ring

/-- A finite primary product is nonzero away from every zero in its multiset. -/
theorem finitePrimaryProduct_ne_zero (Z : Multiset ℂ) {s : ℂ}
    (hZ0 : ∀ ρ ∈ Z, ρ ≠ 0) (hsZ : ∀ ρ ∈ Z, s ≠ ρ) :
    finitePrimaryProduct Z s ≠ 0 := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | @cons ρ Z ih =>
      have hρ0 : ρ ≠ 0 := hZ0 ρ (by simp)
      have hsρ : s ≠ ρ := hsZ ρ (by simp)
      have htail0 : ∀ z ∈ Z, z ≠ 0 := by
        intro z hz
        exact hZ0 z (by simp [hz])
      have hsTail : ∀ z ∈ Z, s ≠ z := by
        intro z hz
        exact hsZ z (by simp [hz])
      rw [finitePrimaryProduct_cons]
      apply mul_ne_zero
      · rw [primaryFactorOne_ne_zero_iff]
        exact fun h ↦ hsρ ((div_eq_one_iff_eq hρ0).mp h)
      · exact ih htail0 hsTail

/-- Finite, convergence-free logarithmic-derivative identity for the genus-one
canonical factors. -/
theorem logDeriv_finitePrimaryProduct (Z : Multiset ℂ) {s : ℂ}
    (hZ0 : ∀ ρ ∈ Z, ρ ≠ 0) (hsZ : ∀ ρ ∈ Z, s ≠ ρ) :
    logDeriv (finitePrimaryProduct Z) s =
      (Z.map fun ρ ↦ (1 / (s - ρ) + 1 / ρ)).sum := by
  induction Z using Multiset.induction_on with
  | empty =>
      rw [show finitePrimaryProduct 0 = fun _ : ℂ ↦ 1 by
        funext z
        exact finitePrimaryProduct_empty z]
      simp
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
        exact fun h ↦ hsρ ((div_eq_one_iff_eq hρ0).mp h)
      have htail : finitePrimaryProduct Z s ≠ 0 :=
        finitePrimaryProduct_ne_zero Z htail0 hsTail
      rw [show finitePrimaryProduct (ρ ::ₘ Z) = fun z ↦
          primaryFactorOne (z / ρ) * finitePrimaryProduct Z z by
        funext z
        exact finitePrimaryProduct_cons ρ Z z]
      rw [logDeriv_mul s hhead htail
          ((differentiable_primaryFactorOne_div ρ) s)
          ((differentiable_finitePrimaryProduct Z) s),
        logDeriv_primaryFactorOne_div hρ0 hsρ, ih htail0 hsTail]
      simp

/-- The finite Li functional written as the binomially weighted normalized jet
at `s = 1` of the compensated logarithmic derivative `Σρ 1 / (s - ρ)`.
The summand with index `j` is its `(j-1)`-st normalized derivative. -/
def finiteLogDerivLiJet (Z : Multiset ℂ) (m : ℕ) : ℂ :=
  (Z.map fun ρ ↦ ∑ j ∈ Finset.Icc 1 m,
    (-1 : ℂ) ^ (j - 1) * Nat.choose m j / (1 - ρ) ^ j).sum

/-- Finite analogue of Lagarias's derivative/zero identity. It has no
convergence or global factorization input: the finite compensated
logarithmic-derivative jet is exactly the negative-index finite Li zero sum. -/
theorem finiteLogDerivLiJet_eq_finiteLiZeroValue (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (m : ℕ) :
    finiteLogDerivLiJet Z m = finiteLiZeroValue Z (-(m : ℤ)) := by
  unfold finiteLogDerivLiJet finiteLiZeroValue
  apply congrArg Multiset.sum
  refine Multiset.map_congr rfl ?_
  intro ρ hρ
  obtain ⟨hρ0, hρ1⟩ := hZ ρ hρ
  rw [weilLiTest_neg (m : ℤ) hρ0 hρ1,
    weilLiTest_nat_expansion m (sub_ne_zero.mpr hρ1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hsign : (-1 : ℂ) ^ (j + 1) = (-1 : ℂ) ^ (j - 1) := by
    rw [show j + 1 = (j - 1) + 2 by omega, pow_add]
    norm_num
  rw [hsign]

/-- The exact global analytic input still required to identify xi with its
genus-one divisor product. No inhabitant is asserted here. The first conjunct
records local uniform convergence of the primary-factor product; `A + B*s` is
the degree-at-most-one exponential quotient. -/
def XiGenusOneFactorization : Prop :=
  MultipliableLocallyUniformlyOn
      (fun ρ : XiZero ↦ fun s : ℂ ↦
        primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ)) Set.univ ∧
    ∃ A B : ℂ, ∀ s : ℂ,
      riemannXi s = Complex.exp (A + B * s) *
        ∏' ρ : XiZero,
          primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ)

end RHGarden
