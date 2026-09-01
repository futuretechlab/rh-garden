import RHGarden.LiHadamardFinite
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

noncomputable section

open Complex

namespace RHGarden

/-- The intrinsic genus-one primary factor attached to a distinct xi zero.
Multiplicity is represented by the exponent, rather than by repeating the index. -/
def xiPrimaryFactor (ρ : XiZero) (s : ℂ) : ℂ :=
  primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ)

theorem differentiable_xiPrimaryFactor (ρ : XiZero) :
    Differentiable ℂ (xiPrimaryFactor ρ) := by
  exact (differentiable_primaryFactorOne_div (ρ : ℂ)).pow _

theorem analyticAt_xiPrimaryFactor (ρ : XiZero) (s : ℂ) :
    AnalyticAt ℂ (xiPrimaryFactor ρ) s :=
  (differentiable_xiPrimaryFactor ρ).analyticAt s

@[simp] theorem xiPrimaryFactor_zero (ρ : XiZero) :
    xiPrimaryFactor ρ 0 = 1 := by
  simp [xiPrimaryFactor]

theorem xiPrimaryFactor_ne_zero {ρ : XiZero} {s : ℂ} (hs : s ≠ (ρ : ℂ)) :
    xiPrimaryFactor ρ s ≠ 0 := by
  apply pow_ne_zero
  rw [primaryFactorOne_ne_zero_iff]
  intro h
  exact hs ((div_eq_one_iff_eq ρ.ne_zero).mp h)

/-- The intrinsic genus-one canonical product over distinct xi zeros, with analytic
multiplicity carried by `xiPrimaryFactor`. This definition does not itself assert convergence. -/
noncomputable def xiCanonicalProduct (s : ℂ) : ℂ :=
  ∏' ρ : XiZero, xiPrimaryFactor ρ s

@[simp] theorem xiCanonicalProduct_zero : xiCanonicalProduct 0 = 1 := by
  simp [xiCanonicalProduct]

/-- Local uniform multipliability is the precise convergence input needed to make the
intrinsic xi canonical product entire. -/
theorem differentiable_xiCanonicalProduct
    (hprod : MultipliableLocallyUniformlyOn xiPrimaryFactor Set.univ) :
    Differentiable ℂ xiCanonicalProduct := by
  change Differentiable ℂ (fun s : ℂ ↦ ∏' ρ : XiZero, xiPrimaryFactor ρ s)
  have hdiff := hprod.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall <| by
      intro u
      simp only [xiPrimaryFactor, primaryFactorOne]
      fun_prop)
    isOpen_univ
  exact fun s ↦ (hdiff s (Set.mem_univ s)).differentiableAt Filter.univ_mem

/-- The logarithmic-derivative statement sufficient for the later Li-value
identification. It remains an open analytic proposition; no inhabitant is asserted. -/
def XiLogDerivPartialFraction : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, riemannXi s ≠ 0 →
    logDeriv riemannXi s =
      B + ∑' ρ : XiZero,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))

end RHGarden
