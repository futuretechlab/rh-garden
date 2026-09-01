import RHGarden.LiHadamardFinite
import RHGarden.Zeta23LocalCount
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

noncomputable section

open Complex

namespace RHGarden

/-- One occurrence of a distinct xi zero. The finite second coordinate expands
the analytic multiplicity into separate product indices. -/
abbrev XiZeroOccurrence := Σ ρ : XiZero, Fin (xiMultiplicity (ρ : ℂ))

namespace XiZeroOccurrence

def zero (a : XiZeroOccurrence) : XiZero := a.1

def value (a : XiZeroOccurrence) : ℂ := (a.1 : ℂ)

theorem value_ne_zero (a : XiZeroOccurrence) : a.value ≠ 0 := a.1.ne_zero

end XiZeroOccurrence

/-- The genus-one primary factor belonging to one occurrence of a xi zero. -/
def xiOccurrencePrimaryFactor (a : XiZeroOccurrence) (s : ℂ) : ℂ :=
  primaryFactorOne (s / a.value)

theorem differentiable_xiOccurrencePrimaryFactor (a : XiZeroOccurrence) :
    Differentiable ℂ (xiOccurrencePrimaryFactor a) :=
  differentiable_primaryFactorOne_div a.value

theorem analyticAt_xiOccurrencePrimaryFactor (a : XiZeroOccurrence) (s : ℂ) :
    AnalyticAt ℂ (xiOccurrencePrimaryFactor a) s :=
  (differentiable_xiOccurrencePrimaryFactor a).analyticAt s

@[simp] theorem xiOccurrencePrimaryFactor_zero (a : XiZeroOccurrence) :
    xiOccurrencePrimaryFactor a 0 = 1 := by
  simp [xiOccurrencePrimaryFactor]

theorem xiOccurrencePrimaryFactor_ne_zero {a : XiZeroOccurrence} {s : ℂ}
    (hs : s ≠ a.value) : xiOccurrencePrimaryFactor a s ≠ 0 := by
  rw [xiOccurrencePrimaryFactor, primaryFactorOne_ne_zero_iff]
  intro h
  exact hs ((div_eq_one_iff_eq a.value_ne_zero).mp h)

/-- The factor deviation used in the locally uniform product M-test. -/
def xiOccurrencePrimaryDelta (a : XiZeroOccurrence) (s : ℂ) : ℂ :=
  xiOccurrencePrimaryFactor a s - 1

/-- Unconditional multiplicity-weighted reciprocal-square summability, obtained by
applying the Zeta23 local zero-count theorem to the existing general result. -/
theorem xi_reciprocal_sq_summable_unconditional :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
  xi_reciprocal_sq_summable xiLocalZeroCountBound

/-- Expanding every zero into its finitely many multiplicity occurrences turns the
weighted reciprocal-square series into an ordinary summable series. -/
theorem xiOccurrence_reciprocal_sq_summable :
    Summable (fun a : XiZeroOccurrence ↦ 1 / ‖a.value‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  constructor
  · intro ρ
    exact (hasSum_fintype fun _ : Fin (xiMultiplicity (ρ : ℂ)) ↦
      1 / ‖(ρ : ℂ)‖ ^ 2).summable
  · simpa [XiZeroOccurrence.value, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul,
      div_eq_mul_inv, mul_comm] using xi_reciprocal_sq_summable_unconditional

/-- Quadratic small-argument estimate for the genus-one factor.

The proof is native to RH Garden. Its decomposition follows the elementary-factor estimate in
`PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/WeierstrassFactor.lean`, repository
`leibniz-rs/PrimeNumberTheoremAnd`, commit
`8dc50485d7166be58b05ee0d54216c06a4b3aef9` (Apache-2.0). -/
theorem norm_primaryFactorOne_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖primaryFactorOne w - 1‖ ≤ 4 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ ≤ 1 := hw.trans (by norm_num)
  have hrem := Complex.norm_exp_sub_one_sub_id_le hw1
  have hlin := Complex.norm_exp_sub_one_le hw1
  have hid : primaryFactorOne w - 1 =
      (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by
    simp only [primaryFactorOne]
    ring
  rw [hid]
  calc
    ‖(Complex.exp w - 1 - w) - w * (Complex.exp w - 1)‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
      gcongr
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hlin (norm_nonneg w)
    _ ≤ 4 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]

private theorem xiOccurrencePrimaryDelta_compact_majorant
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ u : XiZeroOccurrence → ℝ, Summable u ∧
      ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
        ∀ s ∈ K, ‖xiOccurrencePrimaryDelta a s‖ ≤ u a := by
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right R₀ 1)
  let u : XiZeroOccurrence → ℝ := fun a ↦
    (4 * R ^ 2) * (1 / ‖a.value‖ ^ 2)
  have hu : Summable u :=
    xiOccurrence_reciprocal_sq_summable.mul_left (4 * R ^ 2)
  refine ⟨u, hu, ?_⟩
  have htend := xiOccurrence_reciprocal_sq_summable.tendsto_cofinite_zero
  have hthreshold : 0 < (1 / (4 * R ^ 2) : ℝ) := by positivity
  have hevent : ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
      1 / ‖a.value‖ ^ 2 < 1 / (4 * R ^ 2) :=
    htend.eventually (eventually_lt_nhds hthreshold)
  filter_upwards [hevent] with a ha s hsK
  have hsR : ‖s‖ ≤ R := (hR₀ s hsK).trans (le_max_left R₀ 1)
  have haNorm : 2 * R ≤ ‖a.value‖ := by
    by_contra hnot
    have halt : ‖a.value‖ < 2 * R := lt_of_not_ge hnot
    have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
    have hsq : ‖a.value‖ ^ 2 < 4 * R ^ 2 := by nlinarith [sq_nonneg ‖a.value‖]
    have hinv : 1 / (4 * R ^ 2) < 1 / ‖a.value‖ ^ 2 :=
      one_div_lt_one_div_of_lt (sq_pos_of_pos hapos) hsq
    exact (not_lt_of_ge hinv.le) ha
  have hratio : ‖s / a.value‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div]
    have hden : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
    calc
      ‖s‖ / ‖a.value‖ ≤ R / ‖a.value‖ :=
        div_le_div_of_nonneg_right hsR hden.le
      _ ≤ R / (2 * R) := by
        exact div_le_div_of_nonneg_left hR.le (by positivity) haNorm
      _ = 1 / 2 := by field_simp
  have hE := norm_primaryFactorOne_sub_one_le hratio
  calc
    ‖xiOccurrencePrimaryDelta a s‖
        ≤ 4 * ‖s / a.value‖ ^ 2 := by
          simpa [xiOccurrencePrimaryDelta, xiOccurrencePrimaryFactor] using hE
    _ = 4 * ‖s‖ ^ 2 * (1 / ‖a.value‖ ^ 2) := by
          rw [norm_div]
          field_simp [norm_ne_zero_iff.mpr a.value_ne_zero]
    _ ≤ (4 * R ^ 2) * (1 / ‖a.value‖ ^ 2) := by
          gcongr
    _ = u a := rfl

/-- The occurrence-factor deviations are summable locally uniformly on the plane. -/
theorem xiOccurrencePrimaryDelta_summableLocallyUniformly :
    SummableLocallyUniformlyOn xiOccurrencePrimaryDelta Set.univ := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
    (g := fun s ↦ ∑' a : XiZeroOccurrence, xiOccurrencePrimaryDelta a s)
  apply hasSumLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hKuniv hK
  obtain ⟨u, hu, hbound⟩ := xiOccurrencePrimaryDelta_compact_majorant K hK
  exact HasSumUniformlyOn.of_norm_le_summable_eventually hu hbound

/-- The intrinsic genus-one product over zero occurrences converges locally uniformly. -/
theorem xiOccurrencePrimaryFactors_multipliableLocallyUniformly :
    MultipliableLocallyUniformlyOn xiOccurrencePrimaryFactor Set.univ := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _hKuniv hK
  obtain ⟨u, hu, hbound⟩ := xiOccurrencePrimaryDelta_compact_majorant K hK
  have hprod := Summable.hasProdUniformlyOn_one_add hK hu hbound
    (fun a ↦ ((differentiable_xiOccurrencePrimaryFactor a).continuous.sub
      continuous_const).continuousOn)
  simpa [xiOccurrencePrimaryDelta] using hprod

/-- The locally uniformly convergent genus-one canonical product indexed by zero occurrences. -/
noncomputable def xiCanonicalProductOccurrences (s : ℂ) : ℂ :=
  ∏' a : XiZeroOccurrence, xiOccurrencePrimaryFactor a s

@[simp] theorem xiCanonicalProductOccurrences_zero :
    xiCanonicalProductOccurrences 0 = 1 := by
  simp [xiCanonicalProductOccurrences]

theorem differentiable_xiCanonicalProductOccurrences :
    Differentiable ℂ xiCanonicalProductOccurrences := by
  change Differentiable ℂ (fun s : ℂ ↦
    ∏' a : XiZeroOccurrence, xiOccurrencePrimaryFactor a s)
  have hdiff :=
    xiOccurrencePrimaryFactors_multipliableLocallyUniformly.hasProdLocallyUniformlyOn
      |>.differentiableOn
        (.of_forall <| by
          intro u
          simp only [xiOccurrencePrimaryFactor, primaryFactorOne]
          fun_prop)
        isOpen_univ
  exact fun s ↦ (hdiff s (Set.mem_univ s)).differentiableAt Filter.univ_mem

/-- The occurrence canonical product is nonzero away from the xi divisor. -/
theorem xiCanonicalProductOccurrences_ne_zero {s : ℂ} (hs : riemannXi s ≠ 0) :
    xiCanonicalProductOccurrences s ≠ 0 := by
  have hsρ : ∀ a : XiZeroOccurrence, s ≠ a.value := by
    intro a h
    apply hs
    rw [h]
    exact (mem_xiDivisor_support_iff a.value).mp a.1.property
  have hdelta := xiOccurrencePrimaryDelta_summableLocallyUniformly.summable
    (x := s) (Set.mem_univ s)
  have hne := tprod_one_add_ne_zero_of_summable
    (f := fun a : XiZeroOccurrence ↦ xiOccurrencePrimaryDelta a s)
    (fun a ↦ by
      simpa [xiOccurrencePrimaryDelta] using xiOccurrencePrimaryFactor_ne_zero (hsρ a))
    hdelta.norm
  simpa [xiCanonicalProductOccurrences, xiOccurrencePrimaryDelta] using hne

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

theorem logDeriv_xiOccurrencePrimaryFactor {a : XiZeroOccurrence} {s : ℂ}
    (hs : s ≠ a.value) :
    logDeriv (xiOccurrencePrimaryFactor a) s =
      1 / (s - a.value) + 1 / a.value := by
  rw [show xiOccurrencePrimaryFactor a =
    (fun z : ℂ ↦ primaryFactorOne (z / a.value)) from rfl]
  exact logDeriv_primaryFactorOne_div a.value_ne_zero hs

/-- Away from the xi divisor, the occurrence-factor logarithmic derivatives form
an absolutely summable series. -/
theorem summable_logDeriv_xiOccurrencePrimaryFactor {s : ℂ}
    (hs : riemannXi s ≠ 0) :
    Summable (fun a : XiZeroOccurrence ↦
      logDeriv (xiOccurrencePrimaryFactor a) s) := by
  have hsρ : ∀ a : XiZeroOccurrence, s ≠ a.value := by
    intro a h
    apply hs
    rw [h]
    exact (mem_xiDivisor_support_iff a.value).mp a.1.property
  let R : ℝ := max ‖s‖ 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right ‖s‖ 1)
  have hsR : ‖s‖ ≤ R := le_max_left ‖s‖ 1
  let u : XiZeroOccurrence → ℝ := fun a ↦
    (2 * ‖s‖) * (1 / ‖a.value‖ ^ 2)
  have hu : Summable u :=
    xiOccurrence_reciprocal_sq_summable.mul_left (2 * ‖s‖)
  refine Summable.of_norm_bounded_eventually hu ?_
  have htend := xiOccurrence_reciprocal_sq_summable.tendsto_cofinite_zero
  have hthreshold : 0 < (1 / (4 * R ^ 2) : ℝ) := by positivity
  have hevent : ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
      1 / ‖a.value‖ ^ 2 < 1 / (4 * R ^ 2) :=
    htend.eventually (eventually_lt_nhds hthreshold)
  filter_upwards [hevent] with a ha
  have haNorm : 2 * R ≤ ‖a.value‖ := by
    by_contra hnot
    have halt : ‖a.value‖ < 2 * R := lt_of_not_ge hnot
    have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
    have hsq : ‖a.value‖ ^ 2 < 4 * R ^ 2 := by nlinarith [sq_nonneg ‖a.value‖]
    have hinv : 1 / (4 * R ^ 2) < 1 / ‖a.value‖ ^ 2 :=
      one_div_lt_one_div_of_lt (sq_pos_of_pos hapos) hsq
    exact (not_lt_of_ge hinv.le) ha
  have hhalf : ‖a.value‖ / 2 ≤ ‖s - a.value‖ := by
    have htri := norm_sub_norm_le a.value s
    rw [norm_sub_rev] at htri
    have hsHalf : ‖s‖ ≤ ‖a.value‖ / 2 := by nlinarith
    linarith
  have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
  have hdiffpos : 0 < ‖s - a.value‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hsρ a))
  rw [logDeriv_xiOccurrencePrimaryFactor (hsρ a)]
  have halg : 1 / (s - a.value) + 1 / a.value =
      s / (a.value * (s - a.value)) := by
    field_simp [a.value_ne_zero, sub_ne_zero.mpr (hsρ a)]
    ring
  rw [halg, norm_div, norm_mul]
  calc
    ‖s‖ / (‖a.value‖ * ‖s - a.value‖)
        ≤ ‖s‖ / (‖a.value‖ ^ 2 / 2) := by
          apply div_le_div_of_nonneg_left (norm_nonneg s) (by positivity)
          nlinarith
    _ = (2 * ‖s‖) * (1 / ‖a.value‖ ^ 2) := by
          field_simp [ne_of_gt hapos]
    _ = u a := rfl

/-- Exact partial-fraction expansion for the logarithmic derivative of the
locally uniformly convergent occurrence canonical product. -/
theorem logDeriv_xiCanonicalProductOccurrences {s : ℂ}
    (hs : riemannXi s ≠ 0) :
    logDeriv xiCanonicalProductOccurrences s =
      ∑' a : XiZeroOccurrence,
        (1 / (s - a.value) + 1 / a.value) := by
  rw [show xiCanonicalProductOccurrences =
      (fun z : ℂ ↦ ∏' a : XiZeroOccurrence, xiOccurrencePrimaryFactor a z) from rfl]
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ s)
    (fun a ↦ xiOccurrencePrimaryFactor_ne_zero (by
      intro h
      apply hs
      rw [h]
      exact (mem_xiDivisor_support_iff a.value).mp a.1.property))
    (fun a ↦ (differentiable_xiOccurrencePrimaryFactor a).differentiableOn)
    (summable_logDeriv_xiOccurrencePrimaryFactor hs)
    xiOccurrencePrimaryFactors_multipliableLocallyUniformly
    (xiCanonicalProductOccurrences_ne_zero hs)]
  apply tsum_congr
  intro a
  exact logDeriv_xiOccurrencePrimaryFactor (by
    intro h
    apply hs
    rw [h]
    exact (mem_xiDivisor_support_iff a.value).mp a.1.property)

/-- Occurrence-indexed form of the open xi logarithmic-derivative identification.
The canonical-product summand is now fully justified; only its equality with the xi
logarithmic derivative up to an affine constant remains open. -/
def XiLogDerivPartialFractionOccurrences : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, riemannXi s ≠ 0 →
    logDeriv riemannXi s =
      B + ∑' a : XiZeroOccurrence,
        (1 / (s - a.value) + 1 / a.value)

/-- The logarithmic-derivative statement sufficient for the later Li-value
identification. It remains an open analytic proposition; no inhabitant is asserted. -/
def XiLogDerivPartialFraction : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, riemannXi s ≠ 0 →
    logDeriv riemannXi s =
      B + ∑' ρ : XiZero,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))

end RHGarden
