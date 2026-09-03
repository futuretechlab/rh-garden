import RHGarden.LiQuotientGrowth
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

noncomputable section

open Complex Filter Set
open scoped Topology

namespace RHGarden

/-- Differentiating the xi functional equation exchanges the derivatives at
zero and one with a minus sign. -/
theorem deriv_riemannXi_one_eq_neg_deriv_zero :
    deriv riemannXi 1 = -deriv riemannXi 0 := by
  have hfun : (fun z : ℂ ↦ riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hderiv := congrArg (fun f : ℂ → ℂ ↦ deriv f 0) hfun
  have hcomp :
      deriv (fun z : ℂ ↦ riemannXi (1 - z)) 0 =
        -(deriv riemannXi 1) := by
    change deriv (riemannXi ∘ fun z : ℂ ↦ 1 - z) 0 = _
    rw [deriv_comp 0 differentiable_riemannXi.differentiableAt (by fun_prop)]
    simp
  rw [hcomp] at hderiv
  calc
    deriv riemannXi 1 = -(-(deriv riemannXi 1)) := by ring
    _ = -deriv riemannXi 0 := congrArg Neg.neg hderiv

/-- Logarithmic derivatives at the two symmetry points differ by a minus
sign. -/
theorem logDeriv_riemannXi_one_eq_neg_zero :
    logDeriv riemannXi 1 = -logDeriv riemannXi 0 := by
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one, riemannXi_zero,
    deriv_riemannXi_one_eq_neg_deriv_zero]
  ring

/-- The finite genus-one corrected partial fraction in Lagarias height
ordering. -/
noncomputable def xiCorrectedPartialFraction (T : ℝ) (s : ℂ) : ℂ :=
  ((xiZeroHeightCutoff T).map fun ρ ↦
    1 / (s - ρ) + 1 / ρ).sum

private theorem xiCorrectedTerm_one_summable :
    Summable (fun a : XiZeroOccurrence ↦
      1 / ((1 : ℂ) - a.value) + 1 / a.value) := by
  have h := summable_logDeriv_xiOccurrencePrimaryFactor
    riemannXi_one_ne_zero
  exact h.congr fun a ↦ logDeriv_xiOccurrencePrimaryFactor
    (ne_comm.mpr a.1.ne_one)

private theorem xiCorrectedWeightedTerm_one_summable :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℂ) *
        (1 / ((1 : ℂ) - ρ) + 1 / ρ)) := by
  have h := xiCorrectedTerm_one_summable.sigma
  have h' : Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / ((1 : ℂ) - ρ)) +
        (xiMultiplicity (ρ : ℂ) : ℂ) * (1 / ρ)) := by
    simpa [XiZeroOccurrence.value, tsum_fintype, Finset.sum_const,
      nsmul_eq_mul] using h
  exact h'.congr fun ρ ↦ by ring

private theorem tsum_xiCorrectedTerm_one_eq_weighted :
    (∑' a : XiZeroOccurrence,
        (1 / ((1 : ℂ) - a.value) + 1 / a.value)) =
      ∑' ρ : XiZero,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / ((1 : ℂ) - ρ) + 1 / ρ) := by
  calc
    (∑' a : XiZeroOccurrence,
        (1 / ((1 : ℂ) - a.value) + 1 / a.value)) =
        ∑' ρ : XiZero, ∑' _i : Fin (xiMultiplicity (ρ : ℂ)),
          (1 / ((1 : ℂ) - ρ) + 1 / ρ) :=
      xiCorrectedTerm_one_summable.tsum_sigma
    _ = ∑' ρ : XiZero,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / ((1 : ℂ) - ρ) + 1 / ρ) := by
      apply tsum_congr
      intro ρ
      simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
      ring

private theorem xiCorrectedPartialFraction_eq_sum (T : ℝ) (s : ℂ) :
    xiCorrectedPartialFraction T s =
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          (1 / (s - ρ) + 1 / ρ) := by
  exact xiZeroHeightCutoff_map_sum_eq_sum T
    (fun ρ ↦ 1 / (s - ρ) + 1 / ρ)

/-- At `s = 1`, the height-ordered finite corrected fractions converge to
the exact occurrence-indexed corrected tsum. -/
theorem xiCorrectedPartialFraction_one_tendsto :
    Tendsto (fun T : ℝ ↦ xiCorrectedPartialFraction T 1) atTop
      (nhds (∑' a : XiZeroOccurrence,
        (1 / ((1 : ℂ) - a.value) + 1 / a.value))) := by
  rw [tsum_xiCorrectedTerm_one_eq_weighted]
  simpa only [xiCorrectedPartialFraction_eq_sum] using
    tendsto_xiZeroHeightFinset_sum xiCorrectedWeightedTerm_one_summable

/-- Reflection symmetry makes the finite corrected reciprocal sum exactly
twice the finite reciprocal star sum. -/
theorem xiCorrectedPartialFraction_one_eq_two_mul_reciprocalStarPartial
    (T : ℝ) :
    xiCorrectedPartialFraction T 1 = 2 * reciprocalStarPartial T := by
  have hfirst :
      ((xiZeroHeightCutoff T).map (fun ρ ↦ 1 / ((1 : ℂ) - ρ))).sum =
        reciprocalStarPartial T := by
    calc
      ((xiZeroHeightCutoff T).map
          (fun ρ ↦ 1 / ((1 : ℂ) - ρ))).sum =
          finiteLogDerivLiJet (xiZeroHeightCutoff T) 1 := by
        simp [finiteLogDerivLiJet]
      _ = finiteLiZeroValue (xiZeroHeightCutoff T) (-(1 : ℤ)) :=
        finiteLogDerivLiJet_eq_finiteLiZeroValue
          (xiZeroHeightCutoff T) (xiZeroHeightCutoff_valid T) 1
      _ = liStarPartial T (-(1 : ℤ)) := rfl
      _ = starRingEnd ℂ (liStarPartial T (1 : ℤ)) :=
        liStarPartial_neg T 1
      _ = starRingEnd ℂ (reciprocalStarPartial T) := by
        congr 1
        unfold liStarPartial finiteLiZeroValue reciprocalStarPartial
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro ρ _hρ
        simp [weilLiTest]
      _ = reciprocalStarPartial T := reciprocalStarPartial_conj T
  rw [xiCorrectedPartialFraction]
  rw [Multiset.sum_map_add]
  rw [hfirst]
  change reciprocalStarPartial T + reciprocalStarPartial T = _
  ring

/-- The formerly existential reciprocal-star limit has the exact value
`-logDeriv riemannXi 0`. -/
theorem reciprocalStarPartial_tendsto_neg_logDeriv_zero :
    Tendsto reciprocalStarPartial atTop
      (nhds (-logDeriv riemannXi 0)) := by
  have hsum :
      (∑' a : XiZeroOccurrence,
          (1 / ((1 : ℂ) - a.value) + 1 / a.value)) =
        -2 * logDeriv riemannXi 0 := by
    have hpf := logDeriv_riemannXi_eq_zero_value_add_zero_sum
      (s := (1 : ℂ)) riemannXi_one_ne_zero
    rw [logDeriv_riemannXi_one_eq_neg_zero] at hpf
    linear_combination -hpf
  have hcorrected :
      Tendsto (fun T : ℝ ↦ 2 * reciprocalStarPartial T) atTop
        (nhds (-2 * logDeriv riemannXi 0)) := by
    simpa only [xiCorrectedPartialFraction_one_eq_two_mul_reciprocalStarPartial,
      hsum] using xiCorrectedPartialFraction_one_tendsto
  have hscaled := hcorrected.mul_const (1 / 2 : ℂ)
  have hfun : (fun T : ℝ ↦
      2 * reciprocalStarPartial T * (1 / 2 : ℂ)) =
      reciprocalStarPartial := by
    funext T
    ring
  have hvalue :
      -2 * logDeriv riemannXi 0 * (1 / 2 : ℂ) =
        -logDeriv riemannXi 0 := by ring
  rw [hfun, hvalue] at hscaled
  exact hscaled

/-- The open set on which the xi logarithmic derivative and its partial
fractions are holomorphic. -/
def xiNonzeroSet : Set ℂ := {s | riemannXi s ≠ 0}

theorem isOpen_xiNonzeroSet : IsOpen xiNonzeroSet := by
  exact isOpen_ne_fun differentiable_riemannXi.continuous continuous_const

/-- The genus-one corrected occurrence fractions are normally summable on
the zero-free locus of xi. -/
theorem xiCorrectedOccurrence_summableLocallyUniformlyOn :
    SummableLocallyUniformlyOn
      (fun a : XiZeroOccurrence ↦ fun s : ℂ ↦
        1 / (s - a.value) + 1 / a.value)
      xiNonzeroSet := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    isOpen_xiNonzeroSet
  intro K hKsub hK
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right R₀ 1)
  let u : XiZeroOccurrence → ℝ := fun a ↦
    (2 * R) * (1 / ‖a.value‖ ^ 2)
  have hu : Summable u :=
    xiOccurrence_reciprocal_sq_summable.mul_left (2 * R)
  refine ⟨u, hu, ?_⟩
  have htend := xiOccurrence_reciprocal_sq_summable.tendsto_cofinite_zero
  have hthreshold : 0 < (1 / (4 * R ^ 2) : ℝ) := by positivity
  have hevent : ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
      1 / ‖a.value‖ ^ 2 < 1 / (4 * R ^ 2) :=
    htend.eventually (eventually_lt_nhds hthreshold)
  filter_upwards [hevent] with a ha s hsK
  have hsR : ‖s‖ ≤ R := (hR₀ s hsK).trans (le_max_left R₀ 1)
  have hsxi : riemannXi s ≠ 0 := hKsub hsK
  have hsa : s ≠ a.value := by
    intro h
    apply hsxi
    rw [h]
    exact (mem_xiDivisor_support_iff a.value).mp a.1.property
  have haNorm : 2 * R ≤ ‖a.value‖ := by
    by_contra hnot
    have halt : ‖a.value‖ < 2 * R := lt_of_not_ge hnot
    have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
    have hsq : ‖a.value‖ ^ 2 < 4 * R ^ 2 := by
      nlinarith [sq_nonneg ‖a.value‖]
    have hinv : 1 / (4 * R ^ 2) < 1 / ‖a.value‖ ^ 2 :=
      one_div_lt_one_div_of_lt (sq_pos_of_pos hapos) hsq
    exact (not_lt_of_ge hinv.le) ha
  have hhalf : ‖a.value‖ / 2 ≤ ‖s - a.value‖ := by
    have htri := norm_sub_norm_le a.value s
    rw [norm_sub_rev] at htri
    have hsHalf : ‖s‖ ≤ ‖a.value‖ / 2 := by nlinarith
    linarith
  have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
  have halg : 1 / (s - a.value) + 1 / a.value =
      s / (a.value * (s - a.value)) := by
    field_simp [a.value_ne_zero, sub_ne_zero.mpr hsa]
    ring
  rw [halg, norm_div, norm_mul]
  calc
    ‖s‖ / (‖a.value‖ * ‖s - a.value‖)
        ≤ ‖s‖ / (‖a.value‖ ^ 2 / 2) := by
          apply div_le_div_of_nonneg_left (norm_nonneg s) (by positivity)
          nlinarith
    _ = (2 * ‖s‖) * (1 / ‖a.value‖ ^ 2) := by
          field_simp [ne_of_gt hapos]
    _ ≤ (2 * R) * (1 / ‖a.value‖ ^ 2) := by gcongr
    _ = u a := rfl

/-- Occurrence indices selected by the same height ordering as the Lagarias
multiset cutoff. -/
noncomputable def xiOccurrenceHeightFinset (T : ℝ) :
    Finset XiZeroOccurrence :=
  (xiZeroHeightFinset T).sigma fun _ρ ↦ Finset.univ

theorem mem_xiOccurrenceHeightFinset_iff (T : ℝ)
    (a : XiZeroOccurrence) :
    a ∈ xiOccurrenceHeightFinset T ↔ |a.value.im| ≤ T := by
  simp [xiOccurrenceHeightFinset, mem_xiZeroHeightFinset_iff,
    XiZeroOccurrence.value]

theorem tendsto_xiOccurrenceHeightFinset_atTop :
    Tendsto xiOccurrenceHeightFinset atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro A
  filter_upwards [eventually_ge_atTop
      (∑ a ∈ A, |a.value.im|)] with T hT
  intro a ha
  rw [mem_xiOccurrenceHeightFinset_iff]
  exact le_trans (Finset.single_le_sum
    (fun (b : XiZeroOccurrence) (_ : b ∈ A) ↦ abs_nonneg b.value.im) ha) hT

private theorem xiCorrectedPartialFraction_eq_occurrence_sum
    (T : ℝ) (s : ℂ) :
    xiCorrectedPartialFraction T s =
      ∑ a ∈ xiOccurrenceHeightFinset T,
        (1 / (s - a.value) + 1 / a.value) := by
  rw [xiCorrectedPartialFraction_eq_sum]
  classical
  rw [xiOccurrenceHeightFinset, Finset.sum_sigma]
  simp [XiZeroOccurrence.value, Finset.sum_const, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro ρ _hρ
  ring

/-- Height-ordered corrected partial fractions converge locally uniformly on
the zero-free locus to their occurrence-indexed tsum. -/
theorem xiCorrectedPartialFraction_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn xiCorrectedPartialFraction
      (fun s : ℂ ↦ ∑' a : XiZeroOccurrence,
        (1 / (s - a.value) + 1 / a.value))
      atTop xiNonzeroSet := by
  have hsum :=
    xiCorrectedOccurrence_summableLocallyUniformlyOn.hasSumLocallyUniformlyOn
  have hheight :
      TendstoLocallyUniformlyOn
        (fun T : ℝ ↦ fun s : ℂ ↦
          ∑ a ∈ xiOccurrenceHeightFinset T,
            (1 / (s - a.value) + 1 / a.value))
        (fun s : ℂ ↦ ∑' a : XiZeroOccurrence,
          (1 / (s - a.value) + 1 / a.value))
        atTop xiNonzeroSet := by
    intro V hV s hs
    obtain ⟨t, ht, hfin⟩ := hsum V hV s hs
    exact ⟨t, ht, tendsto_xiOccurrenceHeightFinset_atTop.eventually hfin⟩
  exact hheight.congr fun T s _hs ↦
    (xiCorrectedPartialFraction_eq_occurrence_sum T s).symm

/-- Corrected height partial fractions converge locally uniformly to the xi
logarithmic derivative minus its value at zero. -/
theorem xiCorrectedPartialFraction_tendstoLocallyUniformlyOn_logDeriv_sub_zero :
    TendstoLocallyUniformlyOn xiCorrectedPartialFraction
      (fun s : ℂ ↦ logDeriv riemannXi s - logDeriv riemannXi 0)
      atTop xiNonzeroSet := by
  apply xiCorrectedPartialFraction_tendstoLocallyUniformlyOn.congr_right
  intro s hs
  have hpf := logDeriv_riemannXi_eq_zero_value_add_zero_sum hs
  linear_combination -hpf

/-- The finite uncorrected partial fraction in Lagarias height ordering. -/
noncomputable def xiPartialFraction (T : ℝ) (s : ℂ) : ℂ :=
  ((xiZeroHeightCutoff T).map fun ρ ↦ 1 / (s - ρ)).sum

theorem xiPartialFraction_eq_sum (T : ℝ) (s : ℂ) :
    xiPartialFraction T s =
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ)) := by
  exact xiZeroHeightCutoff_map_sum_eq_sum T (fun ρ ↦ 1 / (s - ρ))

theorem xiPartialFraction_eq_corrected_sub_reciprocal
    (T : ℝ) (s : ℂ) :
    xiPartialFraction T s =
      xiCorrectedPartialFraction T s - reciprocalStarPartial T := by
  rw [xiPartialFraction, xiCorrectedPartialFraction, reciprocalStarPartial,
    Multiset.sum_map_add]
  ring

/-- The finite uncorrected height partial fractions converge locally uniformly
to the exact logarithmic derivative of xi on its zero-free locus. -/
theorem xiPartialFraction_tendstoLocallyUniformlyOn_logDeriv :
    TendstoLocallyUniformlyOn xiPartialFraction (logDeriv riemannXi)
      atTop xiNonzeroSet := by
  have hconstant :
      TendstoLocallyUniformlyOn
        (fun T : ℝ ↦ fun _s : ℂ ↦ reciprocalStarPartial T)
        (fun _s : ℂ ↦ -logDeriv riemannXi 0)
        atTop xiNonzeroSet :=
    ((reciprocalStarPartial_tendsto_neg_logDeriv_zero).tendstoUniformlyOn_const
      xiNonzeroSet).tendstoLocallyUniformlyOn
  have hsub :=
    xiCorrectedPartialFraction_tendstoLocallyUniformlyOn_logDeriv_sub_zero.sub
      hconstant
  have hleft := hsub.congr fun T s _hs ↦
    (xiPartialFraction_eq_corrected_sub_reciprocal T s).symm
  apply hleft.congr_right
  intro s _hs
  simp only [Pi.sub_apply]
  ring

/-- Every finite height partial fraction is holomorphic to all orders on the
zero-free locus. -/
theorem contDiffOn_xiPartialFraction (T : ℝ) :
    ContDiffOn ℂ ⊤ (xiPartialFraction T) xiNonzeroSet := by
  rw [show xiPartialFraction T = fun s : ℂ ↦
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ)) from
    funext (xiPartialFraction_eq_sum T)]
  apply ContDiffOn.sum
  intro ρ _hρ
  apply contDiffOn_const.mul
  have hsub : ContDiffOn ℂ ⊤ (fun s : ℂ ↦ s - (ρ : ℂ)) xiNonzeroSet :=
    contDiffOn_id.sub contDiffOn_const
  exact contDiffOn_const.div hsub fun s hs ↦ by
    apply sub_ne_zero.mpr
    intro h
    apply hs
    rw [h]
    exact (mem_xiDivisor_support_iff (ρ : ℂ)).mp ρ.property

theorem differentiableOn_iteratedDeriv_xiPartialFraction
    (T : ℝ) (m : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv m (xiPartialFraction T))
      xiNonzeroSet := by
  have hwithin := (contDiffOn_xiPartialFraction T)
    |>.differentiableOn_iteratedDerivWithin
      (m := m) (by simp) isOpen_xiNonzeroSet.uniqueDiffOn
  exact hwithin.congr fun s hs ↦
    (iteratedDerivWithin_of_isOpen isOpen_xiNonzeroSet hs).symm

/-- Local uniform convergence of the partial fractions transports through
every fixed iterated derivative. -/
theorem iteratedDeriv_xiPartialFraction_tendstoLocallyUniformlyOn
    (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ ↦ iteratedDeriv m (xiPartialFraction T))
      (iteratedDeriv m (logDeriv riemannXi)) atTop xiNonzeroSet := by
  induction m with
  | zero =>
      simpa [iteratedDeriv_zero] using
        xiPartialFraction_tendstoLocallyUniformlyOn_logDeriv
  | succ m ih =>
      have hderiv := ih.deriv
        (Filter.Eventually.of_forall fun T ↦
          differentiableOn_iteratedDeriv_xiPartialFraction T m)
        isOpen_xiNonzeroSet
      simpa [iteratedDeriv_succ, Function.comp_def] using hderiv

/-- Pointwise derivative transport at the normalization point `s = 1`. -/
theorem iteratedDeriv_xiPartialFraction_tendsto (m : ℕ) :
    Tendsto
      (fun T : ℝ ↦ iteratedDeriv m (xiPartialFraction T) 1)
      atTop (nhds (iteratedDeriv m (logDeriv riemannXi) 1)) :=
  (iteratedDeriv_xiPartialFraction_tendstoLocallyUniformlyOn m).tendsto_at
    riemannXi_one_ne_zero

/-- The normalized finite jet of a logarithmic derivative at `s = 1` that
occurs in Li's differential formula. -/
noncomputable def logDerivLiJet (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 m,
    (Nat.choose m j : ℂ) * iteratedDeriv (j - 1) f 1 /
      ((j - 1).factorial : ℂ)

private theorem iteratedDeriv_one_div_sub_at_one
    (k : ℕ) (ρ : ℂ) :
    iteratedDeriv k (fun s : ℂ ↦ 1 / (s - ρ)) 1 =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) / (1 - ρ) ^ (k + 1) := by
  rw [congrFun (iteratedDeriv_comp_sub_const k (fun y : ℂ ↦ 1 / y) ρ) 1]
  have h := iteratedDerivWithin_one_div (s := Set.univ) k isOpen_univ
      (Set.mem_univ (1 - ρ : ℂ))
  rw [iteratedDerivWithin_univ] at h
  rw [h]
  have hz : (1 - ρ) ^ (-1 - (k : ℤ)) =
      ((1 - ρ) ^ (k + 1))⁻¹ := by
    rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega,
      zpow_neg (1 - ρ) ((k + 1 : ℕ) : ℤ), zpow_natCast]
  change (-1 : ℂ) ^ k * (k.factorial : ℂ) *
      (1 - ρ) ^ (-1 - (k : ℤ)) = _
  rw [hz]
  simp only [div_eq_mul_inv]

private theorem iteratedDeriv_xiPartialFraction_eq_sum
    (T : ℝ) (k : ℕ) :
    iteratedDeriv k (xiPartialFraction T) 1 =
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) *
          ((-1 : ℂ) ^ k * (k.factorial : ℂ) /
            (1 - (ρ : ℂ)) ^ (k + 1)) := by
  rw [show xiPartialFraction T = fun s : ℂ ↦
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) * (1 / (s - ρ)) from
    funext (xiPartialFraction_eq_sum T)]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro ρ _hρ
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_one_div_sub_at_one k (ρ : ℂ)]
  · intro ρ _hρ
    apply contDiffAt_const.mul
    exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.mpr ρ.ne_one.symm)

/-- The normalized derivative jet of a finite height partial fraction is the
existing finite Lagarias Li jet of the same zero multiset. -/
theorem logDerivLiJet_xiPartialFraction_eq_finiteLogDerivLiJet
    (T : ℝ) (m : ℕ) :
    logDerivLiJet m (xiPartialFraction T) =
      finiteLogDerivLiJet (xiZeroHeightCutoff T) m := by
  rw [logDerivLiJet, finiteLogDerivLiJet,
    xiZeroHeightCutoff_map_sum_eq_sum]
  simp_rw [iteratedDeriv_xiPartialFraction_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _hρ
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hfac : (((j - 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (j - 1)
  rw [show j - 1 + 1 = j by omega]
  field_simp

private theorem eventually_deriv_standardXiLog_eq_logDeriv :
    ∀ᶠ s in nhds (1 : ℂ),
      deriv standardXiLog s = logDeriv riemannXi s := by
  have hxi : ∀ᶠ s in nhds (1 : ℂ), riemannXi s ∈ Complex.slitPlane :=
    differentiable_riemannXi.continuous.continuousAt
      (Complex.isOpen_slitPlane.mem_nhds riemannXi_one_mem_slitPlane)
  filter_upwards [hxi] with s hs
  rw [show standardXiLog = Complex.log ∘ riemannXi by
      ext z; rfl,
    Complex.deriv_log_comp_eq_logDeriv
      differentiable_riemannXi.differentiableAt hs]

private theorem iteratedDeriv_standardXiLog_eq_logDeriv
    (j : ℕ) (hj : 1 ≤ j) :
    iteratedDeriv j standardXiLog 1 =
      iteratedDeriv (j - 1) (logDeriv riemannXi) 1 := by
  rw [show j = (j - 1) + 1 by omega, iteratedDeriv_succ']
  exact Filter.EventuallyEq.iteratedDeriv_eq (j - 1)
    eventually_deriv_standardXiLog_eq_logDeriv

private theorem sum_Icc_one_succ_eq_sum_range_reflect
    (f : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 (n + 1), f j =
      ∑ i ∈ Finset.range (n + 1), f (n + 1 - i) := by
  have hIcc : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
    ext j
    simp
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [show n + 2 - 1 = n + 1 by omega]
  rw [← Finset.sum_range_reflect (fun i ↦ f (1 + i)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  congr 1
  omega

/-- The limiting normalized logarithmic-derivative jet is exactly the
zero-based classical Li coefficient. -/
theorem logDerivLiJet_logDeriv_riemannXi_eq_classicalLiCoefficient
    (n : ℕ) :
    logDerivLiJet (n + 1) (logDeriv riemannXi) =
      classicalLiCoefficient n := by
  rw [logDerivLiJet]
  rw [sum_Icc_one_succ_eq_sum_range_reflect
    (f := fun j ↦ (Nat.choose (n + 1) j : ℂ) *
      iteratedDeriv (j - 1) (logDeriv riemannXi) 1 /
        ((j - 1).factorial : ℂ)) (n := n)]
  rw [classicalLiCoefficient]
  change _ = iteratedDeriv (n + 1)
      ((fun s : ℂ ↦ s ^ n) * standardXiLog) 1 /
        (n.factorial : ℂ)
  rw [iteratedDeriv_mul]
  · rw [Finset.sum_div]
    nth_rewrite 2 [Finset.sum_range_succ]
    have hlast :
        ((Nat.choose (n + 1) (n + 1) : ℂ) *
            iteratedDeriv (n + 1) (fun s : ℂ ↦ s ^ n) 1 *
            iteratedDeriv (n + 1 - (n + 1)) standardXiLog 1) /
          (n.factorial : ℂ) = 0 := by
      rw [iteratedDeriv_pow]
      simp
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hile : i ≤ n := by omega
    have hisub : 1 ≤ n + 1 - i := by omega
    rw [iteratedDeriv_pow, one_pow, mul_one,
      iteratedDeriv_standardXiLog_eq_logDeriv (n + 1 - i) hisub]
    rw [Nat.choose_symm (show i ≤ n + 1 by omega)]
    rw [show n + 1 - i - 1 = n - i by omega]
    have hfacsub : (((n - i).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - i)
    have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hid : (((n - i).factorial : ℕ) : ℂ) *
        (n.descFactorial i : ℂ) = (n.factorial : ℂ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hile
    field_simp
    rw [← hid]
    ring
  · fun_prop
  · exact analyticAt_standardXiLog.contDiffAt

/-- The locally uniform partial-fraction limit transports through the whole
finite normalized Li jet. -/
theorem logDerivLiJet_xiPartialFraction_tendsto (m : ℕ) :
    Tendsto (fun T : ℝ ↦ logDerivLiJet m (xiPartialFraction T)) atTop
      (nhds (logDerivLiJet m (logDeriv riemannXi))) := by
  unfold logDerivLiJet
  apply tendsto_finsetSum
  intro j _hj
  exact (Filter.Tendsto.const_mul (Nat.choose m j : ℂ)
    (iteratedDeriv_xiPartialFraction_tendsto (j - 1))).div_const
      ((j - 1).factorial : ℂ)

/-- The finite Lagarias jets in exact height ordering converge to the
classical Li coefficient. -/
theorem finiteLogDerivLiJet_tendsto_classicalLiCoefficient (n : ℕ) :
    Tendsto
      (fun T : ℝ ↦ finiteLogDerivLiJet (xiZeroHeightCutoff T) (n + 1))
      atTop (nhds (classicalLiCoefficient n)) := by
  have h := logDerivLiJet_xiPartialFraction_tendsto (n + 1)
  rw [logDerivLiJet_logDeriv_riemannXi_eq_classicalLiCoefficient n] at h
  exact h.congr' (Filter.Eventually.of_forall fun T ↦
    logDerivLiJet_xiPartialFraction_eq_finiteLogDerivLiJet T (n + 1))

/-- The classical Li coefficient is the exact negative-index Lagarias star
limit, in the project's zero-based indexing. -/
theorem classicalLiEqualsNegativeStar :
    ClassicalLiEqualsNegativeStar := by
  intro n
  unfold LiStarConvergesTo liStarPartial
  have h := finiteLogDerivLiJet_tendsto_classicalLiCoefficient n
  exact h.congr' (Filter.Eventually.of_forall fun T ↦
    finiteLogDerivLiJet_eq_finiteLiZeroValue
      (xiZeroHeightCutoff T) (xiZeroHeightCutoff_valid T) (n + 1))

/-- By conjugation symmetry and reality, the same classical coefficient is
also the positive-index Lagarias star limit. -/
theorem classicalLiEqualsPositiveStar (n : ℕ) :
    LiStarConvergesTo (((n + 1 : ℕ) : ℤ)) (classicalLiCoefficient n) := by
  have h := (classicalLiEqualsNegativeStar n).neg
  simpa [classicalLiCoefficient_conj] using h

end RHGarden
