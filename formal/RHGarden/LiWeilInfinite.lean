import RHGarden.LiStarIdentification

noncomputable section

open Complex Filter Set
open scoped Topology

namespace RHGarden

/-- The real-even integer extension of the zero-based classical Li sequence.
The indices `±(k+1)` both carry `classicalLiCoefficient k`. -/
def classicalLiSigned : ℤ → ℂ
  | .ofNat 0 => 0
  | .ofNat (k + 1) => classicalLiCoefficient k
  | .negSucc k => classicalLiCoefficient k

@[simp] theorem classicalLiSigned_zero : classicalLiSigned 0 = 0 := rfl

@[simp] theorem classicalLiSigned_ofNat_succ (k : ℕ) :
    classicalLiSigned ((k + 1 : ℕ) : ℤ) = classicalLiCoefficient k := rfl

@[simp] theorem classicalLiSigned_negSucc (k : ℕ) :
    classicalLiSigned (.negSucc k) = classicalLiCoefficient k := rfl

theorem classicalLiSigned_neg (n : ℤ) :
    classicalLiSigned (-n) = classicalLiSigned n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => simp
      | succ k =>
          change classicalLiSigned (Int.negSucc k) =
            classicalLiSigned (Int.ofNat (Nat.succ k))
          rfl
  | negSucc k =>
      change classicalLiSigned (Int.ofNat (Nat.succ k)) =
        classicalLiSigned (Int.negSucc k)
      rfl

/-- Every integer-indexed Lagarias height star sum converges to the single
signed classical Li sequence. -/
theorem liStarConvergesTo_classicalLiSigned (n : ℤ) :
    LiStarConvergesTo n (classicalLiSigned n) := by
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          unfold LiStarConvergesTo liStarPartial finiteLiZeroValue
          simpa using tendsto_const_nhds
      | succ k =>
          simpa [classicalLiSigned] using classicalLiEqualsPositiveStar k
  | negSucc k =>
      have h := classicalLiEqualsNegativeStar k
      change LiStarConvergesTo (-(((k + 1 : ℕ) : ℤ)))
        (classicalLiCoefficient k)
      exact h

private theorem norm_weilLiTest_natCast_le_inv_norm
    (m : ℕ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖weilLiTest (m : ℤ) z‖ ≤
      (∑ k ∈ Finset.Icc 1 m,
        ‖((-1 : ℂ) ^ (k + 1) * Nat.choose m k)‖) / ‖z‖ := by
  have hz0 : z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hz))
  rw [weilLiTest_nat_expansion m hz0]
  calc
    ‖∑ k ∈ Finset.Icc 1 m,
        (-1 : ℂ) ^ (k + 1) * Nat.choose m k / z ^ k‖ ≤
        ∑ k ∈ Finset.Icc 1 m,
          ‖(-1 : ℂ) ^ (k + 1) * Nat.choose m k / z ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 m,
        ‖(-1 : ℂ) ^ (k + 1) * Nat.choose m k‖ / ‖z‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _)
        (lt_of_lt_of_le zero_lt_one hz)
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      have hp : 1 ≤ ‖z‖ ^ (k - 1) := one_le_pow₀ hz
      nlinarith [norm_nonneg z]
    _ = _ := by rw [Finset.sum_div]

/-- Every fixed integer-indexed Li test is `O(1 / |ρ|)` on xi zeros.
The radius `2` is chosen so negative indices can be reflected without any
small-denominator issue. -/
theorem norm_weilLiTest_le_inv_norm (n : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : XiZero, 2 ≤ ‖(ρ : ℂ)‖ →
      ‖weilLiTest n (ρ : ℂ)‖ ≤ C / ‖(ρ : ℂ)‖ := by
  cases n with
  | ofNat m =>
      let C : ℝ := ∑ k ∈ Finset.Icc 1 m,
        ‖((-1 : ℂ) ^ (k + 1) * Nat.choose m k)‖
      refine ⟨C, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
      intro ρ hρ
      exact norm_weilLiTest_natCast_le_inv_norm m (by linarith)
  | negSucc k =>
      let m := k + 1
      let C₀ : ℝ := ∑ j ∈ Finset.Icc 1 m,
        ‖((-1 : ℂ) ^ (j + 1) * Nat.choose m j)‖
      refine ⟨2 * C₀, mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), ?_⟩
      intro ρ hρ
      have hρ0 := ρ.ne_zero
      have hρ1 := ρ.ne_one
      have hreflect : weilLiTest (.negSucc k) (ρ : ℂ) =
          weilLiTest (m : ℤ) (1 - (ρ : ℂ)) := by
        rw [show Int.negSucc k = -(m : ℤ) by simp [m, Int.negSucc_eq]]
        exact weilLiTest_neg (m : ℤ) hρ0 hρ1
      have hnorm : ‖(ρ : ℂ)‖ / 2 ≤ ‖1 - (ρ : ℂ)‖ := by
        have htri := norm_sub_norm_le (ρ : ℂ) 1
        rw [norm_sub_rev, norm_one] at htri
        linarith
      have hone : 1 ≤ ‖1 - (ρ : ℂ)‖ := by linarith
      rw [hreflect]
      refine (norm_weilLiTest_natCast_le_inv_norm m hone).trans ?_
      dsimp [C₀]
      have hpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr ρ.ne_zero
      calc
        (∑ j ∈ Finset.Icc 1 m,
            ‖((-1 : ℂ) ^ (j + 1) * Nat.choose m j)‖) /
              ‖1 - (ρ : ℂ)‖ ≤
            (∑ j ∈ Finset.Icc 1 m,
              ‖((-1 : ℂ) ^ (j + 1) * Nat.choose m j)‖) /
                (‖(ρ : ℂ)‖ / 2) := by
          exact div_le_div_of_nonneg_left
            (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            (div_pos hpos (by norm_num)) hnorm
        _ = (2 * ∑ j ∈ Finset.Icc 1 m,
              ‖((-1 : ℂ) ^ (j + 1) * Nat.choose m j)‖) /
                ‖(ρ : ℂ)‖ := by
          field_simp [ne_of_gt hpos]

/-- One occurrence contribution to the Weil scalar product for two Li test
functions.  Unlike an individual Li zero value, this term will be summed by
an ordinary absolutely convergent `tsum`. -/
def weilLiScalarTerm (n m : ℤ) (a : XiZeroOccurrence) : ℂ :=
  weilLiTest n a.value *
    starRingEnd ℂ (weilLiTest m (weilReflect a.value))

theorem weilLiScalarTerm_eq_mul_neg (n m : ℤ) (a : XiZeroOccurrence) :
    weilLiScalarTerm n m a =
      weilLiTest n a.value * weilLiTest (-m) a.value := by
  rw [weilLiScalarTerm,
    conj_weilLiTest_weilReflect m a.value_ne_zero a.1.ne_one]

/-- Absolute convergence of the Li-test specialization of Lagarias's Weil
scalar product.  Both factors are `O(1 / ‖ρ‖)`, so reciprocal-square
summability of the occurrence-indexed xi divisor applies. -/
theorem summable_weilLiScalarTerm (n m : ℤ) :
    Summable (weilLiScalarTerm n m) := by
  obtain ⟨Cn, hCn, hn⟩ := norm_weilLiTest_le_inv_norm n
  obtain ⟨Cm, hCm, hm⟩ := norm_weilLiTest_le_inv_norm (-m)
  let u : XiZeroOccurrence → ℝ := fun a ↦
    (Cn * Cm) * (1 / ‖a.value‖ ^ 2)
  have hu : Summable u :=
    xiOccurrence_reciprocal_sq_summable.mul_left (Cn * Cm)
  refine Summable.of_norm_bounded_eventually hu ?_
  have htend := xiOccurrence_reciprocal_sq_summable.tendsto_cofinite_zero
  have hevent : ∀ᶠ a : XiZeroOccurrence in Filter.cofinite,
      1 / ‖a.value‖ ^ 2 < (1 / 4 : ℝ) :=
    htend.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hevent] with a ha
  have hapos : 0 < ‖a.value‖ := norm_pos_iff.mpr a.value_ne_zero
  have haNorm : 2 ≤ ‖a.value‖ := by
    by_contra hnot
    have halt : ‖a.value‖ < 2 := lt_of_not_ge hnot
    have hsq : ‖a.value‖ ^ 2 < 4 := by nlinarith [sq_nonneg ‖a.value‖]
    have hinv : (1 / 4 : ℝ) < 1 / ‖a.value‖ ^ 2 :=
      one_div_lt_one_div_of_lt (sq_pos_of_pos hapos) hsq
    exact (not_lt_of_ge hinv.le) ha
  rw [weilLiScalarTerm_eq_mul_neg, norm_mul]
  calc
    ‖weilLiTest n a.value‖ * ‖weilLiTest (-m) a.value‖ ≤
        (Cn / ‖a.value‖) * (Cm / ‖a.value‖) := by
      exact mul_le_mul (hn a.1 haNorm) (hm a.1 haNorm)
        (norm_nonneg _) (div_nonneg hCn hapos.le)
    _ = (Cn * Cm) * (1 / ‖a.value‖ ^ 2) := by
      field_simp [ne_of_gt hapos]
    _ = u a := rfl

/-- Lagarias's Weil scalar product specialized to the integer-indexed Li test
family, with xi zeros counted by multiplicity. -/
noncomputable def weilLiScalar (n m : ℤ) : ℂ :=
  ∑' a : XiZeroOccurrence, weilLiScalarTerm n m a

/-- Any absolutely summable occurrence-indexed zero function is exhausted by
the genuine symmetric height cutoffs. -/
theorem tendsto_heightCutoff_sum_of_summable
    {f : XiZeroOccurrence → ℂ} (hf : Summable f) :
    Tendsto (fun T : ℝ ↦ ∑ a ∈ xiOccurrenceHeightFinset T, f a)
      atTop (nhds (∑' a, f a)) := by
  exact hf.hasSum.comp tendsto_xiOccurrenceHeightFinset_atTop

theorem finiteWeilScalar_eq_occurrence_height_sum
    (T : ℝ) (n m : ℤ) :
    finiteWeilScalar (xiZeroHeightCutoff T)
        (weilLiTest n) (weilLiTest m) =
      ∑ a ∈ xiOccurrenceHeightFinset T, weilLiScalarTerm n m a := by
  rw [finiteWeilScalar]
  rw [xiZeroHeightCutoff_map_sum_eq_sum]
  classical
  rw [xiOccurrenceHeightFinset, Finset.sum_sigma]
  simp [weilLiScalarTerm, XiZeroOccurrence.value, Finset.sum_const,
    nsmul_eq_mul]

/-- The finite Weil scalars in the genuine Lagarias height ordering exhaust
the absolutely convergent infinite Weil scalar. -/
theorem finiteWeilScalar_heightCutoff_tendsto (n m : ℤ) :
    Tendsto
      (fun T : ℝ ↦ finiteWeilScalar (xiZeroHeightCutoff T)
        (weilLiTest n) (weilLiTest m))
      atTop (nhds (weilLiScalar n m)) := by
  have h := tendsto_heightCutoff_sum_of_summable
    (summable_weilLiScalarTerm n m)
  exact h.congr' (Filter.Eventually.of_forall fun T ↦
    (finiteWeilScalar_eq_occurrence_height_sum T n m).symm)

/-- Infinite Lagarias equation (3.3) for the Riemann-xi Li test family. -/
theorem weilLiScalar_eq_classicalLiSigned (n m : ℤ) :
    weilLiScalar n m =
      classicalLiSigned n + classicalLiSigned (-m) -
        classicalLiSigned (n - m) := by
  have hright : Tendsto
      (fun T : ℝ ↦ liStarPartial T n + liStarPartial T (-m) -
        liStarPartial T (n - m)) atTop
      (nhds (classicalLiSigned n + classicalLiSigned (-m) -
        classicalLiSigned (n - m))) :=
    ((liStarConvergesTo_classicalLiSigned n).add
      (liStarConvergesTo_classicalLiSigned (-m))).sub
        (liStarConvergesTo_classicalLiSigned (n - m))
  have hright' : Tendsto
      (fun T : ℝ ↦ finiteWeilScalar (xiZeroHeightCutoff T)
        (weilLiTest n) (weilLiTest m)) atTop
      (nhds (classicalLiSigned n + classicalLiSigned (-m) -
        classicalLiSigned (n - m))) :=
    hright.congr' (Filter.Eventually.of_forall fun T ↦ by
      simpa [liStarPartial] using
        (finiteWeilScalar_liTest (xiZeroHeightCutoff T)
          (xiZeroHeightCutoff_valid T) n m).symm)
  exact tendsto_nhds_unique (finiteWeilScalar_heightCutoff_tendsto n m) hright'

@[simp] theorem star_classicalLiSigned (n : ℤ) :
    starRingEnd ℂ (classicalLiSigned n) = classicalLiSigned n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => simp
      | succ k => simpa [classicalLiSigned] using classicalLiCoefficient_conj k
  | negSucc k => simpa [classicalLiSigned] using classicalLiCoefficient_conj k

/-- Hermitian symmetry of the infinite Li-test Weil scalar. -/
theorem weilLiScalar_conj_symm (n m : ℤ) :
    starRingEnd ℂ (weilLiScalar n m) = weilLiScalar m n := by
  rw [weilLiScalar_eq_classicalLiSigned,
    weilLiScalar_eq_classicalLiSigned]
  simp only [map_sub, map_add, star_classicalLiSigned]
  rw [classicalLiSigned_neg m, classicalLiSigned_neg n]
  have hdiff : m - n = -(n - m) := by ring
  rw [hdiff, classicalLiSigned_neg]
  ring

/-- Diagonal Lagarias equation (3.4), in signed integer indexing. -/
theorem weilLiScalar_self (n : ℤ) :
    weilLiScalar n n = 2 * classicalLiSigned n := by
  rw [weilLiScalar_eq_classicalLiSigned, classicalLiSigned_neg]
  simp only [sub_self, classicalLiSigned_zero]
  ring

/-- Diagonal Lagarias equation (3.4), aligned with RH Garden's zero-based
natural indexing of the classical real Li coefficients. -/
theorem weilLiScalar_self_nat (k : ℕ) :
    weilLiScalar (((k + 1 : ℕ) : ℤ)) (((k + 1 : ℕ) : ℤ)) =
      (2 * classicalLiRealCoefficient k : ℂ) := by
  rw [weilLiScalar_self, classicalLiSigned_ofNat_succ,
    classicalLiCoefficient_eq_real]

/-- The real diagonal Weil value for the `(k+1)`-st Li test function. -/
noncomputable def weilLiQuadraticValue (k : ℕ) : ℝ :=
  (weilLiScalar (((k + 1 : ℕ) : ℤ)) (((k + 1 : ℕ) : ℤ))).re

theorem weilLiQuadraticValue_eq_two_li (k : ℕ) :
    weilLiQuadraticValue k = 2 * classicalLiRealCoefficient k := by
  rw [weilLiQuadraticValue, weilLiScalar_self_nat]
  norm_num

/-- Positivity only on the Li-test diagonal of the Weil form.  This is not
the future full Weil-form positive-semidefiniteness proposition. -/
def WeilLiPositive : Prop :=
  ∀ k : ℕ, 0 ≤ weilLiQuadraticValue k

/-- Positivity of the classical Li sequence is exactly positivity of the
corresponding diagonal Weil values.  This proves an equivalence of two open
propositions, not either proposition itself. -/
theorem liPositive_iff_weilLiPositive :
    LiPositive ↔ WeilLiPositive := by
  constructor
  · intro h k
    unfold LiPositive at h
    rw [weilLiQuadraticValue_eq_two_li]
    exact mul_nonneg (by norm_num) (h k)
  · intro h k
    unfold WeilLiPositive at h
    have hk := h k
    rw [weilLiQuadraticValue_eq_two_li] at hk
    linarith

end RHGarden
