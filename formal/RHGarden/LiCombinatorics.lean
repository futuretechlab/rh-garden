import RHGarden.LiClassical

noncomputable section

namespace RHGarden

open PowerSeries

theorem coeff_liMobiusSeries_pow (n k : ℕ) :
    coeff (n + 1) (liMobiusSeries ^ k) =
      if k = 0 then 0 else (n.choose (k - 1) : ℂ) := by
  cases k with
  | zero => simp
  | succ d =>
      simp only [if_false, Nat.succ_ne_zero, Nat.add_sub_cancel]
      rw [liMobiusSeries, mul_pow, PowerSeries.mk_one_pow_eq_mk_choose_add]
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs with h
      · rw [PowerSeries.coeff_mk]
        have heq : d + (n + 1 - (d + 1)) = n := by omega
        rw [heq]
      · norm_cast
        exact (Nat.choose_eq_zero_of_lt (by omega)).symm

theorem coeff_one_add_X_pow (n k : ℕ) :
    coeff k ((1 + X) ^ n : PowerSeries ℂ) = (n.choose k : ℂ) := by
  have h : ((1 + X) ^ n : PowerSeries ℂ) =
      ((((1 : Polynomial ℂ) + Polynomial.X) ^ n).toPowerSeries) := by
    simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem coeff_subst_liMobius_eq_coeff_one_add_pow_mul
    (H : PowerSeries ℂ)
    (hH0 : constantCoeff H = 0)
    (n : ℕ) :
    coeff (n + 1) (H.subst liMobiusSeries) =
      coeff (n + 1) ((1 + X) ^ n * H) := by
  rw [PowerSeries.coeff_subst' liMobiusSeries_hasSubst]
  simp_rw [coeff_liMobiusSeries_pow]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 2)) (by
    intro k hk
    simp only [Function.mem_support] at hk
    by_contra hkrange
    have hklarge : n + 2 ≤ k := by simpa using hkrange
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero,
      smul_zero] at hk
    exact hk rfl)]
  rw [PowerSeries.coeff_mul]
  change _ = ∑ p ∈ Finset.antidiagonal (n + 1),
    (fun i j ↦ coeff i ((1 + X) ^ n : PowerSeries ℂ) * coeff j H) p.1 p.2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_range_reflect
    (fun j ↦ coeff j ((1 + X) ^ n : PowerSeries ℂ) *
      coeff (n + 1 - j) H) (n + 2)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n + 1 := by
    have := Finset.mem_range.mp hj
    omega
  by_cases hj0 : j = 0
  · subst j
    simp [hH0]
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hsub : n + 1 - (n + 2 - 1 - j) = j := by omega
    have hchooseArg : n + 2 - 1 - j = n - (j - 1) := by omega
    rw [hsub, coeff_one_add_X_pow, hchooseArg,
      Nat.choose_symm (by omega)]
    simp [hj0, mul_comm]

/-- The coefficient functional obtained by differentiating the formally
substituted generating logarithm. -/
def liGeneratingFunctional (H : PowerSeries ℂ) (n : ℕ) : ℂ :=
  coeff n (PowerSeries.derivative ℂ (H.subst liMobiusSeries))

/-- The coefficient functional corresponding to Li's shifted original
derivative expression. -/
def liOriginalFunctional (H : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) * coeff (n + 1) ((1 + X) ^ n * H)

theorem liGeneratingFunctional_eq_liOriginalFunctional
    (H : PowerSeries ℂ) (hH0 : constantCoeff H = 0) (n : ℕ) :
    liGeneratingFunctional H n = liOriginalFunctional H n := by
  rw [liGeneratingFunctional, liOriginalFunctional,
    PowerSeries.coeff_derivative,
    coeff_subst_liMobius_eq_coeff_one_add_pow_mul H hH0 n]
  ring

end RHGarden
