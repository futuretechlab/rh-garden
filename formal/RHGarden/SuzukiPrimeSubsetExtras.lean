import RHGarden.SuzukiPrimeSubset

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Adding separately verified, nonprime arrivals to a prime-subset lower bound. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

theorem primeSubset_primeLogArrival_lower {m x : ℕ} {L : ℚ} (rs : List SuzukiPrimeLowerRow)
    (hm : 1 ≤ m) (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log m)
    (hvalid : ∀ r ∈ rs, r.Valid m x L)
    (hchain : (rs.map SuzukiPrimeLowerRow.prime).IsChain (· < ·)) :
    (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 ≤
      ∑ q ∈ (Finset.Ioc m x).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q) := by
  let f := fun q : ℕ => ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q)
  have hd : (rs.map SuzukiPrimeLowerRow.prime).Nodup :=
    (List.isChain_iff_pairwise.mp hchain).imp (fun h => ne_of_lt h)
  have hl := List.sum_le_sum (fun r hr => SuzukiPrimeLowerRow.lower hm hL0 hL (hvalid r hr))
  have he : (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 =
      (rs.map (fun r => (r.weightLowerNumerator : ℝ) / 1000000000000)).sum := by
    clear hvalid hchain hd hl
    induction rs with
    | nil => simp
    | cons r rs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div, ih]
  rw [he]
  apply hl.trans
  have hs := List.sum_toFinset f hd
  rw [List.map_map] at hs
  dsimp [f, Function.comp_def] at hs
  rw [← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(hvalid r hr).2.1, (hvalid r hr).2.2.1⟩, (hvalid r hr).1⟩
  · intro q hq _
    have hqq := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.log_nonneg ((one_le_div hq0).mpr (by exact_mod_cast hqq.2)))

theorem primeSubset_logArrival_lower_with_extras {m x : ℕ} {L : ℚ}
    (rs : List SuzukiPrimeLowerRow) (extra : Finset ℕ)
    (hm : 1 ≤ m) (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log m)
    (hvalid : ∀ r ∈ rs, r.Valid m x L)
    (hchain : (rs.map SuzukiPrimeLowerRow.prime).IsChain (· < ·))
    (he : extra ⊆ Finset.Ioc m x) (hnp : ∀ q ∈ extra, ¬ q.Prime) :
    (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 +
      ∑ q ∈ extra, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q) ≤
      ∑ q ∈ Finset.Ioc m x, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q) := by
  let f := fun q : ℕ => ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q)
  let P := (rs.map SuzukiPrimeLowerRow.prime).toFinset
  have hd : (rs.map SuzukiPrimeLowerRow.prime).Nodup :=
    (List.isChain_iff_pairwise.mp hchain).imp (fun h => ne_of_lt h)
  have hlow : (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 ≤
      ∑ q ∈ P, f q := by
    have hl := List.sum_le_sum (fun r hr => SuzukiPrimeLowerRow.lower hm hL0 hL (hvalid r hr))
    have hs := List.sum_toFinset f hd
    rw [List.map_map] at hs
    dsimp [Function.comp_def] at hs
    change _ ≤ ∑ q ∈ (rs.map SuzukiPrimeLowerRow.prime).toFinset, f q
    rw [hs]
    have heq : (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 =
        (rs.map (fun r => (r.weightLowerNumerator : ℝ) / 1000000000000)).sum := by
      clear hvalid hchain hd hl hs P
      induction rs with
      | nil => simp
      | cons r rs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div, ih]
    rw [heq]
    exact hl
  have hP (q : ℕ) (hq : q ∈ P) : q ∈ Finset.Ioc m x ∧ q.Prime := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact ⟨Finset.mem_Ioc.mpr ⟨(hvalid r hr).2.1, (hvalid r hr).2.2.1⟩, (hvalid r hr).1⟩
  have hdis : Disjoint P extra := Finset.disjoint_left.mpr (fun q hp hq => hnp q hq (hP q hp).2)
  have hsum : (∑ q ∈ P, f q) + ∑ q ∈ extra, f q ≤ ∑ q ∈ Finset.Ioc m x, f q := by
    rw [← Finset.sum_union hdis]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rcases Finset.mem_union.mp hq with hp | hq
      · exact (hP q hp).1
      · exact he hq
    · intro q hq _
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := (Finset.mem_Ioc.mp hq).1; omega)
      exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (Real.log_nonneg ((one_le_div hq0).mpr (by exact_mod_cast (Finset.mem_Ioc.mp hq).2)))
  exact (add_le_add hlow le_rfl).trans hsum

theorem onePercent_square571_lower :
    (44 / 100000 : ℝ) ≤ ArithmeticFunction.vonMangoldt 326041 / Real.sqrt 326041 *
      Real.log (339360 / 326041) := by
  have hp : Nat.Prime 571 := by norm_num
  have hl : (63 / 10 : ℝ) ≤ Real.log 571 := by
    have h := logRatioLower_le_log (by norm_num : (0 : ℚ) < 512) (by norm_num : (512 : ℚ) ≤ 571)
    have h2 := Real.log_two_gt_d9
    norm_num [logRatioLower] at h
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    have he : Real.log (512 : ℝ) = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
    rw [he] at h
    linarith
  have hr := logRatioLower_le_log (by norm_num : (0 : ℚ) < 326041)
    (by norm_num : (326041 : ℚ) ≤ 339360)
  norm_num [logRatioLower] at hr
  rw [show 326041 = 571 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  norm_num
  have hs : Real.sqrt (326041 : ℝ) = 571 := by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  rw [hs]
  have hlog0 : 0 ≤ Real.log (339360 / 326041 : ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right (show ((63 / 10) / 571 : ℝ) ≤ Real.log 571 / 571 by linarith) hlog0
  nlinarith

theorem onePercent_square577_lower :
    (20 / 100000 : ℝ) ≤ ArithmeticFunction.vonMangoldt 332929 / Real.sqrt 332929 *
      Real.log (339360 / 332929) := by
  have hp : Nat.Prime 577 := by norm_num
  have hl : (63 / 10 : ℝ) ≤ Real.log 577 := by
    have h := logRatioLower_le_log (by norm_num : (0 : ℚ) < 512) (by norm_num : (512 : ℚ) ≤ 577)
    have h2 := Real.log_two_gt_d9
    norm_num [logRatioLower] at h
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    have he : Real.log (512 : ℝ) = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
    rw [he] at h
    linarith
  have hr := logRatioLower_le_log (by norm_num : (0 : ℚ) < 332929)
    (by norm_num : (332929 : ℚ) ≤ 339360)
  norm_num [logRatioLower] at hr
  rw [show 332929 = 577 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  norm_num
  have hs : Real.sqrt (332929 : ℝ) = 577 := by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  rw [hs]
  have hlog0 : 0 ≤ Real.log (339360 / 332929 : ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right (show ((63 / 10) / 577 : ℝ) ≤ Real.log 577 / 577 by linarith) hlog0
  nlinarith

end RHGarden
