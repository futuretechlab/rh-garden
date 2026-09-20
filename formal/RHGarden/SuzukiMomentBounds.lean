import RHGarden.SuzukiGreedyMoment
import RHGarden.SuzukiFiniteSieve
import RHGarden.SuzukiRecoveryMarginBounds
import RHGarden.SuzukiFinitePrefix37

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.
Actual arithmetic instantiations of finite moment relaxation bounds.
The only unfixed arithmetic scalar used by the candidates is terminal S_q.
No uniform reserve floor, smaller zero-free strip, or RH proof is supplied.
-/
noncomputable section
open scoped BigOperators
namespace RHGarden
open CumulativeMoment

def suzukiMomentWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem momentWeight_nonneg (n : ℕ) : 0 ≤ suzukiMomentWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem momentWeight_mass {q : ℕ} (_hq : 1 ≤ q) :
    mass suzukiMomentWeight q = suzukiMangoldtSlope q := by
  unfold mass suzukiMangoldtSlope suzukiMomentWeight
  apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
  intro n hn hn'
  have hn1 : n = 1 := by simp only [Finset.mem_Icc] at hn hn'; omega
  simp [hn1]

theorem momentWeight_moment {q : ℕ} (_hq : 1 ≤ q) :
    moment suzukiMomentWeight q = suzukiMangoldtIntercept q := by
  have hsum : (∑ n ∈ Finset.Icc 2 q, ArithmeticFunction.vonMangoldt n * Real.log n / Real.sqrt n) =
      suzukiMangoldtIntercept q := by
    unfold suzukiMangoldtIntercept
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
    intro n hn hn'
    have hn1 : n = 1 := by simp only [Finset.mem_Icc] at hn hn'; omega
    simp [hn1]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp [suzukiMomentWeight]
  ring

theorem pinnedPrefix_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ suzukiPinnedPrefixUpper n :=
  (suzukiMangoldtSlope_nonneg n).trans (mangoldtSlope_le_pinnedPrefix hn)

theorem pinnedPrefix_mono : MonotoneOn suzukiPinnedPrefixUpper (Set.Ici 1) := by
  intro m hm n hn hmn
  have hm1 : 1 ≤ m := hm
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hl : Real.log m ≤ Real.log n := Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
    (by exact_mod_cast hmn)
  have hs := Real.sqrt_le_sqrt (show (m : ℝ) ≤ n by exact_mod_cast hmn)
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.log 4 by positivity)
  have hsq : Real.log m ^ 2 ≤ Real.log n ^ 2 := by nlinarith
  dsimp [suzukiPinnedPrefixUpper]
  linarith

def suzukiCumulativeMomentLower (q : ℕ) : ℝ :=
  lower suzukiPinnedPrefixUpper (suzukiMangoldtSlope q) q

/-- Exact finite layer identity for actual correctly weighted arrivals. -/
theorem mangoldtIntercept_eq_layer {q : ℕ} (hq : 2 ≤ q) :
    suzukiMangoldtIntercept q = layer (suzukiMangoldtSlope q) suzukiMangoldtSlope q := by
  rw [← momentWeight_moment (by omega : 1 ≤ q), moment_eq_layer _ hq,
    momentWeight_mass (by omega : 1 ≤ q)]
  unfold layer
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [momentWeight_mass (by have := (Finset.mem_Ico.mp hn).1; omega)]

theorem mangoldtIntercept_sub_cumulativeLower {q : ℕ} (hq : 2 ≤ q) :
    suzukiMangoldtIntercept q - suzukiCumulativeMomentLower q =
      ∑ n ∈ Finset.Ico 2 q,
        (min (suzukiMangoldtSlope q) (suzukiPinnedPrefixUpper n) - suzukiMangoldtSlope n) * stepLog n := by
  have h := moment_sub_lower suzukiMomentWeight suzukiPinnedPrefixUpper hq
  rw [momentWeight_moment (by omega : 1 ≤ q), momentWeight_mass (by omega : 1 ≤ q)] at h
  rw [suzukiCumulativeMomentLower, h]
  apply Finset.sum_congr rfl
  intro n hn
  rw [momentWeight_mass (by have := (Finset.mem_Ico.mp hn).1; omega)]

theorem cumulativeMomentLower_le_intercept {q : ℕ} (hq : 2 ≤ q) :
    suzukiCumulativeMomentLower q ≤ suzukiMangoldtIntercept q := by
  have h := lower_le_moment (a := suzukiMomentWeight) (U := suzukiPinnedPrefixUpper) hq (fun n _ => momentWeight_nonneg n)
    (fun n hn => by
      rw [momentWeight_mass (by have := (Finset.mem_Ico.mp hn).1; omega)]
      exact mangoldtSlope_le_pinnedPrefix (by have := (Finset.mem_Ico.mp hn).1; omega))
  simpa [momentWeight_mass (by omega : 1 ≤ q), momentWeight_moment (by omega : 1 ≤ q),
    suzukiCumulativeMomentLower] using h

/-- Attainment for the P-only REAL-WEIGHT relaxation at the actual scalar S_q.
The attaining artificial weights are not claimed to be Mangoldt weights. -/
theorem pinned_moment_relaxation_attained {q : ℕ} (hq : 2 ≤ q) :
    ∃ a : ℕ → ℝ, (∀ n ∈ Finset.Icc 2 q, 0 ≤ a n) ∧
      (∀ n ∈ Finset.Icc 2 q, mass a n ≤ suzukiPinnedPrefixUpper n) ∧
      mass a q = suzukiMangoldtSlope q ∧ moment a q = suzukiCumulativeMomentLower q :=
  prefix_cap_attainment hq (suzukiMangoldtSlope_nonneg q)
    (fun n hn => pinnedPrefix_nonneg (by omega))
    (pinnedPrefix_mono.mono (by intro n hn; exact show 1 ≤ n by have : 2 ≤ n := hn; omega))
    (mangoldtSlope_le_pinnedPrefix (by omega))

def suzukiParityMomentCap (n : ℕ) : ℝ := suzukiParityMangoldtUpper n / Real.sqrt n
def suzukiParityCumulativeMomentLower (q : ℕ) : ℝ :=
  layer (suzukiMangoldtSlope q)
    (greedy suzukiPinnedPrefixUpper suzukiParityMomentCap (suzukiMangoldtSlope q)) q

theorem momentWeight_le_parityCap (n : ℕ) : suzukiMomentWeight n ≤ suzukiParityMomentCap n :=
  div_le_div_of_nonneg_right (vonMangoldt_le_parity n) (Real.sqrt_nonneg _)

theorem parityMomentCap_nonneg (n : ℕ) : 0 ≤ suzukiParityMomentCap n :=
  (momentWeight_nonneg n).trans (momentWeight_le_parityCap n)

theorem parityCumulativeMomentLower_le_intercept {q : ℕ} (hq : 2 ≤ q) :
    suzukiParityCumulativeMomentLower q ≤ suzukiMangoldtIntercept q := by
  have h := greedy_layer_le_moment (a := suzukiMomentWeight) (U := suzukiPinnedPrefixUpper) hq
    (fun n _ => momentWeight_nonneg n)
    (fun n hn => by
      rw [momentWeight_mass (by have := (Finset.mem_Icc.mp hn).1; omega)]
      exact mangoldtSlope_le_pinnedPrefix (by have := (Finset.mem_Icc.mp hn).1; omega))
    (fun n _ => momentWeight_le_parityCap n)
  simpa [momentWeight_mass (by omega : 1 ≤ q), momentWeight_moment (by omega : 1 ≤ q),
    suzukiParityCumulativeMomentLower] using h

theorem cumulativeLower_le_parityCumulativeLower (q : ℕ) :
    suzukiCumulativeMomentLower q ≤ suzukiParityCumulativeMomentLower q :=
  lower_le_greedy_layer (suzukiMangoldtSlope_nonneg q) q

theorem parity_moment_relaxation_attained {q : ℕ} (hq : 2 ≤ q) :
    ∃ g : ℕ → ℝ, (∀ n ∈ Finset.Icc 2 q, 0 ≤ g n ∧ g n ≤ suzukiParityMomentCap n) ∧
      (∀ n ∈ Finset.Icc 2 q, mass g n ≤ suzukiPinnedPrefixUpper n) ∧
      mass g q = suzukiMangoldtSlope q ∧ moment g q = suzukiParityCumulativeMomentLower q := by
  apply greedy_attainment (a := suzukiMomentWeight) hq (suzukiMangoldtSlope_nonneg q)
    (fun n hn => pinnedPrefix_nonneg (by omega)) (fun n _ => parityMomentCap_nonneg n)
    (pinnedPrefix_mono.mono (by intro n hn; exact show 1 ≤ n by have : 2 ≤ n := hn; omega))
    (fun n _ => momentWeight_nonneg n)
  · intro n hn
    rw [momentWeight_mass (by have := (Finset.mem_Icc.mp hn).1; omega)]
    exact mangoldtSlope_le_pinnedPrefix (by have := (Finset.mem_Icc.mp hn).1; omega)
  · exact fun n _ => momentWeight_le_parityCap n
  · exact momentWeight_mass (by omega)

theorem globalDualMargin_ge_cumulative {q : ℕ} (hq : 2 ≤ q) :
    suzukiCumulativeMomentLower q - suzukiArchDual (suzukiMangoldtSlope q) ≤
      suzukiGlobalDualMargin q := sub_le_sub_right (cumulativeMomentLower_le_intercept hq) _

theorem globalDualMargin_ge_parityCumulative {q : ℕ} (hq : 2 ≤ q) :
    suzukiParityCumulativeMomentLower q - suzukiArchDual (suzukiMangoldtSlope q) ≤
      suzukiGlobalDualMargin q := sub_le_sub_right (parityCumulativeMomentLower_le_intercept hq) _

/-- The P-only bound improves log(2)*S_q by at least 4/5 for every q>=31.
This is a moment improvement, NOT a positive or uniform reserve bound. -/
theorem cumulativeMoment_improves_of_thirtyOne_le {q : ℕ} (hq : 31 ≤ q) :
    suzukiMangoldtSlope q * Real.log 2 + (4 / 5 : ℝ) ≤ suzukiCumulativeMomentLower q := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have hP : suzukiPinnedPrefixUpper 2 ≤ 6 := by
    dsimp [suzukiPinnedPrefixUpper]
    rw [hlog4]
    nlinarith [mul_le_mul hl hsqrt (Real.sqrt_nonneg 2) (by norm_num : (0 : ℝ) ≤ 7 / 10)]
  have hS : 8 ≤ suzukiMangoldtSlope q := by
    have hm := suzukiMangoldtSlope_monotone hq
    linarith [small_state_31.1.1]
  have hstep : (2 / 5 : ℝ) ≤ stepLog 2 := by
    rw [stepLog_eq_sub (by norm_num : 1 ≤ (2 : ℕ))]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  have hterm : (4 / 5 : ℝ) ≤ max (suzukiMangoldtSlope q - suzukiPinnedPrefixUpper 2) 0 * stepLog 2 := by
    have hx : 2 ≤ max (suzukiMangoldtSlope q - suzukiPinnedPrefixUpper 2) 0 :=
      le_trans (by linarith) (le_max_left _ _)
    nlinarith [mul_le_mul hx hstep (by norm_num : (0 : ℝ) ≤ 2 / 5) (le_max_right (suzukiMangoldtSlope q - suzukiPinnedPrefixUpper 2) 0)]
  have hsum := Finset.single_le_sum (s := Finset.Ico 2 q)
    (f := fun n => max (suzukiMangoldtSlope q - suzukiPinnedPrefixUpper n) 0 * stepLog n)
    (fun n hn => mul_nonneg (le_max_right _ _) (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega)).le)
    (by simp only [Finset.mem_Ico]; omega : 2 ∈ Finset.Ico 2 q)
  exact add_le_add le_rfl (hterm.trans hsum)

theorem cumulativeMoment_thirtyOne_improves :
    suzukiMangoldtSlope 31 * Real.log 2 + (4 / 5 : ℝ) ≤ suzukiCumulativeMomentLower 31 :=
  cumulativeMoment_improves_of_thirtyOne_le le_rfl

/-- The proper-prime-power state used by the retained m=31 recovery. -/
theorem cumulativeMoment_thirtyTwo_improves :
    suzukiMangoldtSlope 32 * Real.log 2 + (4 / 5 : ℝ) ≤ suzukiCumulativeMomentLower 32 :=
  cumulativeMoment_improves_of_thirtyOne_le (by norm_num)

theorem cumulativeMoment_thirtyOne_proved_bound :
    suzukiMangoldtSlope 31 * Real.log 2 + (4 / 5 : ℝ) ≤ suzukiMangoldtIntercept 31 :=
  cumulativeMoment_thirtyOne_improves.trans (cumulativeMomentLower_le_intercept (by norm_num))

end RHGarden
