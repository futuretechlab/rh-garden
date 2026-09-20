import RHGarden.SuzukiPinnedEventBound
import Mathlib.Algebra.BigOperators.Intervals

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite logarithmic-moment optimization over arbitrary nonnegative REAL weights.
This relaxation is not a model of primes, nor an arithmetic impossibility result.
-/
noncomputable section
open scoped BigOperators
namespace RHGarden.CumulativeMoment

def mass (a : ℕ → ℝ) (q : ℕ) : ℝ := ∑ n ∈ Finset.Icc 2 q, a n
def moment (a : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 q, a n * Real.log n
def stepLog (n : ℕ) : ℝ := Real.log (((n : ℝ) + 1) / n)
def layer (s : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ :=
  s * Real.log 2 + ∑ n ∈ Finset.Ico 2 q, (s - C n) * stepLog n
def lower (U : ℕ → ℝ) (s : ℝ) (q : ℕ) : ℝ :=
  s * Real.log 2 + ∑ n ∈ Finset.Ico 2 q, max (s - U n) 0 * stepLog n

theorem stepLog_eq_sub {n : ℕ} (hn : 1 ≤ n) :
    stepLog n = Real.log (n + 1 : ℕ) - Real.log n := by
  rw [stepLog, Real.log_div (by positivity) (by exact_mod_cast (show n ≠ 0 by omega))]
  push_cast
  rfl

theorem stepLog_pos {n : ℕ} (hn : 1 ≤ n) : 0 < stepLog n := by
  rw [stepLog_eq_sub hn]
  exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast (show 0 < n by omega))
    (by exact_mod_cast Nat.lt_succ_self n))

theorem sum_stepLog {q : ℕ} (hq : 2 ≤ q) :
    (∑ n ∈ Finset.Ico 2 q, stepLog n) = Real.log q - Real.log 2 := by
  calc
    _ = ∑ n ∈ Finset.Ico 2 q, (Real.log (n + 1 : ℕ) - Real.log n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact stepLog_eq_sub (by have := (Finset.mem_Ico.mp hn).1; omega)
    _ = _ := Finset.sum_Ico_sub (fun n : ℕ => Real.log n) hq

theorem mass_succ (a : ℕ → ℝ) {q : ℕ} (hq : 1 ≤ q) :
    mass a (q + 1) = mass a q + a (q + 1) := by
  unfold mass
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ q + 1)]

/-- Finite Abel identity; no sign assumption is needed for the equality. -/
theorem moment_abel (a : ℕ → ℝ) {q : ℕ} (hq : 2 ≤ q) :
    moment a q = mass a q * Real.log q -
      ∑ n ∈ Finset.Ico 2 q, mass a n * stepLog n := by
  induction q, hq using Nat.le_induction with
  | base => simp [moment, mass]
  | succ q hq ih =>
    rw [moment, Finset.sum_Icc_succ_top (by omega)]
    change moment a q + a (q + 1) * Real.log (q + 1 : ℕ) = _
    rw [ih, mass_succ a (by omega), Finset.sum_Ico_succ_top hq, stepLog_eq_sub (by omega)]
    ring

theorem moment_eq_layer (a : ℕ → ℝ) {q : ℕ} (hq : 2 ≤ q) :
    moment a q = layer (mass a q) (mass a) q := by
  rw [moment_abel a hq]
  simp only [layer, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_stepLog hq]
  ring

theorem mass_mono {a : ℕ → ℝ} {q : ℕ}
    (ha : ∀ n ∈ Finset.Icc 2 q, 0 ≤ a n) {n : ℕ} (hn : n ≤ q) :
    mass a n ≤ mass a q := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hn
  · intro i hi _
    exact ha i hi

/-- Exact gap, even before nonnegativity of its summands is established. -/
theorem moment_sub_lower (a U : ℕ → ℝ) {q : ℕ} (hq : 2 ≤ q) :
    moment a q - lower U (mass a q) q =
      ∑ n ∈ Finset.Ico 2 q, (min (mass a q) (U n) - mass a n) * stepLog n := by
  rw [moment_eq_layer a hq]
  simp only [layer, lower, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : mass a q ≤ U n
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem lower_le_moment {a U : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q)
    (ha : ∀ n ∈ Finset.Icc 2 q, 0 ≤ a n)
    (hU : ∀ n ∈ Finset.Ico 2 q, mass a n ≤ U n) :
    lower U (mass a q) q ≤ moment a q := by
  apply sub_nonneg.mp
  rw [moment_sub_lower a U hq]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (sub_nonneg.mpr (le_min (mass_mono ha (Finset.mem_Ico.mp hn).2.le)
    (hU n hn))) (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega)).le

theorem baseline_le_lower (U : ℕ → ℝ) (s : ℝ) (q : ℕ) :
    s * Real.log 2 ≤ lower U s q := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun n hn => mul_nonneg (le_max_right _ _)
    (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega)).le)

theorem baseline_lt_lower {U : ℕ → ℝ} {s : ℝ} {q n : ℕ}
    (hn : n ∈ Finset.Ico 2 q) (hUs : U n < s) : s * Real.log 2 < lower U s q := by
  apply lt_add_of_pos_right
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (le_max_right _ _) (stepLog_pos (by have := (Finset.mem_Ico.mp hk).1; omega)).le
  · exact ⟨n, hn, mul_pos (lt_max_of_lt_left (sub_pos.mpr hUs))
      (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega))⟩

def cappedPrefix (U : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  if n < 2 then 0 else min s (U n)
def increments (C : ℕ → ℝ) (n : ℕ) : ℝ := C n - C (n - 1)

theorem mass_increments {C : ℕ → ℝ} (hC : C 1 = 0) {q : ℕ} (hq : 1 ≤ q) :
    mass (increments C) q = C q := by
  induction q, hq using Nat.le_induction with
  | base => simp [mass, hC]
  | succ q hq ih => rw [mass_succ _ hq, ih]; simp [increments]

theorem cappedPrefix_mono {U : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hU : ∀ n, 2 ≤ n → 0 ≤ U n) (hmono : MonotoneOn U (Set.Ici 2)) :
    Monotone (cappedPrefix U s) := by
  intro i j hij
  unfold cappedPrefix
  split_ifs with hi hj hj
  · rfl
  · exact le_min hs (hU j (by omega))
  · omega
  · exact min_le_min le_rfl (hmono (by simpa using (show 2 ≤ i by omega))
      (by simpa using (show 2 ≤ j by omega)) hij)

/-- Attainment ONLY in the relaxation of arbitrary nonnegative real weights
with cumulative caps. No prime or active-block structure is asserted. -/
theorem prefix_cap_attainment {U : ℕ → ℝ} {s : ℝ} {q : ℕ} (hq : 2 ≤ q)
    (hs : 0 ≤ s) (hU : ∀ n, 2 ≤ n → 0 ≤ U n)
    (hmono : MonotoneOn U (Set.Ici 2)) (hsq : s ≤ U q) :
    ∃ a : ℕ → ℝ, (∀ n ∈ Finset.Icc 2 q, 0 ≤ a n) ∧
      (∀ n ∈ Finset.Icc 2 q, mass a n ≤ U n) ∧ mass a q = s ∧
      moment a q = lower U s q := by
  let C := cappedPrefix U s
  have hC1 : C 1 = 0 := by simp [C, cappedPrefix]
  have hmass (n : ℕ) (hn : 1 ≤ n) : mass (increments C) n = C n := mass_increments hC1 hn
  have hCq : C q = s := by simp [C, cappedPrefix, show ¬ q < 2 by omega, min_eq_left hsq]
  refine ⟨increments C, ?_, ?_, (hmass q (by omega)).trans hCq, ?_⟩
  · intro n hn
    exact sub_nonneg.mpr (cappedPrefix_mono hs hU hmono (Nat.sub_le n 1))
  · intro n hn
    rw [hmass n (by have := (Finset.mem_Icc.mp hn).1; omega)]
    simp only [C, cappedPrefix, if_neg (by have := (Finset.mem_Icc.mp hn).1; omega : ¬ n < 2)]
    exact min_le_right _ _
  · rw [moment_eq_layer _ hq, hmass q (by omega), hCq]
    unfold layer lower
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hmass n (by have := (Finset.mem_Ico.mp hn).1; omega)]
    simp only [C, cappedPrefix, if_neg (by have := (Finset.mem_Ico.mp hn).1; omega : ¬ n < 2)]
    by_cases hnU : s ≤ U n
    · rw [min_eq_left hnU, max_eq_right (by linarith), sub_self]
    · rw [min_eq_right (le_of_not_ge hnU), max_eq_left (by linarith)]

theorem capped_increments_supported {U : ℕ → ℝ} {s : ℝ} {q : ℕ} (hq : 2 ≤ q)
    (hmono : MonotoneOn U (Set.Ici 2)) (hsq : s ≤ U q) {n : ℕ}
    (hn : n ∉ Finset.Icc 2 q) : increments (cappedPrefix U s) n = 0 := by
  by_cases hn2 : n < 2
  · have hh : n = 0 ∨ n = 1 := by omega
    rcases hh with rfl | rfl <;> simp [increments, cappedPrefix]
  · have hqn : q < n := by simp only [Finset.mem_Icc] at hn; omega
    have hcap (k : ℕ) (hk : q ≤ k) : cappedPrefix U s k = s := by
      have hsU := hsq.trans (hmono (by simpa using hq)
        (by simpa using (hq.trans hk)) hk)
      simp [cappedPrefix, show ¬ k < 2 by omega, min_eq_left hsU]
    rw [increments, hcap n hqn.le, hcap (n - 1) (by omega), sub_self]

/-- Altering a FIXED initial set of caps changes the relaxed moment by
this exact constant once s dominates those caps. No asymptotic premise. -/
theorem lower_sub_lower_fixed_prefix {U W : ℕ → ℝ} {s : ℝ} {N q : ℕ}
    (hN : 2 ≤ N) (hNq : N ≤ q)
    (htail : ∀ n ∈ Finset.Ico N q, W n = U n)
    (hlarge : ∀ n ∈ Finset.Ico 2 N, U n ≤ s ∧ W n ≤ s) :
    lower W s q - lower U s q =
      ∑ n ∈ Finset.Ico 2 N, (U n - W n) * stepLog n := by
  simp only [lower, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_Ico_consecutive _ hN hNq]
  have hzero : (∑ n ∈ Finset.Ico N q,
      (max (s - W n) 0 * stepLog n - max (s - U n) 0 * stepLog n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [htail n hn, sub_self]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  rw [max_eq_left (sub_nonneg.mpr (hlarge n hn).2),
    max_eq_left (sub_nonneg.mpr (hlarge n hn).1)]
  ring

end RHGarden.CumulativeMoment
