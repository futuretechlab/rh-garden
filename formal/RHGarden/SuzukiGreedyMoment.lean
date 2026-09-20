import RHGarden.SuzukiCumulativeMoment

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.
Prefix-cap PLUS pointwise-cap relaxation. The greedy sequence uses only U, c,
and the scalar total mass s, never unknown intermediate arithmetic samples.
-/
noncomputable section
open scoped BigOperators
namespace RHGarden.CumulativeMoment

def greedy (U c : ℕ → ℝ) (s : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if n = 0 then 0 else
      min (min s (U (n + 1))) (greedy U c s n + c (n + 1))

@[simp] theorem greedy_one (U c : ℕ → ℝ) (s : ℝ) : greedy U c s 1 = 0 := by
  simp [greedy]

theorem greedy_succ (U c : ℕ → ℝ) (s : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    greedy U c s (n + 1) = min (min s (U (n + 1))) (greedy U c s n + c (n + 1)) := by
  simp [greedy, show n ≠ 0 by omega]

theorem greedy_le_total {U c : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    greedy U c s n ≤ s := by
  rcases n with _ | n
  · exact hs
  by_cases hn : n = 0
  · subst n; simpa using hs
  · rw [greedy_succ U c s (by omega)]
    exact (min_le_left _ _).trans (min_le_left _ _)

theorem greedy_le_cap (U c : ℕ → ℝ) (s : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    greedy U c s n ≤ U n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [greedy_succ U c s (by omega)]
  exact (min_le_left _ _).trans (min_le_right _ _)

theorem greedy_nonneg {U c : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hU : ∀ n, 2 ≤ n → 0 ≤ U n) (hc : ∀ n, 2 ≤ n → 0 ≤ c n) (n : ℕ) :
    0 ≤ greedy U c s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [greedy_succ U c s (by omega)]
      exact le_min (le_min hs (hU _ (by omega))) (add_nonneg ih (hc _ (by omega)))

theorem greedy_mono {U c : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hU : ∀ n, 2 ≤ n → 0 ≤ U n) (hc : ∀ n, 2 ≤ n → 0 ≤ c n)
    (hmono : MonotoneOn U (Set.Ici 2)) : Monotone (greedy U c s) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n = 0
  · subst n; simp [greedy]
  rw [greedy_succ U c s (by omega)]
  refine le_min (le_min (greedy_le_total hs n) ?_) (le_add_of_nonneg_right (hc _ (by omega)))
  by_cases hn1 : n = 1
  · subst n; simpa using hU 2 (by norm_num)
  · exact (greedy_le_cap U c s (by omega : 2 ≤ n)).trans
      (hmono (by simpa using (show 2 ≤ n by omega))
        (by simpa using (show 2 ≤ n + 1 by omega)) (Nat.le_succ n))

theorem greedy_increment_le (U c : ℕ → ℝ) (s : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    increments (greedy U c s) n ≤ c n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  dsimp [increments]
  rw [greedy_succ U c s (by omega)]
  have := min_le_right (min s (U (k + 1))) (greedy U c s k + c (k + 1))
  linarith

/-- Every feasible prefix is dominated; monotonicity of U is not even
needed for this direction. All future information is expressed by the caps. -/
theorem mass_le_greedy {a U c : ℕ → ℝ} {s : ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hcap : ∀ n ∈ Finset.Icc 2 q, mass a n ≤ U n)
    (htotal : ∀ n ∈ Finset.Icc 2 q, mass a n ≤ s)
    (hpoint : ∀ n ∈ Finset.Icc 2 q, a n ≤ c n) :
    mass a q ≤ greedy U c s q := by
  induction q, hq using Nat.le_induction with
  | base => simp [mass]
  | succ q hq ih =>
    have hmem : q + 1 ∈ Finset.Icc 2 (q + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    have hsub : Finset.Icc 2 q ⊆ Finset.Icc 2 (q + 1) := Finset.Icc_subset_Icc le_rfl (Nat.le_succ q)
    rw [greedy_succ U c s hq]
    refine le_min (le_min (htotal _ hmem) (hcap _ hmem)) ?_
    rw [mass_succ a hq]
    exact add_le_add (ih (fun n hn => hcap n (hsub hn))
      (fun n hn => htotal n (hsub hn)) (fun n hn => hpoint n (hsub hn))) (hpoint _ hmem)

theorem greedy_terminal_eq {a U c : ℕ → ℝ} {s : ℝ} {q : ℕ} (hq : 2 ≤ q)
    (hs : 0 ≤ s) (ha : ∀ n ∈ Finset.Icc 2 q, 0 ≤ a n)
    (hcap : ∀ n ∈ Finset.Icc 2 q, mass a n ≤ U n)
    (hpoint : ∀ n ∈ Finset.Icc 2 q, a n ≤ c n) (htotal : mass a q = s) :
    greedy U c s q = s := by
  apply le_antisymm (greedy_le_total hs q)
  rw [← htotal]
  exact mass_le_greedy (by omega) hcap
    (fun n hn => mass_mono ha (Finset.mem_Icc.mp hn).2) hpoint

/-- A sound lower moment bound using both classes of arithmetic inequalities. -/
theorem greedy_layer_le_moment {a U c : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q)
    (ha : ∀ n ∈ Finset.Icc 2 q, 0 ≤ a n)
    (hcap : ∀ n ∈ Finset.Icc 2 q, mass a n ≤ U n)
    (hpoint : ∀ n ∈ Finset.Icc 2 q, a n ≤ c n) :
    layer (mass a q) (greedy U c (mass a q)) q ≤ moment a q := by
  rw [moment_eq_layer a hq]
  unfold layer
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro n hn
  have hsub : Finset.Icc 2 n ⊆ Finset.Icc 2 q :=
    Finset.Icc_subset_Icc le_rfl (Finset.mem_Ico.mp hn).2.le
  have hh := mass_le_greedy (by have := (Finset.mem_Ico.mp hn).1; omega : 1 ≤ n)
    (fun i hi => hcap i (hsub hi))
    (fun i hi => mass_mono ha (Finset.mem_Icc.mp (hsub hi)).2)
    (fun i hi => hpoint i (hsub hi))
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hh _)
    (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega)).le

theorem lower_le_greedy_layer {U c : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (q : ℕ) :
    lower U s q ≤ layer s (greedy U c s) q := by
  unfold lower layer
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (stepLog_pos (by have := (Finset.mem_Ico.mp hn).1; omega)).le
  exact max_le (sub_le_sub_left (greedy_le_cap U c s (Finset.mem_Ico.mp hn).1) _)
    (sub_nonneg.mpr (greedy_le_total hs n))

/-- Exact extra information contributed by pointwise caps. -/
theorem greedy_layer_sub_lower (U c : ℕ → ℝ) (s : ℝ) (q : ℕ) :
    layer s (greedy U c s) q - lower U s q =
      ∑ n ∈ Finset.Ico 2 q, (min s (U n) - greedy U c s n) * stepLog n := by
  simp only [layer, lower, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : s ≤ U n
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem greedy_increments_supported {U c : ℕ → ℝ} {s : ℝ} {q : ℕ}
    (hs : 0 ≤ s) (hmono : Monotone (greedy U c s)) (hq : greedy U c s q = s)
    {n : ℕ} (hn : n ∉ Finset.Icc 2 q) : increments (greedy U c s) n = 0 := by
  by_cases hn2 : n < 2
  · have hh : n = 0 ∨ n = 1 := by omega
    rcases hh with rfl | rfl <;> simp [increments, greedy]
  · have hqn : q < n := by simp only [Finset.mem_Icc] at hn; omega
    have heq (k : ℕ) (hk : q ≤ k) : greedy U c s k = s :=
      le_antisymm (greedy_le_total hs k) (by simpa only [hq] using hmono hk)
    rw [increments, heq n hqn.le, heq (n - 1) (by omega), sub_self]

/-- If any feasible sequence has total s, greedy increments are feasible,
attain total s, and attain the lower moment. This is a real-weight optimum,
not an optimum among Mangoldt sequences. -/
theorem greedy_attainment {a U c : ℕ → ℝ} {s : ℝ} {q : ℕ} (hq : 2 ≤ q)
    (hs : 0 ≤ s) (hU : ∀ n, 2 ≤ n → 0 ≤ U n)
    (hc : ∀ n, 2 ≤ n → 0 ≤ c n) (hmono : MonotoneOn U (Set.Ici 2))
    (ha : ∀ n ∈ Finset.Icc 2 q, 0 ≤ a n)
    (hcap : ∀ n ∈ Finset.Icc 2 q, mass a n ≤ U n)
    (hpoint : ∀ n ∈ Finset.Icc 2 q, a n ≤ c n) (htotal : mass a q = s) :
    ∃ g : ℕ → ℝ, (∀ n ∈ Finset.Icc 2 q, 0 ≤ g n ∧ g n ≤ c n) ∧
      (∀ n ∈ Finset.Icc 2 q, mass g n ≤ U n) ∧ mass g q = s ∧
      moment g q = layer s (greedy U c s) q := by
  let C := greedy U c s
  have hC1 : C 1 = 0 := greedy_one _ _ _
  have hmass (n : ℕ) (hn : 1 ≤ n) : mass (increments C) n = C n := mass_increments hC1 hn
  have hCq : C q = s := greedy_terminal_eq hq hs ha hcap hpoint htotal
  refine ⟨increments C, ?_, ?_, (hmass q (by omega)).trans hCq, ?_⟩
  · intro n hn
    exact ⟨sub_nonneg.mpr (greedy_mono hs hU hc hmono (Nat.sub_le n 1)),
      greedy_increment_le U c s (Finset.mem_Icc.mp hn).1⟩
  · intro n hn
    rw [hmass n (by have := (Finset.mem_Icc.mp hn).1; omega)]
    exact greedy_le_cap U c s (Finset.mem_Icc.mp hn).1
  · rw [moment_eq_layer _ hq, hmass q (by omega), hCq]
    unfold layer
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hmass n (by have := (Finset.mem_Ico.mp hn).1; omega)]

end RHGarden.CumulativeMoment
