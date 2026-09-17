import RHGarden.SuzukiPrimePowerSurcharge
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite rational divisor-square arithmetic bounds. Inputs are divisibility counts,
not future prime samples. Negative coefficient products are retained exactly. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

def suzukiSieveWeight (D : Finset ℕ) (a : ℕ → ℚ) (n : ℕ) : ℝ :=
  (∑ d ∈ D, if d ∣ n then (a d : ℝ) else 0) ^ 2

theorem suzukiSieveWeight_nonneg (D : Finset ℕ) (a : ℕ → ℚ) (n : ℕ) :
    0 ≤ suzukiSieveWeight D a n := sq_nonneg _

theorem suzukiSieveWeight_prime {D : Finset ℕ} {a : ℕ → ℚ} {z p : ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z) (h1 : 1 ∈ D) (ha : a 1 = 1)
    (hp : p.Prime) (hzp : z < p) : suzukiSieveWeight D a p = 1 := by
  have he : (∑ d ∈ D, if d ∣ p then (a d : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [ha]
    · intro d hd hd1
      have hn : ¬ d ∣ p := by
        intro hdiv
        rcases (Nat.dvd_prime hp).mp hdiv with h | h
        · exact hd1 h
        · have := (hD d hd).2; omega
      simp [hn]
    · exact fun h => (h h1).elim
  simp [suzukiSieveWeight, he]

theorem prime_weight_sum_le_sieve {D : Finset ℕ} {a : ℕ → ℚ} {z m N : ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z) (h1 : 1 ∈ D) (ha : a 1 = 1) (hzm : z ≤ m)
    (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc m N, 0 ≤ w n) :
    (∑ p ∈ (Finset.Ioc m N).filter Nat.Prime, w p) ≤
      ∑ n ∈ Finset.Ioc m N, w n * suzukiSieveWeight D a n := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · rw [if_pos hp, suzukiSieveWeight_prime hD h1 ha hp (lt_of_le_of_lt hzm (Finset.mem_Ioc.mp hn).1), mul_one]
  · rw [if_neg hp]
    exact mul_nonneg (hw n hn) (suzukiSieveWeight_nonneg _ _ _)

theorem suzukiSieveWeight_eq_quadratic (D : Finset ℕ) (a : ℕ → ℚ) (n : ℕ) :
    suzukiSieveWeight D a n =
      ∑ d ∈ D, ∑ e ∈ D, (a d : ℝ) * (a e : ℝ) * (if Nat.lcm d e ∣ n then 1 else 0) := by
  unfold suzukiSieveWeight
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Nat.lcm_dvd_iff]
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he]

/-- Exact weighted lcm matrix, with no sign restriction on a_d*a_e. -/
theorem weighted_sieve_eq_quadratic (D : Finset ℕ) (a : ℕ → ℚ)
    (T : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ T, w n * suzukiSieveWeight D a n) =
      ∑ d ∈ D, ∑ e ∈ D, (a d : ℝ) * (a e : ℝ) *
        ∑ n ∈ T, if Nat.lcm d e ∣ n then w n else 0 := by
  simp_rw [suzukiSieveWeight_eq_quadratic, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

theorem count_multiples_Ioc {m N L : ℕ} (hmN : m ≤ N) :
    ((Finset.Ioc m N).filter (fun n => L ∣ n)).card = N / L - m / L := by
  have h := Nat.Ioc_filter_dvd_card_eq_div N L
  have hm := Nat.Ioc_filter_dvd_card_eq_div m L
  have hs : (Finset.Ioc 0 N).filter (fun n => L ∣ n) =
      ((Finset.Ioc 0 m).filter (fun n => L ∣ n)) ∪
        ((Finset.Ioc m N).filter (fun n => L ∣ n)) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hmN]
  have hd : Disjoint ((Finset.Ioc 0 m).filter (fun n => L ∣ n))
      ((Finset.Ioc m N).filter (fun n => L ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn').1).1
    omega
  rw [hs, Finset.card_union_of_disjoint hd, hm] at h
  omega

theorem unit_sieve_eq_count_quadratic (D : Finset ℕ) (a : ℕ → ℚ)
    {m N : ℕ} (hmN : m ≤ N) :
    (∑ n ∈ Finset.Ioc m N, suzukiSieveWeight D a n) =
      ∑ d ∈ D, ∑ e ∈ D, (a d : ℝ) * (a e : ℝ) *
        ((N / Nat.lcm d e - m / Nat.lcm d e : ℕ) : ℝ) := by
  have h := weighted_sieve_eq_quadratic D a (Finset.Ioc m N) (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, count_multiples_Ioc hmN]

theorem count_multiples_real_Ioc {m L : ℕ} {x : ℝ} (hmx : (m : ℝ) ≤ x) :
    ((Finset.Ioc m ⌊x⌋₊).filter (fun n => L ∣ n)).card = ⌊x / L⌋₊ - m / L := by
  rw [count_multiples_Ioc (Nat.le_floor hmx), Nat.floor_div_natCast]

/-- Concrete rational specialization a_1=1, a_2=-1. -/
def suzukiParitySieveCoeff (d : ℕ) : ℚ := if d = 1 then 1 else -1

theorem suzukiParitySieveWeight (n : ℕ) :
    suzukiSieveWeight {1, 2} suzukiParitySieveCoeff n = if 2 ∣ n then 0 else 1 := by
  simp [suzukiSieveWeight, suzukiParitySieveCoeff]
  split_ifs <;> norm_num

theorem prime_weight_sum_le_odd {m N : ℕ} (hm : 2 ≤ m)
    (w : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc m N, 0 ≤ w n) :
    (∑ p ∈ (Finset.Ioc m N).filter Nat.Prime, w p) ≤
      ∑ n ∈ Finset.Ioc m N, if 2 ∣ n then 0 else w n := by
  have h := prime_weight_sum_le_sieve (D := {1, 2}) (a := suzukiParitySieveCoeff)
    (z := 2) (by intro d hd; simp at hd; rcases hd with rfl | rfl <;> omega)
    (by simp) (by simp [suzukiParitySieveCoeff]) hm w hw
  simpa only [suzukiParitySieveWeight, mul_ite, mul_zero, mul_one] using h

/-- Correct Mangoldt weight at every even integer: a power of two contributes log 2,
and a non-prime-power contributes zero. No local factorization table is an input. -/
theorem vonMangoldt_le_log_two_of_even {n : ℕ} (hn : 2 ∣ n) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply, (Nat.minFac_eq_two_iff n).mpr hn]
  split_ifs
  · rfl
  · exact Real.log_nonneg (by norm_num)

def suzukiParityMangoldtUpper (n : ℕ) : ℝ := if 2 ∣ n then Real.log 2 else Real.log n

theorem vonMangoldt_le_parity (n : ℕ) :
    ArithmeticFunction.vonMangoldt n ≤ suzukiParityMangoldtUpper n := by
  unfold suzukiParityMangoldtUpper
  split_ifs with hn
  · exact vonMangoldt_le_log_two_of_even hn
  · exact ArithmeticFunction.vonMangoldt_le_log

theorem weightedMangoldt_le_parity {T : Finset ℕ} (w : ℕ → ℝ)
    (hw : ∀ n ∈ T, 0 ≤ w n) :
    (∑ n ∈ T, ArithmeticFunction.vonMangoldt n * w n) ≤
      ∑ n ∈ T, suzukiParityMangoldtUpper n * w n :=
  Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (vonMangoldt_le_parity n) (hw n hn))

theorem parity_le_all_integer {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n)
    (w : ℕ → ℝ) (hw : ∀ n ∈ T, 0 ≤ w n) :
    (∑ n ∈ T, suzukiParityMangoldtUpper n * w n) ≤
      ∑ n ∈ T, Real.log n * w n := by
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (hw n hn)
  unfold suzukiParityMangoldtUpper
  split_ifs
  · exact Real.log_le_log (by norm_num) (by exact_mod_cast hT n hn)
  · rfl

/-- All integer bases, not just primes: the extra composite-base representations
are deliberate overcount. Nat.log gives the exact integer exponent cutoff. -/
def suzukiAllBasePowerBound (m N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), ∑ a ∈ Finset.Icc 2 N,
    if a ^ k ∈ Finset.Ioc m N then Real.log a * w (a ^ k) else 0

theorem vonMangoldt_le_prime_add_allBases {q N : ℕ} (hq : q ≤ N) :
    ArithmeticFunction.vonMangoldt q ≤ (if q.Prime then Real.log q else 0) +
      ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), ∑ a ∈ Finset.Icc 2 N,
        if a ^ k = q then Real.log a else 0 := by
  have hnon (k : ℕ) : 0 ≤ ∑ a ∈ Finset.Icc 2 N,
      if a ^ k = q then Real.log a else 0 := by
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ a by have := (Finset.mem_Icc.mp ha).1; omega))
    · rfl
  by_cases hp : q.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hnon k))
  rw [if_neg hp, zero_add]
  by_cases he : IsPrimePow q
  · obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff q).mp he
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hk1 : k = 1 := by omega
      simp [hk1] at hp
      exact hp hp'
    have hkK : k ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hp'.two_le k).trans hq)
    have hpN : p ≤ N := (Nat.le_self_pow (by omega) p).trans hq
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp']
    calc
      _ ≤ ∑ a ∈ Finset.Icc 2 N, if a ^ k = p ^ k then Real.log a else 0 := by
        have h := Finset.single_le_sum (s := Finset.Icc 2 N)
          (f := fun a => if a ^ k = p ^ k then Real.log a else 0)
          (by intro a ha; split_ifs; exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ a by have := (Finset.mem_Icc.mp ha).1; omega)); rfl)
          (Finset.mem_Icc.mpr ⟨hp'.two_le, hpN⟩)
        simpa using h
      _ ≤ _ := Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_Icc.mpr ⟨hk2, hkK⟩)
  · rw [ArithmeticFunction.vonMangoldt_apply, if_neg he]
    exact Finset.sum_nonneg (fun k _ => hnon k)

theorem weightedMangoldt_le_prime_add_allBasePowers {m N : ℕ}
    (w : ℕ → ℝ) (hw : ∀ q ∈ Finset.Ioc m N, 0 ≤ w q) :
    (∑ q ∈ Finset.Ioc m N, ArithmeticFunction.vonMangoldt q * w q) ≤
      (∑ p ∈ (Finset.Ioc m N).filter Nat.Prime, Real.log p * w p) +
      suzukiAllBasePowerBound m N w := by
  have he : (∑ q ∈ Finset.Ioc m N, (∑ k ∈ Finset.Icc 2 (Nat.log 2 N),
      ∑ a ∈ Finset.Icc 2 N, if a ^ k = q then Real.log a else 0) * w q) =
      suzukiAllBasePowerBound m N w := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    unfold suzukiAllBasePowerBound
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hmem : a ^ k ∈ Finset.Ioc m N
    · rw [if_pos hmem, Finset.sum_eq_single (a ^ k)]
      · simp
      · intro q hq hn; simp [Ne.symm hn]
      · exact fun h => (h hmem).elim
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro q hq
      have hn : a ^ k ≠ q := by intro h; exact hmem (h ▸ hq)
      simp [hn]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc m N, ((if q.Prime then Real.log q else 0) +
        ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), ∑ a ∈ Finset.Icc 2 N,
          if a ^ k = q then Real.log a else 0) * w q := by
      exact Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right
        (vonMangoldt_le_prime_add_allBases (Finset.mem_Ioc.mp hq).2) (hw q hq))
    _ = _ := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, he, Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp

/-- Effective, sample-independent, correctly weighted sieve bound. Its only arithmetic
inputs are the rational divisor coefficients and exact divisibility tests. -/
theorem weightedMangoldt_le_sieve_add_allBasePowers {D : Finset ℕ} {a : ℕ → ℚ}
    {z m N : ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z) (h1 : 1 ∈ D)
    (ha : a 1 = 1) (hzm : z ≤ m) (w : ℕ → ℝ)
    (hw : ∀ q ∈ Finset.Ioc m N, 0 ≤ w q) :
    (∑ q ∈ Finset.Ioc m N, ArithmeticFunction.vonMangoldt q * w q) ≤
      (∑ n ∈ Finset.Ioc m N, Real.log n * w n * suzukiSieveWeight D a n) +
      suzukiAllBasePowerBound m N w := by
  apply (weightedMangoldt_le_prime_add_allBasePowers w hw).trans
  apply add_le_add _ le_rfl
  apply prime_weight_sum_le_sieve hD h1 ha hzm
  intro n hn
  apply mul_nonneg _ (hw n hn)
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Ioc.mp hn).1; omega))

end RHGarden
