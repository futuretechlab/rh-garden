import RHGarden.SuzukiPrimePowerSurcharge
import Mathlib.Analysis.PSeries

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Summability ingredients for the higher-power part of the surcharge.
The PNT/partial-summation limit itself is not asserted in this module. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

/-- The exponent tail starting at exponent three. For a prime p, take
r = 1/sqrt(p); the summand times log(p) is gamma(p^(n+3)). -/
theorem higherPower_geometric_mass {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) * r ^ (n + 3)) ∧
    (∑' n : ℕ, ((n : ℝ) + 2) * r ^ (n + 3)) ≤ 32 * r ^ 3 := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_right (r ^ 3)
  have h2 := (hasSum_geometric_of_norm_lt_one hn).mul_left (2 * r ^ 3)
  have he : HasSum (fun n : ℕ => ((n : ℝ) + 2) * r ^ (n + 3))
      (r / (1 - r) ^ 2 * r ^ 3 + 2 * r ^ 3 * (1 - r)⁻¹) := by
    have hf : (fun n : ℕ => ((n : ℝ) + 2) * r ^ (n + 3)) =
        (fun n : ℕ => (n : ℝ) * r ^ n * r ^ 3 + 2 * r ^ 3 * r ^ n) := by
      funext n
      rw [pow_add]
      ring
    rw [hf]
    exact h1.add h2
  refine ⟨he.summable, ?_⟩
  rw [he.tsum_eq]
  have hd : 0 < 1 - r := by linarith
  have hb : (2 - r) / (1 - r)^2 ≤ 32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [sq_nonneg (r - 3 / 4)]
  calc
    _ = r ^ 3 * ((2 - r) / (1 - r)^2) := by field_simp; ring
    _ ≤ r ^ 3 * 32 := mul_le_mul_of_nonneg_left hb (pow_nonneg hr0 _)
    _ = _ := by ring

/-- An elementary summable majorant for the total higher-prime-power mass.
It is summed over all naturals, so restricting it to primes is harmless. -/
theorem summable_log_div_threeHalves :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (5 / 4 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hp.mul_left 4)
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hl := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 4 by norm_num)
  calc
    Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤
        ((n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) / (n : ℝ) ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_right hl (Real.rpow_nonneg hn0.le _)
    _ = 4 * (1 / (n : ℝ) ^ (5 / 4 : ℝ)) := by
      have he : (n : ℝ) ^ (3 / 2 : ℝ) =
          (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hn0]
        norm_num
      rw [he]
      field_simp

theorem primePowerOvercharge_eq_geometric {p : ℕ} (hp : p.Prime) (n : ℕ) :
    suzukiPrimePowerOvercharge (p ^ (n + 3)) =
      Real.log p * (((n : ℝ) + 2) * (Real.sqrt p)⁻¹ ^ (n + 3)) := by
  have hs (k : ℕ) : Real.sqrt ((p : ℝ) ^ k) = (Real.sqrt p) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) k), ih, pow_succ]
  rw [suzukiPrimePowerOvercharge_prime_pow hp (by omega), Nat.cast_pow, hs]
  push_cast
  rw [inv_pow]
  ring

theorem summable_higher_primePower_overcharge {p : ℕ} (hp : p.Prime) :
    Summable (fun n : ℕ => suzukiPrimePowerOvercharge (p ^ (n + 3))) ∧
    (∑' n : ℕ, suzukiPrimePowerOvercharge (p ^ (n + 3))) ≤
      32 * Real.log p * (Real.sqrt p)⁻¹ ^ 3 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hs : (Real.sqrt (p : ℝ))⁻¹ ≤ (3 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hs0).mpr
    nlinarith [Real.sq_sqrt hp0.le]
  obtain ⟨hsum, hbound⟩ := higherPower_geometric_mass (inv_nonneg.mpr hs0.le) hs
  have he : (fun n : ℕ => suzukiPrimePowerOvercharge (p ^ (n + 3))) =
      (fun n : ℕ => Real.log p * (((n : ℝ) + 2) * (Real.sqrt p)⁻¹ ^ (n + 3))) := by
    funext n
    exact primePowerOvercharge_eq_geometric hp n
  rw [he]
  refine ⟨hsum.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hb := mul_le_mul_of_nonneg_left hbound (Real.log_natCast_nonneg p)
  nlinarith

end RHGarden
