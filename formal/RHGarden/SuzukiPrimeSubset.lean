import RHGarden.SuzukiArithmeticSieve
import RHGarden.SuzukiSmallArithmetic
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Kernel-checkable LOWER certificates from a subset of prime arrivals. These finite
reference data are never inputs to a sample-independent arithmetic upper bound. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

def logRatioLower (a b : ℚ) : ℚ :=
  let z := (b - a) / (b + a)
  2 * (z + z ^ 3 / 3)

theorem logRatioLower_nonneg {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ logRatioLower a b := by
  unfold logRatioLower
  have : 0 ≤ (b - a) / (b + a) := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  positivity

theorem logRatioLower_le_log {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) :
    (logRatioLower a b : ℝ) ≤ Real.log ((b : ℝ) / a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  let z : ℝ := (b - a) / (b + a)
  have hz : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz1 : z < 1 := (div_lt_one (by linarith : (0 : ℝ) < b + a)).mpr (by linarith)
  have hh := Real.sum_range_le_log_div hz hz1 2
  have he : (1 + z) / (1 - z) = (b : ℝ) / a := by
    have hz0 : 1 - z ≠ 0 := (sub_pos.mpr hz1).ne'
    field_simp [hz0, haR.ne']
    dsimp [z]
    field_simp [(show (b : ℝ) + a ≠ 0 by linarith)]
    ring
  rw [he] at hh
  norm_num [Finset.sum_range_succ] at hh
  have hh2 : 2 * (z + z ^ 3 / 3) ≤ Real.log ((b : ℝ) / a) := by linarith
  simpa [logRatioLower, z] using hh2

structure SuzukiPrimeLowerRow where
  prime : ℕ
  sqrtUpperNumerator : ℕ
  weightLowerNumerator : ℕ
  deriving DecidableEq

def SuzukiPrimeLowerRow.Valid (m x : ℕ) (L : ℚ) (r : SuzukiPrimeLowerRow) : Prop :=
  r.prime.Prime ∧ m < r.prime ∧ r.prime ≤ x ∧ 0 < r.sqrtUpperNumerator ∧
    (r.prime : ℚ) ≤ ((r.sqrtUpperNumerator : ℚ) / 1000000000) ^ 2 ∧
    (r.weightLowerNumerator : ℚ) / 1000000000000 ≤
      (L + logRatioLower m r.prime) / (r.sqrtUpperNumerator / 1000000000) * logRatioLower r.prime x

instance (m x : ℕ) (L : ℚ) (r : SuzukiPrimeLowerRow) : Decidable (r.Valid m x L) := by
  unfold SuzukiPrimeLowerRow.Valid
  infer_instance

theorem SuzukiPrimeLowerRow.lower {m x : ℕ} {L : ℚ} {r : SuzukiPrimeLowerRow}
    (hm : 1 ≤ m) (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log m) (hr : r.Valid m x L) :
    (r.weightLowerNumerator : ℝ) / 1000000000000 ≤
      ArithmeticFunction.vonMangoldt r.prime / Real.sqrt r.prime * Real.log ((x : ℝ) / r.prime) := by
  obtain ⟨hp, hmp, hpx, hs0, hsq, hw⟩ := hr
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hmpQ : (m : ℚ) ≤ r.prime := by exact_mod_cast hmp.le
  have hpQ : (0 : ℚ) < r.prime := by exact_mod_cast hp.pos
  have hpxQ : (r.prime : ℚ) ≤ x := by exact_mod_cast hpx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR : (0 : ℝ) < r.prime := by exact_mod_cast hp.pos
  have hsR : (0 : ℝ) < (r.sqrtUpperNumerator : ℝ) / 1000000000 := by positivity
  have hsqR : (r.prime : ℝ) ≤ ((r.sqrtUpperNumerator : ℝ) / 1000000000) ^ 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hsq
    simpa using hh
  have hs : Real.sqrt r.prime ≤ (r.sqrtUpperNumerator : ℝ) / 1000000000 := by
    nlinarith [Real.sq_sqrt hpR.le, Real.sqrt_nonneg (r.prime : ℝ)]
  have ha := logRatioLower_le_log hmQ hmpQ
  have hb := logRatioLower_le_log hpQ hpxQ
  push_cast at ha hb
  have ha0 : (0 : ℝ) ≤ L + (logRatioLower m r.prime : ℝ) := by
    exact_mod_cast add_nonneg hL0 (logRatioLower_nonneg hmQ hmpQ)
  have hb0 : (0 : ℝ) ≤ (logRatioLower r.prime x : ℝ) := by
    exact_mod_cast logRatioLower_nonneg hpQ hpxQ
  have hlog : (L : ℝ) + (logRatioLower m r.prime : ℝ) ≤ Real.log r.prime := by
    rw [Real.log_div hpR.ne' hmR.ne'] at ha
    linarith
  have hwR : (r.weightLowerNumerator : ℝ) / 1000000000000 ≤
      ((L : ℝ) + (logRatioLower m r.prime : ℝ)) /
        ((r.sqrtUpperNumerator : ℝ) / 1000000000) * (logRatioLower r.prime x : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hw
    simpa using hh
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  apply hwR.trans
  apply mul_le_mul _ hb hb0 (div_nonneg (ha0.trans hlog) (Real.sqrt_nonneg _))
  exact (div_le_div_of_nonneg_right hlog hsR.le).trans
    (div_le_div_of_nonneg_left (ha0.trans hlog) (Real.sqrt_pos.mpr hpR) hs)

theorem primeSubset_logArrival_lower {m x : ℕ} {L : ℚ} (rs : List SuzukiPrimeLowerRow)
    (hm : 1 ≤ m) (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log m)
    (hvalid : ∀ r ∈ rs, r.Valid m x L) (hchain : (rs.map SuzukiPrimeLowerRow.prime).IsChain (· < ·)) :
    (((rs.map SuzukiPrimeLowerRow.weightLowerNumerator).sum : ℕ) : ℝ) / 1000000000000 ≤
      ∑ q ∈ Finset.Ioc m x, ArithmeticFunction.vonMangoldt q / Real.sqrt q * Real.log ((x : ℝ) / q) := by
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
    exact Finset.mem_Ioc.mpr ⟨(hvalid r hr).2.1, (hvalid r hr).2.2.1⟩
  · intro q hq _
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := (Finset.mem_Ioc.mp hq).1; omega)
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.log_nonneg ((one_le_div hq0).mpr (by exact_mod_cast (Finset.mem_Ioc.mp hq).2)))

end RHGarden
