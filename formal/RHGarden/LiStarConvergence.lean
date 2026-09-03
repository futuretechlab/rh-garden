/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) 2026 Future Technologies Laboratory LLC.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

The integer-window summability argument is adapted from
anthropics/formal-math, zeta23/Zeta23/WeilEF/ZeroSummability.lean,
commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
-/

import RHGarden.ZetaMultiplicity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Complex Filter Set

namespace RHGarden

/-- A distinct xi zero. Multiplicity is carried separately by `xiMultiplicity`. -/
abbrev XiZero := {ρ : ℂ // ρ ∈ xiDivisor.support}

namespace XiZero

theorem xi_eq_zero (ρ : XiZero) : riemannXi (ρ : ℂ) = 0 :=
  (xiDivisor_ne_zero_iff (ρ : ℂ)).mp ρ.property

theorem re_mem_Ioo (ρ : XiZero) : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
  riemannXi_zero_re_mem_Ioo ρ.xi_eq_zero

theorem ne_zero (ρ : XiZero) : (ρ : ℂ) ≠ 0 := by
  intro h
  simpa [h] using ρ.re_mem_Ioo.1

theorem ne_one (ρ : XiZero) : (ρ : ℂ) ≠ 1 := by
  intro h
  simpa [h] using ρ.re_mem_Ioo.2

end XiZero

private lemma liWeight_le (n : ℤ) (hn : n ≠ 0) :
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤
      4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  have h1 := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ |(n : ℝ)| + 3 by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) ≤
      (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) =
      2 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hn0.le,
      show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num)]
        norm_num]
  have hA : Real.log (|(n : ℝ)| + 3) ≤
      4 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    have : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) / (1 / 2) =
        2 * (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1
    rw [h3] at h2
    linarith
  have hB : 1 / (1 + (n : ℝ) ^ 2) ≤ |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs, one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) =
        Real.log (|(n : ℝ)| + 3) * (1 / (1 + (n : ℝ) ^ 2)) := by ring
    _ ≤ (4 * |(n : ℝ)| ^ (1 / 2 : ℝ)) * |(n : ℝ)| ^ (-2 : ℝ) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hn0]
      norm_num

private lemma summable_liWeight :
    Summable (fun n : ℤ ↦
      Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact liWeight_le n hn

private lemma summable_threeHalvesWindowWeight :
    Summable (fun n : ℤ ↦
      Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) := by
  have harg : Tendsto (fun n : ℤ ↦ |(n : ℝ)| + 3) cofinite atTop := by
    have hnorm : Tendsto (fun n : ℤ ↦ ‖(n : ℝ)‖) cofinite atTop :=
      tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite
    simpa only [Real.norm_eq_abs] using
      tendsto_atTop_add_const_right cofinite 3 hnorm
  have hlog : ∀ᶠ n : ℤ in cofinite,
      ‖Real.log (|(n : ℝ)| + 3)‖ ≤ ‖(|(n : ℝ)| + 3) ^ (1 / 4 : ℝ)‖ :=
    harg.eventually ((isLittleO_log_rpow_atTop
      (show (0 : ℝ) < 1 / 4 by norm_num)).eventuallyLE)
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1 : ℝ) < 5 / 4 by norm_num)).mul_left
      ((4 : ℝ) ^ (1 / 4 : ℝ))) ?_
  filter_upwards [hlog, eventually_cofinite_ne 0] with n hnlog hn0
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn0
  have hnpos : (0 : ℝ) < |(n : ℝ)| := lt_of_lt_of_le zero_lt_one hn1
  have hlog' : Real.log (|(n : ℝ)| + 3) ≤
      (|(n : ℝ)| + 3) ^ (1 / 4 : ℝ) := by
    have hlognon : 0 ≤ Real.log (|(n : ℝ)| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])
    have hrpownon : 0 ≤ (|(n : ℝ)| + 3) ^ (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by linarith [abs_nonneg (n : ℝ)]) _
    rw [Real.norm_eq_abs, abs_of_nonneg hlognon,
      Real.norm_eq_abs, abs_of_nonneg hrpownon] at hnlog
    exact hnlog
  have hquarter : (|(n : ℝ)| + 3) ^ (1 / 4 : ℝ) ≤
      (4 * |(n : ℝ)|) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc
    ‖Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))‖ =
        Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)]))
            (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ (|(n : ℝ)| + 3) ^ (1 / 4 : ℝ) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog' (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ (4 * |(n : ℝ)|) ^ (1 / 4 : ℝ) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hquarter (Real.rpow_nonneg (abs_nonneg _) _)
    _ = (4 : ℝ) ^ (1 / 4 : ℝ) * |(n : ℝ)| ^ (-(5 / 4 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hnpos.le, mul_assoc,
        ← Real.rpow_add hnpos]
      norm_num

private def threeHalvesWindowTotalWeight : ℝ :=
  ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))

private def liTotalWeight : ℝ :=
  ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)

private def heightKey (y : ℝ) : ℤ := ⌈y⌉ - 1

private lemma heightKey_lt (y : ℝ) : (heightKey y : ℝ) < y := by
  have := Int.ceil_lt_add_one y
  unfold heightKey
  push_cast
  linarith

private lemma le_heightKey_add_one (y : ℝ) : y ≤ (heightKey y : ℝ) + 1 := by
  have := Int.le_ceil y
  unfold heightKey
  push_cast
  linarith

private lemma xi_heightKey_fiber_multiplicity_le (s : Finset XiZero) (n : ℤ) :
    ∑ ρ ∈ s.filter (fun ρ : XiZero ↦ heightKey (ρ : ℂ).im = n),
        xiMultiplicity (ρ : ℂ) ≤
      xiHeightWindowMultiplicityCount (n : ℝ) ((n : ℝ) + 1) := by
  let fiber := s.filter (fun ρ : XiZero ↦ heightKey (ρ : ℂ).im = n)
  let values : Finset ℂ := fiber.image (fun ρ : XiZero ↦ ρ.1)
  have hvalues : values ⊆
      xiZeroHeightWindowSupportFinset (n : ℝ) ((n : ℝ) + 1) := by
    intro z hz
    simp only [values] at hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    simp only [fiber, Finset.mem_filter] at hρ
    rw [mem_xiZeroHeightWindowSupportFinset_iff]
    refine ⟨ρ.property, ?_, ?_⟩
    · rw [← hρ.2]
      exact heightKey_lt _
    · rw [← hρ.2]
      exact le_heightKey_add_one _
  rw [xiHeightWindowMultiplicityCount_eq_sum]
  rw [show ∑ ρ ∈ s.filter (fun ρ : XiZero ↦ heightKey (ρ : ℂ).im = n),
      xiMultiplicity ρ.1 =
      ∑ z ∈ values, xiMultiplicity z by
    simp only [values, fiber]
    rw [Finset.sum_image]
    exact fun _ _ _ _ h ↦ Subtype.val_injective h]
  exact Finset.sum_le_sum_of_subset_of_nonneg hvalues (fun _ _ _ ↦ Nat.zero_le _)

private lemma half_abs_heightKey_le_norm (ρ : XiZero)
    (hkey : (2 : ℝ) ≤ |(heightKey (ρ : ℂ).im : ℝ)|) :
    |(heightKey (ρ : ℂ).im : ℝ)| / 2 ≤ ‖(ρ : ℂ)‖ := by
  let n := heightKey (ρ : ℂ).im
  have h1 : (n : ℝ) < (ρ : ℂ).im := heightKey_lt _
  have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := le_heightKey_add_one _
  have him : |(n : ℝ)| / 2 ≤ |(ρ : ℂ).im| := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · have hy : 0 ≤ (ρ : ℂ).im := by linarith
      rw [abs_of_nonneg hn, abs_of_nonneg hy]
      linarith
    · have hnle : (n : ℝ) ≤ -2 := by
        have hk := hkey
        change (2 : ℝ) ≤ |(n : ℝ)| at hk
        rw [abs_of_neg hn] at hk
        linarith
      have hy : (ρ : ℂ).im < 0 := by linarith
      rw [abs_of_neg hn, abs_of_neg hy]
      linarith
  exact him.trans (Complex.abs_im_le_norm (ρ : ℂ))

private lemma one_add_height_sq_ge {y : ℝ} {n : ℤ}
    (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2)
        (by linarith : (0 : ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]

private theorem xi_inv_one_add_normSq_summable
    (hCount : XiLocalZeroCountBound) :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ))) := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := hCount
  refine summable_of_sum_le (c := 4 * A₀ * liTotalWeight)
    (fun ρ ↦ div_nonneg (Nat.cast_nonneg _)
      (by linarith [Complex.normSq_nonneg (ρ : ℂ)])) fun s ↦ ?_
  set κ : XiZero → ℤ := fun ρ ↦ heightKey (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
    (fun ρ hρ ↦ Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n,
          (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ)) ≤
        4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwinNat : ∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n), xiMultiplicity (ρ : ℂ) ≤
        xiHeightWindowMultiplicityCount (n : ℝ) ((n : ℝ) + 1) := by
      simpa only [hκ] using xi_heightKey_fiber_multiplicity_le s n
    have hwin : ∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n),
          (xiMultiplicity (ρ : ℂ) : ℝ) ≤
        A₀ * Real.log (|(n : ℝ)| + 3) := by
      have hc : ((∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n),
          xiMultiplicity ρ.1 : ℕ) : ℝ) ≤
          (xiHeightWindowMultiplicityCount (n : ℝ) ((n : ℝ) + 1) : ℝ) := by
        exact_mod_cast hwinNat
      simpa only [Nat.cast_sum] using hc.trans (hloc (n : ℝ))
    have hpt : ∀ ρ ∈ s.filter (fun ρ ↦ κ ρ = n),
        (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ)) ≤
          (4 / (1 + (n : ℝ) ^ 2)) * (xiMultiplicity (ρ : ℂ) : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by
        rw [← hρ.2]
        exact heightKey_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by
        rw [← hρ.2]
        exact le_heightKey_add_one _
      have hge := one_add_height_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (ρ : ℂ) := by
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (ρ : ℂ).re]
      have hm : (0 : ℝ) ≤ xiMultiplicity (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (ρ : ℂ) := by
        linarith [Complex.normSq_nonneg (ρ : ℂ)]
      have hinv : 1 / (1 + Complex.normSq (ρ : ℂ)) ≤
          4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]
        nlinarith [hge, hnorm]
      calc
        (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ)) =
            (xiMultiplicity (ρ : ℂ) : ℝ) *
              (1 / (1 + Complex.normSq (ρ : ℂ))) := by ring
        _ ≤ (xiMultiplicity (ρ : ℂ) : ℝ) *
              (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) *
              (xiMultiplicity (ρ : ℂ) : ℝ) := by ring
    calc
      ∑ ρ ∈ s with κ ρ = n,
          (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ)) ≤
          ∑ ρ ∈ s with κ ρ = n,
            (4 / (1 + (n : ℝ) ^ 2)) * (xiMultiplicity (ρ : ℂ) : ℝ) :=
        Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) *
          ∑ ρ ∈ s with κ ρ = n, (xiMultiplicity (ρ : ℂ) : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) *
          (A₀ * Real.log (|(n : ℝ)| + 3)) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ *
          (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc
    ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n,
        (xiMultiplicity (ρ : ℂ) : ℝ) / (1 + Complex.normSq (ρ : ℂ)) ≤
        ∑ n ∈ s.image κ,
          4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ,
        Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * liTotalWeight := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      exact summable_liWeight.sum_le_tsum _ fun n _ ↦
        div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)

private theorem xi_heightKey_reciprocal_three_halves_summable
    (hCount : XiLocalZeroCountBound) :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℝ) *
        |(heightKey (ρ : ℂ).im : ℝ)| ^ (-(3 / 2 : ℝ))) := by
  classical
  let κ : XiZero → ℤ := fun ρ ↦ heightKey (ρ : ℂ).im
  change Summable (fun ρ : XiZero ↦
    (xiMultiplicity (ρ : ℂ) : ℝ) * |(κ ρ : ℝ)| ^ (-(3 / 2 : ℝ)))
  obtain ⟨A₀, hA₀, hloc⟩ := hCount
  refine summable_of_sum_le (c := A₀ * threeHalvesWindowTotalWeight)
    (fun ρ ↦ mul_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (abs_nonneg _) _)) fun s ↦ ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
    (fun ρ hρ ↦ Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n,
          (xiMultiplicity (ρ : ℂ) : ℝ) * |(κ ρ : ℝ)| ^ (-(3 / 2 : ℝ)) ≤
        A₀ * (Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) := by
    intro n _
    have hwinNat : ∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n), xiMultiplicity (ρ : ℂ) ≤
        xiHeightWindowMultiplicityCount (n : ℝ) ((n : ℝ) + 1) := by
      simpa only [κ] using xi_heightKey_fiber_multiplicity_le s n
    have hwin : ∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n),
          (xiMultiplicity (ρ : ℂ) : ℝ) ≤
        A₀ * Real.log (|(n : ℝ)| + 3) := by
      have hc : ((∑ ρ ∈ s.filter (fun ρ ↦ κ ρ = n),
          xiMultiplicity ρ.1 : ℕ) : ℝ) ≤
          (xiHeightWindowMultiplicityCount (n : ℝ) ((n : ℝ) + 1) : ℝ) := by
        exact_mod_cast hwinNat
      simpa only [Nat.cast_sum] using hc.trans (hloc (n : ℝ))
    calc
      ∑ ρ ∈ s with κ ρ = n,
          (xiMultiplicity (ρ : ℂ) : ℝ) * |(κ ρ : ℝ)| ^ (-(3 / 2 : ℝ)) =
          (∑ ρ ∈ s with κ ρ = n, (xiMultiplicity (ρ : ℂ) : ℝ)) *
            |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [(Finset.mem_filter.mp hρ).2]
      _ ≤ (A₀ * Real.log (|(n : ℝ)| + 3)) *
          |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hwin (Real.rpow_nonneg (abs_nonneg _) _)
      _ = A₀ *
          (Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) := by ring
  calc
    ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n,
        (xiMultiplicity (ρ : ℂ) : ℝ) * |(κ ρ : ℝ)| ^ (-(3 / 2 : ℝ)) ≤
        ∑ n ∈ s.image κ,
          A₀ * (Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) :=
      Finset.sum_le_sum hfiber
    _ = A₀ * ∑ n ∈ s.image κ,
        Real.log (|(n : ℝ)| + 3) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ A₀ * threeHalvesWindowTotalWeight := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      exact summable_threeHalvesWindowWeight.sum_le_tsum _ fun n _ ↦
        mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)]))
          (Real.rpow_nonneg (abs_nonneg _) _)

/-- The local unit-height count implies reciprocal three-halves summability,
with analytic multiplicity. -/
theorem xi_reciprocal_three_halves_summable (hCount : XiLocalZeroCountBound) :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ (3 / 2 : ℝ)) := by
  classical
  have hg := (xi_heightKey_reciprocal_three_halves_summable hCount).mul_left
    ((1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)))
  refine Summable.of_norm_bounded_eventually hg ?_
  have hcentral : {ρ : XiZero |
      |(heightKey (ρ : ℂ).im : ℝ)| < 2}.Finite := by
    have hstrip : {ρ : XiZero | (ρ : ℂ) ∈ xiZeroSupportInHeightStrip 3}.Finite := by
      exact (xiZeroSupportInHeightStrip_finite 3).preimage
        (f := fun ρ : XiZero ↦ (ρ : ℂ)) Subtype.val_injective.injOn
    apply hstrip.subset
    intro ρ hρ
    simp only [Set.mem_ofPred_eq] at hρ
    change (ρ : ℂ) ∈ xiZeroSupportInHeightStrip 3
    refine ⟨ρ.property, abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith [heightKey_lt (ρ : ℂ).im, (abs_lt.mp hρ).1]
    · linarith [le_heightKey_add_one (ρ : ℂ).im, (abs_lt.mp hρ).2]
  filter_upwards [hcentral.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hρ
  have hkeypos : 0 < |(heightKey (ρ : ℂ).im : ℝ)| := lt_of_lt_of_le (by norm_num) hρ
  have hhalfpos : 0 < |(heightKey (ρ : ℂ).im : ℝ)| / 2 := by positivity
  have hpows : (|(heightKey (ρ : ℂ).im : ℝ)| / 2) ^ (3 / 2 : ℝ) ≤
      ‖(ρ : ℂ)‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hhalfpos.le (half_abs_heightKey_le_norm ρ hρ) (by norm_num)
  have hinv : 1 / ‖(ρ : ℂ)‖ ^ (3 / 2 : ℝ) ≤
      1 / (|(heightKey (ρ : ℂ).im : ℝ)| / 2) ^ (3 / 2 : ℝ) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hhalfpos _) hpows
  have hscale : 1 / (|(heightKey (ρ : ℂ).im : ℝ)| / 2) ^ (3 / 2 : ℝ) =
      (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) *
        |(heightKey (ρ : ℂ).im : ℝ)| ^ (-(3 / 2 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg hhalfpos.le]
    rw [show |(heightKey (ρ : ℂ).im : ℝ)| / 2 =
        (1 / 2 : ℝ) * |(heightKey (ρ : ℂ).im : ℝ)| by ring,
      Real.mul_rpow (by norm_num) hkeypos.le]
  have hm : (0 : ℝ) ≤ xiMultiplicity (ρ : ℂ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm (Real.rpow_nonneg (norm_nonneg _) _))]
  calc
    (xiMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ (3 / 2 : ℝ) =
        (xiMultiplicity (ρ : ℂ) : ℝ) *
          (1 / ‖(ρ : ℂ)‖ ^ (3 / 2 : ℝ)) := by ring
    _ ≤ (xiMultiplicity (ρ : ℂ) : ℝ) *
          (1 / (|(heightKey (ρ : ℂ).im : ℝ)| / 2) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv hm
    _ = (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) *
          ((xiMultiplicity (ρ : ℂ) : ℝ) *
            |(heightKey (ρ : ℂ).im : ℝ)| ^ (-(3 / 2 : ℝ))) := by
      rw [hscale]
      ring

/-- The local unit-height count implies absolute reciprocal-square summability,
with analytic multiplicity. -/
theorem xi_reciprocal_sq_summable (hCount : XiLocalZeroCountBound) :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
  classical
  have hg := (xi_inv_one_add_normSq_summable hCount).mul_left 2
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {ρ : XiZero | ‖ρ.1‖ ≤ 1}.Finite := by
    have hb := xiZeroSupportInClosedBall_finite 1
    convert hb.preimage Subtype.val_injective.injOn using 1
    ext ρ
    simp [xiZeroSupportInClosedBall, Metric.mem_closedBall]
  filter_upwards [hfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hρ
  have hm : (0 : ℝ) ≤ xiMultiplicity ρ.1 := Nat.cast_nonneg _
  have hn : 0 < ‖ρ.1‖ ^ 2 := sq_pos_of_pos (by linarith)
  have hden : 1 + ‖ρ.1‖ ^ 2 ≤ 2 * ‖ρ.1‖ ^ 2 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm (sq_nonneg _)),
    Complex.normSq_eq_norm_sq]
  have hmain : (xiMultiplicity ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 ≤
      2 * ((xiMultiplicity ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2)) := by
    rw [div_le_iff₀ hn,
      show 2 * ((xiMultiplicity ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2)) * ‖ρ.1‖ ^ 2 =
        (xiMultiplicity ρ.1 : ℝ) *
          (2 * ‖ρ.1‖ ^ 2 / (1 + ‖ρ.1‖ ^ 2)) by ring]
    rcases hm.eq_or_lt with hm0 | hmpos
    · rw [← hm0]
      norm_num
    · rw [le_mul_iff_one_le_right hmpos, one_le_div₀ (by positivity)]
      exact hden
  exact hmain

/-- Every multiplicity-weighted reciprocal power of order at least two is
absolutely summable. -/
theorem xi_reciprocal_pow_summable (hCount : XiLocalZeroCountBound)
    (p : ℕ) (hp : 2 ≤ p) :
    Summable (fun ρ : XiZero ↦ (xiMultiplicity ρ.1 : ℂ) / ρ.1 ^ p) := by
  classical
  refine Summable.of_norm_bounded_eventually (xi_reciprocal_sq_summable hCount) ?_
  have hfin : {ρ : XiZero | ‖ρ.1‖ ≤ 1}.Finite := by
    convert (xiZeroSupportInClosedBall_finite 1).preimage
      Subtype.val_injective.injOn using 1
    ext ρ
    simp [xiZeroSupportInClosedBall, Metric.mem_closedBall]
  filter_upwards [hfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hρ
  rw [norm_div, Complex.norm_natCast, norm_pow]
  have hpow : ‖ρ.1‖ ^ 2 ≤ ‖ρ.1‖ ^ p :=
    pow_le_pow_right₀ (by linarith) hp
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hpow

/-- The genuine height cutoff is also stable under ordinary conjugation. -/
theorem xiZeroHeightCutoff_conjStable (T : ℝ) :
    (xiZeroHeightCutoff T).map (starRingEnd ℂ) = xiZeroHeightCutoff T := by
  classical
  rw [Multiset.ext]
  intro ρ
  have hmap := Multiset.count_map_eq_count' (starRingEnd ℂ)
    (xiZeroHeightCutoff T) (starRingEnd ℂ).injective (starRingEnd ℂ ρ)
  have hc : Multiset.count ρ ((xiZeroHeightCutoff T).map (starRingEnd ℂ)) =
      Multiset.count (starRingEnd ℂ ρ) (xiZeroHeightCutoff T) := by
    simpa using hmap
  rw [hc, count_xiZeroHeightCutoff, count_xiZeroHeightCutoff]
  simp [xiMultiplicity_conj]

/-- The height-symmetric finite reciprocal sum, with zeros repeated according
to analytic multiplicity. -/
noncomputable def reciprocalStarPartial (T : ℝ) : ℂ :=
  ((xiZeroHeightCutoff T).map (fun ρ ↦ 1 / ρ)).sum

theorem reciprocalStarPartial_conj (T : ℝ) :
    starRingEnd ℂ (reciprocalStarPartial T) = reciprocalStarPartial T := by
  classical
  have hstar (W : Multiset ℂ) :
      starRingEnd ℂ W.sum = (W.map (starRingEnd ℂ)).sum := by
    induction W using Multiset.induction_on with
    | empty => simp
    | cons z W ih => simp [map_add, ih]
  rw [reciprocalStarPartial, hstar]
  calc
    _ = (((xiZeroHeightCutoff T).map (starRingEnd ℂ)).map
          (fun x ↦ 1 / x)).sum := by
      rw [Multiset.map_map, Multiset.map_map]
      congr 2
      funext x
      simp
    _ = reciprocalStarPartial T := by
      rw [xiZeroHeightCutoff_conjStable]
      rfl

theorem abs_reciprocal_re_le_sq (ρ : XiZero) :
    |(1 / ρ.1).re| ≤ 1 / ‖ρ.1‖ ^ 2 := by
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hre := ρ.re_mem_Ioo
  rw [abs_of_pos (div_pos hre.1 (sq_pos_of_pos (norm_pos_iff.mpr ρ.ne_zero)))]
  exact div_le_div_of_nonneg_right (le_of_lt hre.2) (sq_nonneg _)

/-- Absolute summability of the conjugate-paired real first moment. -/
theorem xi_reciprocal_re_summable (hCount : XiLocalZeroCountBound) :
    Summable (fun ρ : XiZero ↦
      (xiMultiplicity ρ.1 : ℝ) * (1 / ρ.1).re) := by
  refine Summable.of_norm_bounded (xi_reciprocal_sq_summable hCount) ?_
  intro ρ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by simpa [one_div] using abs_reciprocal_re_le_sq ρ)
    (Nat.cast_nonneg _)

/-- Embed the finite support of a height cutoff into the subtype of xi zeros. -/
def xiHeightZeroEmbedding (T : ℝ) :
    {z // z ∈ xiZeroHeightSupportFinset T} ↪ XiZero where
  toFun z := ⟨z.1, (mem_xiZeroHeightSupportFinset_iff T z.1).mp z.2 |>.1⟩
  inj' := fun _ _ h ↦ Subtype.ext (congrArg (fun w : XiZero ↦ w.1) h)

/-- Distinct xi zeros in the height cutoff; multiplicity remains a weight. -/
noncomputable def xiZeroHeightFinset (T : ℝ) : Finset XiZero :=
  (xiZeroHeightSupportFinset T).attach.map (xiHeightZeroEmbedding T)

/-- Rewrite a multiplicity-expanded height-cutoff multiset sum as a weighted
sum over the corresponding finite set of distinct xi zeros. -/
theorem xiZeroHeightCutoff_map_sum_eq_sum (T : ℝ) (f : ℂ → ℂ) :
    ((xiZeroHeightCutoff T).map f).sum =
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity (ρ : ℂ) : ℂ) * f ρ := by
  classical
  simp [xiZeroHeightCutoff, xiZeroHeightFinset, xiHeightZeroEmbedding,
    Multiset.map_bind, Multiset.sum_bind, Multiset.sum_replicate,
    nsmul_eq_mul]
  rw [← Finset.sum_attach]
  rfl

theorem mem_xiZeroHeightFinset_iff (T : ℝ) (ρ : XiZero) :
    ρ ∈ xiZeroHeightFinset T ↔ |ρ.1.im| ≤ T := by
  classical
  rw [xiZeroHeightFinset, Finset.mem_map]
  constructor
  · rintro ⟨z, _, hz⟩
    have hv : z.1 = ρ.1 := congrArg Subtype.val hz
    subst ρ
    exact (mem_xiZeroHeightSupportFinset_iff T z.1).mp z.2 |>.2
  · intro h
    have hs : ρ.1 ∈ xiZeroHeightSupportFinset T :=
      (mem_xiZeroHeightSupportFinset_iff T ρ.1).mpr ⟨ρ.2, h⟩
    refine ⟨⟨ρ.1, hs⟩, by simp, ?_⟩
    rfl

theorem tendsto_xiZeroHeightFinset_atTop :
    Tendsto xiZeroHeightFinset atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  filter_upwards [eventually_ge_atTop (∑ ρ ∈ s, |ρ.1.im|)] with T hT
  intro ρ hρ
  rw [mem_xiZeroHeightFinset_iff]
  exact le_trans (Finset.single_le_sum
    (fun (x : XiZero) (_ : x ∈ s) ↦ abs_nonneg x.1.im) hρ) hT

theorem tendsto_xiZeroHeightFinset_sum {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {f : XiZero → E}
    (hf : Summable f) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ xiZeroHeightFinset T, f ρ)
      atTop (nhds (∑' ρ, f ρ)) := by
  exact hf.hasSum.comp tendsto_xiZeroHeightFinset_atTop

theorem reciprocalStarPartial_eq_real_sum (T : ℝ) :
    reciprocalStarPartial T =
      ((∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity ρ.1 : ℝ) * (1 / ρ.1).re : ℝ) : ℂ) := by
  classical
  apply Complex.ext
  · simp [reciprocalStarPartial, xiZeroHeightCutoff, xiZeroHeightFinset,
      xiHeightZeroEmbedding, Multiset.map_bind, Multiset.sum_bind,
      Multiset.sum_replicate, nsmul_eq_mul, Complex.inv_re]
    rw [← Finset.sum_attach]
    rfl
  · have hc := reciprocalStarPartial_conj T
    exact (Complex.conj_eq_iff_im.mp hc).trans (by simp)

/-- A finite shell estimate exposing the cancellation of imaginary parts. -/
theorem reciprocalStarPartial_sub_norm_le (T U : ℝ) :
    ‖reciprocalStarPartial U - reciprocalStarPartial T‖ ≤
      ∑ ρ ∈ xiZeroHeightFinset U, (xiMultiplicity ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 +
      ∑ ρ ∈ xiZeroHeightFinset T, (xiMultiplicity ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 := by
  rw [reciprocalStarPartial_eq_real_sum, reciprocalStarPartial_eq_real_sum,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  all_goals
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [one_div] using abs_reciprocal_re_le_sq ρ) (Nat.cast_nonneg _)

def ReciprocalStarConvergesTo (L : ℂ) : Prop :=
  Tendsto reciprocalStarPartial atTop (nhds L)

theorem exists_reciprocalStarLimit (hCount : XiLocalZeroCountBound) :
    ∃ L : ℂ, ReciprocalStarConvergesTo L := by
  let f : XiZero → ℝ := fun ρ ↦
    (xiMultiplicity ρ.1 : ℝ) * (1 / ρ.1).re
  refine ⟨((∑' ρ, f ρ : ℝ) : ℂ), ?_⟩
  unfold ReciprocalStarConvergesTo
  have ht := tendsto_xiZeroHeightFinset_sum (xi_reciprocal_re_summable hCount)
  have heq : reciprocalStarPartial = fun T : ℝ ↦
      ((∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity ρ.1 : ℝ) * (1 / ρ.1).re : ℝ) : ℂ) := by
    funext T
    exact reciprocalStarPartial_eq_real_sum T
  rw [heq]
  change Tendsto (Complex.ofReal ∘ fun T : ℝ ↦
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity ρ.1 : ℝ) * (1 / ρ.1).re) atTop _
  exact (Complex.continuous_ofReal.tendsto _).comp ht

/-- Finite binomial expansion of Lagarias's positive-index test. -/
theorem weilLiTest_nat_expansion (m : ℕ) {ρ : ℂ} (hρ : ρ ≠ 0) :
    weilLiTest (m : ℤ) ρ =
      ∑ k ∈ Finset.Icc 1 m,
        (-1 : ℂ) ^ (k + 1) * Nat.choose m k / ρ ^ k := by
  rw [weilLiTest, zpow_natCast]
  have hb := add_pow (-1 / ρ) 1 m
  simp only [one_pow, mul_one] at hb
  rw [show -1 / ρ + 1 = 1 - 1 / ρ by ring] at hb
  rw [hb]
  have hrange : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by ext k; simp
  rw [hrange, Finset.sum_Ico_eq_sub (f := fun k ↦
    (-1 : ℂ) ^ (k + 1) * Nat.choose m k / ρ ^ k) (by omega)]
  have hsum : (∑ k ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ (k + 1) * Nat.choose m k / ρ ^ k) =
      -(∑ k ∈ Finset.range (m + 1), (-1 / ρ) ^ k * Nat.choose m k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    simp [div_pow, hρ]
    ring
  rw [hsum]
  simp
  ring

noncomputable def reciprocalPowPartial (T : ℝ) (p : ℕ) : ℂ :=
  ((xiZeroHeightCutoff T).map (fun ρ ↦ 1 / ρ ^ p)).sum

theorem reciprocalPowPartial_eq_sum (T : ℝ) (p : ℕ) :
    reciprocalPowPartial T p =
      ∑ ρ ∈ xiZeroHeightFinset T,
        (xiMultiplicity ρ.1 : ℂ) / ρ.1 ^ p := by
  classical
  simp [reciprocalPowPartial, xiZeroHeightCutoff, xiZeroHeightFinset,
    xiHeightZeroEmbedding, Multiset.map_bind, Multiset.sum_bind,
    Multiset.sum_replicate, nsmul_eq_mul]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro z hz
  rfl

theorem reciprocalPowPartial_tendsto (hCount : XiLocalZeroCountBound)
    (p : ℕ) (hp : 2 ≤ p) :
    Tendsto (fun T ↦ reciprocalPowPartial T p) atTop
      (nhds (∑' ρ : XiZero, (xiMultiplicity ρ.1 : ℂ) / ρ.1 ^ p)) := by
  have ht := tendsto_xiZeroHeightFinset_sum
    (xi_reciprocal_pow_summable hCount p hp)
  simpa only [reciprocalPowPartial_eq_sum] using ht

theorem liStarPartial_neg (T : ℝ) (n : ℤ) :
    liStarPartial T (-n) = starRingEnd ℂ (liStarPartial T n) := by
  exact finiteLiZeroValue_neg_eq_conj _ (xiZeroHeightCutoff_valid T)
    (xiZeroHeightCutoff_reflectionStable T) n

theorem LiStarConvergesTo.neg {n : ℤ} {L : ℂ}
    (h : LiStarConvergesTo n L) :
    LiStarConvergesTo (-n) (starRingEnd ℂ L) := by
  unfold LiStarConvergesTo at h ⊢
  have hc := (Complex.continuous_conj.tendsto L).comp h
  simpa [liStarPartial_neg, Function.comp_def] using hc

private theorem finiteLiZeroValue_nat_expansion (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (m : ℕ) :
    finiteLiZeroValue Z (m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        ((-1 : ℂ) ^ (k + 1) * Nat.choose m k) *
          (Z.map (fun ρ ↦ 1 / ρ ^ k)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp [finiteLiZeroValue]
  | @cons ρ Z ih =>
      have hρ := hZ ρ (by simp)
      have hZ' : ValidWeilZeroCutoff Z := fun z hz ↦ hZ z (by simp [hz])
      have hi := ih hZ'
      simp only [finiteLiZeroValue] at hi
      rw [finiteLiZeroValue, Multiset.map_cons, Multiset.sum_cons,
        weilLiTest_nat_expansion m hρ.1, hi]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem liStarPartial_nat_expansion (T : ℝ) (m : ℕ) :
    liStarPartial T (m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        ((-1 : ℂ) ^ (k + 1) * Nat.choose m k) *
          reciprocalPowPartial T k := by
  exact finiteLiZeroValue_nat_expansion _ (xiZeroHeightCutoff_valid T) m

@[simp] theorem reciprocalPowPartial_one (T : ℝ) :
    reciprocalPowPartial T 1 = reciprocalStarPartial T := by
  simp [reciprocalPowPartial, reciprocalStarPartial]

theorem exists_liStarLimit_nat (hCount : XiLocalZeroCountBound)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ L : ℂ, LiStarConvergesTo (m : ℤ) L := by
  obtain ⟨L₁, hL₁⟩ := exists_reciprocalStarLimit hCount
  have hterm : ∀ k ∈ Finset.Icc 1 m, ∃ L : ℂ,
      Tendsto (fun T : ℝ ↦
        ((-1 : ℂ) ^ (k + 1) * Nat.choose m k) * reciprocalPowPartial T k)
        atTop (nhds L) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · refine ⟨((-1 : ℂ) ^ 2 * Nat.choose m 1) * L₁, ?_⟩
      exact tendsto_const_nhds.mul (by simpa [ReciprocalStarConvergesTo] using hL₁)
    · refine ⟨((-1 : ℂ) ^ (k + 1) * Nat.choose m k) *
          (∑' ρ : XiZero, (xiMultiplicity ρ.1 : ℂ) / ρ.1 ^ k), ?_⟩
      exact tendsto_const_nhds.mul (reciprocalPowPartial_tendsto hCount k hk2)
  let L : ℕ → ℂ := fun k ↦ if hk : k ∈ Finset.Icc 1 m then
    Classical.choose (hterm k hk) else 0
  have hL : ∀ k ∈ Finset.Icc 1 m, Tendsto (fun T : ℝ ↦
      ((-1 : ℂ) ^ (k + 1) * Nat.choose m k) * reciprocalPowPartial T k)
      atTop (nhds (L k)) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    rw [show L k = Classical.choose (hterm k hk) by simp [L, hk'.1, hk'.2]]
    exact Classical.choose_spec (hterm k hk)
  refine ⟨∑ k ∈ Finset.Icc 1 m, L k, ?_⟩
  unfold LiStarConvergesTo
  rw [show (fun T : ℝ ↦ liStarPartial T (m : ℤ)) = fun T ↦
      ∑ k ∈ Finset.Icc 1 m,
        ((-1 : ℂ) ^ (k + 1) * Nat.choose m k) * reciprocalPowPartial T k by
        funext T
        exact liStarPartial_nat_expansion T m]
  exact tendsto_finset_sum _ fun k hk ↦ hL k hk

theorem exists_liStarLimit_neg_nat (hCount : XiLocalZeroCountBound)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ L : ℂ, LiStarConvergesTo (-((m : ℕ) : ℤ)) L := by
  obtain ⟨L, hL⟩ := exists_liStarLimit_nat hCount m hm
  exact ⟨starRingEnd ℂ L, hL.neg⟩

/-- The single open local-count proposition implies existence of every
Lagarias height-ordered Li star sum. -/
theorem liStarConvergence_of_localZeroCount (hCount : XiLocalZeroCountBound) :
    ∀ n : ℤ, ∃ L : ℂ, LiStarConvergesTo n L := by
  intro n
  cases n with
  | ofNat m =>
      cases m with
      | zero =>
          refine ⟨0, ?_⟩
          unfold LiStarConvergesTo liStarPartial
          simpa [finiteLiZeroValue] using (tendsto_const_nhds :
            Tendsto (fun _ : ℝ ↦ (0 : ℂ)) atTop (nhds 0))
      | succ m =>
          exact exists_liStarLimit_nat hCount (m + 1) (by omega)
  | negSucc m =>
      change ∃ L : ℂ, LiStarConvergesTo (-((m + 1 : ℕ) : ℤ)) L
      exact exists_liStarLimit_neg_nat hCount (m + 1) (by omega)

end RHGarden
