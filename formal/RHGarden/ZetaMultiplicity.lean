/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) 2026 Future Technologies Laboratory LLC.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

The completed-zeta order seam below is adapted from
anthropics/formal-math, zeta23/Zeta23/WeilEF/XiLogDeriv.lean,
commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
-/

import RHGarden.XiZeroCutoff
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

open Complex Filter Set Metric Topology

namespace RHGarden

theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s
      (differentiableAt_id.div_const _)
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGamma : Gammaℝ = fun u : ℂ =>
      (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) := funext Gammaℝ_def
  rw [hGamma]
  exact h1.mul h2

theorem analyticAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt
    (fun u hu => (differentiableAt_Gammaℝ_of_re_pos hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

theorem completedZeta_eventuallyEq_Gammaℝ_mul_zeta {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hGamma := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp

theorem analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

theorem completedZeta_order_eq_zeta_order {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt completedRiemannZeta ρ =
      analyticOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun e => by simp [e] at h1
  have hGamma : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hev := completedZeta_eventuallyEq_Gammaℝ_mul_zeta h0
  have hGammaAn := analyticAt_Gammaℝ_of_re_pos h0
  have hzetaAn := analyticAt_riemannZeta_of_ne_one hρ1
  rw [analyticOrderAt_congr hev]
  have hmul := analyticOrderAt_mul hGammaAn hzetaAn
  rw [show (Gammaℝ * riemannZeta) =
      (fun u => Gammaℝ u * riemannZeta u) from rfl] at hmul
  rw [hmul, hGammaAn.analyticOrderAt_eq_zero.mpr hGamma, zero_add]

private def xiCompletedPrefactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)

private theorem riemannXi_eventuallyEq_prefactor_mul_completedZeta {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannXi =ᶠ[𝓝 ρ]
      fun s => xiCompletedPrefactor s * completedRiemannZeta s := by
  have hρ0 : ρ ≠ 0 := fun e => by simp [e] at h0
  have hρ1 : ρ ≠ 1 := fun e => by simp [e] at h1
  filter_upwards [eventually_ne_nhds hρ0, eventually_ne_nhds hρ1] with s hs0 hs1
  simpa [xiCompletedPrefactor] using riemannXi_eq_completedRiemannZeta hs0 hs1

theorem analyticOrderAt_riemannXi_eq_completedZeta {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannXi ρ =
      analyticOrderAt completedRiemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := fun e => by simp [e] at h0
  have hρ1 : ρ ≠ 1 := fun e => by simp [e] at h1
  have hprefactorAn : AnalyticAt ℂ xiCompletedPrefactor ρ := by
    unfold xiCompletedPrefactor
    fun_prop
  have hprefactor : xiCompletedPrefactor ρ ≠ 0 := by
    unfold xiCompletedPrefactor
    exact mul_ne_zero (mul_ne_zero (by norm_num) hρ0) (sub_ne_zero.mpr hρ1)
  have hcompletedAn : AnalyticAt ℂ completedRiemannZeta ρ := by
    exact (analyticAt_Gammaℝ_of_re_pos h0).mul
      (analyticAt_riemannZeta_of_ne_one hρ1) |>.congr
        (completedZeta_eventuallyEq_Gammaℝ_mul_zeta h0).symm
  rw [analyticOrderAt_congr
    (riemannXi_eventuallyEq_prefactor_mul_completedZeta h0 h1)]
  have hmul := analyticOrderAt_mul hprefactorAn hcompletedAn
  rw [show (xiCompletedPrefactor * completedRiemannZeta) =
      (fun s => xiCompletedPrefactor s * completedRiemannZeta s) from rfl] at hmul
  rw [hmul, hprefactorAn.analyticOrderAt_eq_zero.mpr hprefactor, zero_add]

noncomputable def zetaMultiplicity (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

theorem xiMultiplicity_eq_zetaMultiplicity {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    xiMultiplicity ρ = zetaMultiplicity ρ := by
  have hzero : riemannXi ρ = 0 := hρ.riemannXi_eq_zero
  obtain ⟨h0, h1⟩ := riemannXi_zero_re_mem_Ioo hzero
  rw [xiMultiplicity_eq_analyticOrderNatAt, zetaMultiplicity,
    analyticOrderNatAt]
  congr 1
  exact (analyticOrderAt_riemannXi_eq_completedZeta h0 h1).trans
    (completedZeta_order_eq_zeta_order h0 h1)

theorem isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo (ρ : ℂ) :
    IsNontrivialZetaZero ρ ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · intro hρ
    exact ⟨hρ.1, riemannXi_zero_re_mem_Ioo hρ.riemannXi_eq_zero⟩
  · rintro ⟨hzeta, h0, h1⟩
    refine ⟨hzeta, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hρ1
      subst ρ
      norm_num at h1

/-- Xi-divisor support in the half-open height window `(a,b]`. -/
def xiZeroSupportInHeightWindow (a b : ℝ) : Set ℂ :=
  {ρ | ρ ∈ xiDivisor.support ∧ a < ρ.im ∧ ρ.im ≤ b}

theorem xiZeroSupportInHeightWindow_finite (a b : ℝ) :
    (xiZeroSupportInHeightWindow a b).Finite := by
  apply (xiZeroSupportInHeightStrip_finite (max |a| |b|)).subset
  intro ρ hρ
  refine ⟨hρ.1, abs_le.mpr ⟨?_, ?_⟩⟩
  · exact le_trans (neg_le_neg (le_max_left |a| |b|))
      ((neg_abs_le a).trans hρ.2.1.le)
  · exact hρ.2.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))

noncomputable def xiZeroHeightWindowSupportFinset (a b : ℝ) : Finset ℂ :=
  (xiZeroSupportInHeightWindow_finite a b).toFinset

theorem mem_xiZeroHeightWindowSupportFinset_iff (a b : ℝ) (ρ : ℂ) :
    ρ ∈ xiZeroHeightWindowSupportFinset a b ↔
      ρ ∈ xiDivisor.support ∧ a < ρ.im ∧ ρ.im ≤ b := by
  rw [xiZeroHeightWindowSupportFinset, Set.Finite.mem_toFinset]
  rfl

noncomputable def xiZeroHeightWindowCutoff (a b : ℝ) : Multiset ℂ :=
  (xiZeroHeightWindowSupportFinset a b).val.bind
    (fun ρ => Multiset.replicate (xiMultiplicity ρ) ρ)

theorem count_xiZeroHeightWindowCutoff (a b : ℝ) (ρ : ℂ) :
    Multiset.count ρ (xiZeroHeightWindowCutoff a b) =
      if a < ρ.im ∧ ρ.im ≤ b then xiMultiplicity ρ else 0 := by
  classical
  rw [xiZeroHeightWindowCutoff, Multiset.count_bind]
  by_cases hwindow : a < ρ.im ∧ ρ.im ≤ b
  · by_cases hzero : riemannXi ρ = 0
    · simp [Multiset.count_replicate, mem_xiZeroHeightWindowSupportFinset_iff,
        Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hwindow, hzero]
    · have hdiv : xiDivisor ρ = 0 := by
        apply not_ne_iff.mp
        exact fun h => hzero ((xiDivisor_ne_zero_iff ρ).mp h)
      simp [Multiset.count_replicate, mem_xiZeroHeightWindowSupportFinset_iff,
        Function.mem_support, xiMultiplicity, hwindow, hdiv]
  · simp [Multiset.count_replicate, mem_xiZeroHeightWindowSupportFinset_iff,
      Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hwindow]

noncomputable def xiHeightWindowMultiplicityCount (a b : ℝ) : ℕ :=
  (xiZeroHeightWindowCutoff a b).card

theorem xiHeightWindowMultiplicityCount_eq_sum (a b : ℝ) :
    xiHeightWindowMultiplicityCount a b =
      ∑ ρ ∈ xiZeroHeightWindowSupportFinset a b, xiMultiplicity ρ := by
  simp [xiHeightWindowMultiplicityCount, xiZeroHeightWindowCutoff]

def zetaZeroSupportInHeightWindow (a b : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    a < ρ.im ∧ ρ.im ≤ b}

theorem zetaZeroSupportInHeightWindow_eq_xi (a b : ℝ) :
    zetaZeroSupportInHeightWindow a b = xiZeroSupportInHeightWindow a b := by
  ext ρ
  simp only [zetaZeroSupportInHeightWindow, xiZeroSupportInHeightWindow,
    Set.mem_ofPred_eq]
  rw [mem_xiDivisor_support_iff_nontrivialZetaZero]
  rw [isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo]
  tauto

theorem zetaZeroSupportInHeightWindow_finite (a b : ℝ) :
    (zetaZeroSupportInHeightWindow a b).Finite := by
  rw [zetaZeroSupportInHeightWindow_eq_xi]
  exact xiZeroSupportInHeightWindow_finite a b

noncomputable def zetaZeroHeightWindowSupportFinset (a b : ℝ) : Finset ℂ :=
  (zetaZeroSupportInHeightWindow_finite a b).toFinset

theorem mem_zetaZeroHeightWindowSupportFinset_iff (a b : ℝ) (ρ : ℂ) :
    ρ ∈ zetaZeroHeightWindowSupportFinset a b ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        a < ρ.im ∧ ρ.im ≤ b := by
  rw [zetaZeroHeightWindowSupportFinset, Set.Finite.mem_toFinset]
  rfl

noncomputable def zetaHeightWindowMultiplicityCount (a b : ℝ) : ℕ :=
  ∑ ρ ∈ zetaZeroHeightWindowSupportFinset a b, zetaMultiplicity ρ

theorem xiHeightWindowMultiplicityCount_eq_zeta (a b : ℝ) :
    xiHeightWindowMultiplicityCount a b =
      zetaHeightWindowMultiplicityCount a b := by
  rw [xiHeightWindowMultiplicityCount_eq_sum]
  have hfinset : xiZeroHeightWindowSupportFinset a b =
      zetaZeroHeightWindowSupportFinset a b := by
    ext ρ
    rw [mem_xiZeroHeightWindowSupportFinset_iff,
      mem_zetaZeroHeightWindowSupportFinset_iff,
      mem_xiDivisor_support_iff_nontrivialZetaZero,
      isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo]
    tauto
  rw [hfinset]
  apply Finset.sum_congr rfl
  intro ρ hρ
  apply xiMultiplicity_eq_zetaMultiplicity
  rw [isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo]
  have hm := (mem_zetaZeroHeightWindowSupportFinset_iff a b ρ).mp hρ
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

/-- The stable-RH-Garden formulation of the externally formalized upstream
unit-height zeta zero-count estimate. No proof is claimed here. -/
def XiLocalZeroCountBound : Prop :=
  ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (xiHeightWindowMultiplicityCount t (t + 1) : ℝ) ≤
      A₀ * Real.log (|t| + 3)

end RHGarden
