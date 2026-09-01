/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) 2026 Future Technologies Laboratory LLC.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

The zero-count estimate imported below is authored by Anthropic PBC in
Zeta23, pinned at commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
This file supplies only the RH Garden representation adapter.
-/

import RHGarden.LiStarConvergence
import Zeta23.RvM.LocalCount

noncomputable section

open Complex Set

namespace RHGarden

theorem zeta23_zerosIn_eq_rhGarden (a b : ℝ) :
    Zeta23.zerosIn a b = zetaZeroSupportInHeightWindow a b := by
  ext ρ
  simp [Zeta23.zerosIn, Zeta23.IsNontrivialZero,
    zetaZeroSupportInHeightWindow]
  tauto

theorem zeta23_Ncount_eq_rhGarden (a b : ℝ) :
    Zeta23.Ncount a b = zetaHeightWindowMultiplicityCount a b := by
  rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _
    (by rw [zeta23_zerosIn_eq_rhGarden]; exact zetaZeroSupportInHeightWindow_finite a b)]
  rw [zetaHeightWindowMultiplicityCount]
  have hfinset :
      (show (Zeta23.zerosIn a b).Finite from by
        rw [zeta23_zerosIn_eq_rhGarden]
        exact zetaZeroSupportInHeightWindow_finite a b).toFinset =
        zetaZeroHeightWindowSupportFinset a b := by
    ext ρ
    simp [zeta23_zerosIn_eq_rhGarden,
      mem_zetaZeroHeightWindowSupportFinset_iff,
      zetaZeroSupportInHeightWindow,
      isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo]
  rw [hfinset]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rfl

theorem xiLocalZeroCountBound : XiLocalZeroCountBound := by
  obtain ⟨A₀, hA₀, hcount⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA₀, fun t ↦ ?_⟩
  rw [xiHeightWindowMultiplicityCount_eq_zeta,
    ← zeta23_Ncount_eq_rhGarden]
  exact hcount t

theorem liStarConvergence :
    ∀ n : ℤ, ∃ L : ℂ, LiStarConvergesTo n L :=
  liStarConvergence_of_localZeroCount xiLocalZeroCountBound

end RHGarden
