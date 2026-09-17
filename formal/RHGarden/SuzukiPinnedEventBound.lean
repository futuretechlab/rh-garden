import RHGarden.SuzukiPrimePowerSurcharge
import Zeta23.Chebyshev

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
An explicit unconditional candidate, kept separate from adequate cost bounds.
The numerical audit shows that its global-prefix error is far too large. -/
noncomputable section
open scoped BigOperators
namespace RHGarden

def suzukiPinnedPrefixUpper (q : ℕ) : ℝ :=
  2 * Real.log 4 * Real.sqrt q + 2 * Real.log q + Real.log q ^ 2 / 2

theorem mangoldtSlope_le_pinnedPrefix {q : ℕ} (hq : 1 ≤ q) :
    suzukiMangoldtSlope q ≤ suzukiPinnedPrefixUpper q := by
  have h := Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise
    (x := (q : ℝ)) (by exact_mod_cast hq)
  rw [Nat.floor_natCast] at h
  simpa only [suzukiMangoldtSlope, suzukiPinnedPrefixUpper,
    show Finset.Icc 1 q = Finset.Ioc 0 q from Finset.Icc_succ_left_eq_Ioc _ _] using h

/-- Retain the exact lower arithmetic prefix. This bound does not sample
the unknown intervening prime locations, but is quantitatively too coarse. -/
theorem excess_le_pinnedPrefix_anchored {m q : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q) :
    suzukiArrivalServiceExcess m q ≤ suzukiPinnedPrefixUpper q -
      suzukiMangoldtSlope m - suzukiRootService (Real.sqrt m) (Real.sqrt q) := by
  unfold suzukiArrivalServiceExcess
  rw [← suzukiMangoldtSlope_sub_eq_weightedInterval hm hmq]
  linarith [mangoldtSlope_le_pinnedPrefix (hm.trans hmq)]

/-- With the exact signed anchor, its lower-prefix terms cancel exactly.
The remaining overestimate is P(q)-S(sqrt(q)), not a reset-to-zero queue. -/
theorem pinnedPrefix_signed_cancellation (m q : ℕ) :
    -suzukiRootSlopeDiscrepancy (Real.sqrt m) +
      (suzukiPinnedPrefixUpper q - suzukiMangoldtSlope m -
        suzukiRootService (Real.sqrt m) (Real.sqrt q)) =
      suzukiPinnedPrefixUpper q - suzukiRootArchSlope (Real.sqrt q) := by
  unfold suzukiRootSlopeDiscrepancy suzukiRootMangoldtSlope suzukiRootService
  rw [Real.sq_sqrt (Nat.cast_nonneg m), Nat.floor_natCast]
  ring

end RHGarden
