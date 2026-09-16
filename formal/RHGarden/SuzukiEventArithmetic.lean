import RHGarden.SuzukiEventPartition

/-!
Copyright (c) 2026 Future Technologies Laboratory LLC.

Finite sample arithmetic for the event verifier. Endpoint samples and
integrals are kept separate: the right endpoint belongs to the next cell,
but a single endpoint has zero measure in a cell integral.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology Interval

namespace RHGarden

theorem rootChebyshevError_eq_jumpAwareKernel
    {q r : ℕ} (h : IsSuzukiEventFreeCell q r) {u : ℝ}
    (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) (hu : 0 < u) :
    suzukiChebyshevError (u ^ 2) / u ^ 2 =
      ((q : ℝ) + suzukiChebyshevError q) / u ^ 2 - 1 := by
  have hqx : (q : ℝ) ≤ u ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg q]
  have hxr : u ^ 2 < (r : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg r]
  rw [suzukiChebyshevError_eq_jumpAwareSample h hqx hxr]
  field_simp

theorem intervalIntegrable_rootChebyshevError_eventFree
    {q r : ℕ} (hq : 0 < q) (h : IsSuzukiEventFreeCell q r) :
    IntervalIntegrable (fun u => suzukiChebyshevError (u ^ 2) / u ^ 2)
      volume (Real.sqrt q) (Real.sqrt r) := by
  have hqr : Real.sqrt q ≤ Real.sqrt r := Real.sqrt_le_sqrt (by exact_mod_cast h.1.le)
  have hpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hq)
  have hint : IntervalIntegrable
      (fun u : ℝ => ((q : ℝ) + suzukiChebyshevError q) / u ^ 2 - 1)
      volume (Real.sqrt q) (Real.sqrt r) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hqr
    intro u hu
    exact ((continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (ne_of_gt (hpos.trans_le hu.1)))).sub
        continuousAt_const).continuousWithinAt
  apply hint.congr_uIoo
  intro u hu
  rw [uIoo_of_le hqr] at hu
  exact (rootChebyshevError_eq_jumpAwareKernel h hu.1.le hu.2
    (hpos.trans hu.1)).symm

/-- The integral of the actual error on a half-open event cell is exactly
the elementary sample formula; the jump at the right endpoint is null. -/
theorem integral_rootChebyshevError_eventFree
    {q r : ℕ} (hq : 0 < q) (h : IsSuzukiEventFreeCell q r) :
    (∫ u in Real.sqrt q..Real.sqrt r, suzukiChebyshevError (u ^ 2) / u ^ 2) =
      ((q : ℝ) + suzukiChebyshevError q) *
        (1 / Real.sqrt q - 1 / Real.sqrt r) - (Real.sqrt r - Real.sqrt q) := by
  rw [← integral_jumpAwareChebyshevEventCell hq h.1.le]
  apply intervalIntegral.integral_congr_uIoo
  intro u hu
  rw [uIoo_of_le (Real.sqrt_le_sqrt (by exact_mod_cast h.1.le))] at hu
  exact rootChebyshevError_eq_jumpAwareKernel h hu.1.le hu.2
    ((Real.sqrt_pos.2 (by exact_mod_cast hq)).trans hu.1)

namespace SuzukiMangoldtBlockChain

/-- Only the finitely many left samples in this chain are constrained. -/
def sampleBounds {q r : ℕ} (rho : ℕ → ℝ) : SuzukiMangoldtBlockChain q r → Prop
  | .single _ => suzukiChebyshevError q ≤ rho q
  | .cons _ tail => suzukiChebyshevError q ≤ rho q ∧ tail.sampleBounds rho

/-- Elementary finite sum representing the transformed integral of the
piecewise slope-minus-one sample envelope. -/
def jumpIntegral {q r : ℕ} (rho : ℕ → ℝ) : SuzukiMangoldtBlockChain q r → ℝ
  | .single _ => ((q : ℝ) + rho q) * (1 / Real.sqrt q - 1 / Real.sqrt r) -
      (Real.sqrt r - Real.sqrt q)
  | @SuzukiMangoldtBlockChain.cons q p r _ tail =>
      (((q : ℝ) + rho q) * (1 / Real.sqrt q - 1 / Real.sqrt p) -
        (Real.sqrt p - Real.sqrt q)) + tail.jumpIntegral rho

theorem intervalIntegrable_rootChebyshevError {q r : ℕ}
    (chain : SuzukiMangoldtBlockChain q r) :
    IntervalIntegrable (fun u => suzukiChebyshevError (u ^ 2) / u ^ 2)
      volume (Real.sqrt q) (Real.sqrt r) := by
  induction chain with
  | single h =>
      exact intervalIntegrable_rootChebyshevError_eventFree h.left_pos
        (isSuzukiEventFreeCell_of_mangoldtBlock h)
  | cons h tail ih => exact
      (intervalIntegrable_rootChebyshevError_eventFree h.left_pos
        (isSuzukiEventFreeCell_of_mangoldtBlock h)).trans ih

theorem integral_rootChebyshevError_eq_jumpIntegral {q r : ℕ}
    (chain : SuzukiMangoldtBlockChain q r) :
    (∫ u in Real.sqrt q..Real.sqrt r, suzukiChebyshevError (u ^ 2) / u ^ 2) =
      chain.jumpIntegral (fun k => suzukiChebyshevError k) := by
  induction chain with
  | single h =>
      exact integral_rootChebyshevError_eventFree h.left_pos
        (isSuzukiEventFreeCell_of_mangoldtBlock h)
  | cons h tail ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_rootChebyshevError_eventFree h.left_pos
          (isSuzukiEventFreeCell_of_mangoldtBlock h)) tail.intervalIntegrable_rootChebyshevError,
        integral_rootChebyshevError_eventFree h.left_pos
          (isSuzukiEventFreeCell_of_mangoldtBlock h), ih]
      rfl

theorem jumpIntegral_mono_samples {q r : ℕ}
    (chain : SuzukiMangoldtBlockChain q r) {rho : ℕ → ℝ}
    (hb : chain.sampleBounds rho) :
    chain.jumpIntegral (fun k => suzukiChebyshevError k) ≤ chain.jumpIntegral rho := by
  have localBound {q r : ℕ} (h : IsMangoldtBlock q r)
      (hs : suzukiChebyshevError q ≤ rho q) :
      ((q : ℝ) + suzukiChebyshevError q) * (1 / Real.sqrt q - 1 / Real.sqrt r) -
          (Real.sqrt r - Real.sqrt q) ≤
        ((q : ℝ) + rho q) * (1 / Real.sqrt q - 1 / Real.sqrt r) -
          (Real.sqrt r - Real.sqrt q) := by
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_right (add_le_add le_rfl hs)
    exact sub_nonneg.mpr (one_div_le_one_div_of_le
      (Real.sqrt_pos.2 (by exact_mod_cast h.left_pos))
      (Real.sqrt_le_sqrt (by exact_mod_cast h.left_lt.le)))
  induction chain with
  | single h => exact localBound h hb
  | cons h tail ih => exact add_le_add (localBound h hb.1) (ih hb.2)

/-- Finite one-sided samples produce an event excess bound. The anchor
error is exact, and the terminal sample is post-jump. No absolute-error
estimate or continuous input hypothesis is used. -/
theorem arrivalServiceExcess_le_jumpSamples {m n : ℕ}
    (chain : SuzukiMangoldtBlockChain m n) {rho : ℕ → ℝ}
    (hb : chain.sampleBounds rho) (hn : suzukiChebyshevError n ≤ rho n) :
    suzukiArrivalServiceExcess m n ≤
      rho n / Real.sqrt n - suzukiChebyshevError m / Real.sqrt m +
        chain.jumpIntegral rho + suzukiRootArchDefect (Real.sqrt m) (Real.sqrt n) := by
  have hm : 2 ≤ m := by
    cases chain with
    | single h => exact h.left_event.two_le
    | cons h _ => exact h.left_event.two_le
  rw [suzukiArrivalServiceExcess_eq_chebyshevError hm chain.left_le_right.le,
    chain.integral_rootChebyshevError_eq_jumpIntegral]
  have he := div_le_div_of_nonneg_right hn (Real.sqrt_nonneg (n : ℝ))
  have hi := chain.jumpIntegral_mono_samples hb
  linarith

theorem jumpIntegral_add_const {q r : ℕ} (chain : SuzukiMangoldtBlockChain q r)
    (rho : ℕ → ℝ) (delta : ℝ) :
    chain.jumpIntegral (fun k => rho k + delta) = chain.jumpIntegral rho +
      delta * (1 / Real.sqrt q - 1 / Real.sqrt r) := by
  induction chain with
  | single h => simp only [jumpIntegral]; ring
  | cons h tail ih => simp only [jumpIntegral, ih]; ring

/-- The exact error caused by a uniform conservative sample allowance.
The lower anchor error is still exact, so endpoint and integral errors
telescope to `delta / sqrt m`, independently of the interval length. -/
theorem transformed_uniform_sample_allowance {m n : ℕ}
    (chain : SuzukiMangoldtBlockChain m n) (delta : ℝ) :
    (suzukiChebyshevError n + delta) / Real.sqrt n -
        suzukiChebyshevError m / Real.sqrt m +
        chain.jumpIntegral (fun k => suzukiChebyshevError k + delta) +
        suzukiRootArchDefect (Real.sqrt m) (Real.sqrt n) =
      suzukiArrivalServiceExcess m n + delta / Real.sqrt m := by
  have hm : 2 ≤ m := by
    cases chain with
    | single h => exact h.left_event.two_le
    | cons h _ => exact h.left_event.two_le
  rw [suzukiArrivalServiceExcess_eq_chebyshevError hm chain.left_le_right.le,
    chain.integral_rootChebyshevError_eq_jumpIntegral, chain.jumpIntegral_add_const]
  ring

end SuzukiMangoldtBlockChain

namespace SuzukiEventChain

def eventLogWeight (n : ℕ) : ℝ := by
  classical
  exact if IsMangoldtEvent n then Real.log n / Real.sqrt n else 0

/-- An unconditional event-local arithmetic coarsening from the pinned
`vonMangoldt_le_log`. Only actual events are charged; a non-event terminal
has zero weight and the anchor is excluded. Prime powers remain events,
and the bound deliberately overcharges their logarithmic weight. -/
def logArrival {q r : ℕ} : SuzukiEventChain q r → ℝ
  | .nil _ => 0
  | @cons _ p _ _ tail => eventLogWeight p + tail.logArrival

theorem weightedArrival_le_logArrival {q r : ℕ} (chain : SuzukiEventChain q r) :
    suzukiWeightedMangoldtInterval q r ≤ chain.logArrival := by
  classical
  induction chain with
  | nil q => simp [suzukiWeightedMangoldtInterval, logArrival]
  | @cons q p r h tail ih =>
      rw [suzukiWeightedMangoldtInterval_add h.1.le tail.ordered,
        weightedMangoldtInterval_eventFree_right h]
      apply add_le_add _ ih
      by_cases hp : IsMangoldtEvent p
      · simp only [eventLogWeight, if_pos hp]
        exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _)
      · have hz : ArithmeticFunction.vonMangoldt p = 0 := by
          simpa only [IsMangoldtEvent, not_not] using hp
        simp [eventLogWeight, hp, hz]

theorem excess_le_logArrival_sub_service {q r : ℕ} (chain : SuzukiEventChain q r) :
    suzukiArrivalServiceExcess q r ≤
      chain.logArrival - suzukiRootService (Real.sqrt q) (Real.sqrt r) := by
  exact sub_le_sub_right chain.weightedArrival_le_logArrival _

end SuzukiEventChain

end RHGarden
