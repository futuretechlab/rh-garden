import RHGarden.SuzukiShiftedHerglotz
import RHGarden.SuzukiLocalPositive

noncomputable section

open Set
open scoped BigOperators

namespace RHGarden

/-! ## The global shifted criterion -/

/-- Suzuki's shifted global positivity criterion, stated without the
intermediate eventual-positivity predicate.  This is an equivalence of open
propositions; it does not assert either side for an unknown parameter. -/
theorem xiZeroFreeRightOf_iff_shiftedGlobalNonnegative (ω : ℝ) :
    XiZeroFreeRightOf ω ↔ ∀ t : ℝ, 0 ≤ suzukiPsiShifted ω t := by
  constructor
  · intro hzero
    exact xiShiftedNevanlinna_implies_shiftedPsi_nonnegative ω
      ((xiZeroFreeRightOf_iff_xiShiftedNevanlinna ω).mp hzero)
  · intro hnonneg
    apply xiZeroFreeRightOf_of_shifted_eventually_nonnegative ω
    exact ⟨0, fun t _ => hnonneg t⟩

/-- At `ω = 0`, shifted global positivity is exactly RH. -/
theorem riemannHypothesis_iff_shifted_zero_nonnegative :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 ≤ suzukiPsiShifted 0 t := by
  rw [riemannHypothesis_iff_xiZeroFreeRightOf_zero,
    xiZeroFreeRightOf_iff_shiftedGlobalNonnegative]

theorem half_mem_suzukiShiftedPositivitySet :
    (1 / 2 : ℝ) ∈ SuzukiShiftedPositivitySet :=
  suzukiPsiShifted_half_nonnegative

theorem mem_suzukiShiftedPositivitySet_iff_xiZeroFreeRightOf (ω : ℝ) :
    ω ∈ SuzukiShiftedPositivitySet ↔ XiZeroFreeRightOf ω := by
  rw [xiZeroFreeRightOf_iff_shiftedGlobalNonnegative]
  rfl

/-! ## A formally exact shifted prime-side evaluator -/

/-- The exact shifted arithmetic representation obtained by applying
Suzuki's Volterra operator to the already certified prime-side formula.  It
is deliberately defined from the real finite-prime expression, so numerical
implementations have a formal normalization target. -/
noncomputable def suzukiPsiShiftedPrimeSide (ω t : ℝ) : ℝ :=
  SuzukiShift ω suzukiPsiPrimeSide t

theorem suzukiPsiShifted_eq_primeSide (ω t : ℝ) :
    suzukiPsiShifted ω t = suzukiPsiShiftedPrimeSide ω t := by
  have hfun : suzukiPsi = suzukiPsiPrimeSide :=
    funext suzukiPsi_eq_primeSide
  simp only [suzukiPsiShifted, suzukiPsiShiftedPrimeSide, hfun]

/-! ## Prime cells -/

/-- The half-open cell on which the finite prime support in Suzuki's
unshifted arithmetic formula is fixed. -/
def SuzukiPrimeCell (n : ℕ) : Set ℝ :=
  Set.Ico (Real.log n) (Real.log (n + 1))

theorem natFloor_exp_eq_of_mem_suzukiPrimeCell
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ SuzukiPrimeCell n) :
    ⌊Real.exp t⌋₊ = n := by
  rw [Nat.floor_eq_iff (Real.exp_pos t).le]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hleft : (n : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log hnreal]
    exact Real.exp_le_exp.mpr ht.1
  have hright : Real.exp t < (n : ℝ) + 1 := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact Real.exp_lt_exp.mpr ht.2
  exact ⟨hleft, hright⟩

/-- Inside one prime cell, Suzuki's arithmetic contribution is a fixed
finite sum.  In particular, threshold points need no exceptional case. -/
theorem suzukiPsiPrimeContribution_eq_fixed_sum_on_cell
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ SuzukiPrimeCell n) :
    suzukiPsiPrimeContribution t =
      ∑ k ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (t - Real.log k) := by
  simp only [suzukiPsiPrimeContribution,
    natFloor_exp_eq_of_mem_suzukiPrimeCell hn ht]

/-! ## Kernel-checkable candidate certificates -/

/-- A machine-generated affine candidate becomes a certificate only after
the two proof fields below are filled by Lean.  All serialized parameters are
rational; floating-point Explorer output cannot inhabit this structure. -/
structure SuzukiCellLowerBoundCertificate where
  omega : ℚ
  left : ℚ
  right : ℚ
  primeCell : ℕ
  slope : ℚ
  intercept : ℚ
  interval_nonempty : (left : ℝ) ≤ (right : ℝ)
  interval_mem_primeCell : ∀ t : ℝ,
    (left : ℝ) ≤ t → t ≤ (right : ℝ) → t ∈ SuzukiPrimeCell primeCell
  lowerBound_nonnegative : ∀ t : ℝ,
    (left : ℝ) ≤ t → t ≤ (right : ℝ) →
      0 ≤ (slope : ℝ) * t + (intercept : ℝ)
  lowerBound_le_shiftedPsi : ∀ t : ℝ,
    (left : ℝ) ≤ t → t ≤ (right : ℝ) →
      (slope : ℝ) * t + (intercept : ℝ) ≤
        suzukiPsiShifted (omega : ℝ) t

theorem SuzukiCellLowerBoundCertificate.shiftedPsi_nonnegative
    (c : SuzukiCellLowerBoundCertificate) {t : ℝ}
    (hlt : (c.left : ℝ) ≤ t) (htr : t ≤ (c.right : ℝ)) :
    0 ≤ suzukiPsiShifted (c.omega : ℝ) t :=
  (c.lowerBound_nonnegative t hlt htr).trans
    (c.lowerBound_le_shiftedPsi t hlt htr)

/-- The existing symbolic local-positivity proof yields a nontrivial
rational-radius, zero-affine certificate.  This is the first end-to-end
Explorer certificate smoke test; its radius is existential rather than
numerically optimized. -/
theorem exists_firstSuzukiCellLowerBoundCertificate :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < Real.log 2 ∧
      ∃ c : SuzukiCellLowerBoundCertificate,
        c.omega = 0 ∧ c.left = 0 ∧ c.right = q ∧
          c.primeCell = 1 ∧ c.slope = 0 ∧ c.intercept = 0 := by
  rcases exists_suzukiPsi_nonnegativeOn with ⟨a, ha, hnonneg⟩
  have hmin : 0 < min a (Real.log 2) :=
    lt_min ha (Real.log_pos (by norm_num))
  rcases exists_rat_btwn hmin with ⟨q, hq0, hqmin⟩
  have hqa : (q : ℝ) < a := hqmin.trans_le (min_le_left _ _)
  have hqlog : (q : ℝ) < Real.log 2 :=
    hqmin.trans_le (min_le_right _ _)
  let c : SuzukiCellLowerBoundCertificate :=
    { omega := 0
      left := 0
      right := q
      primeCell := 1
      slope := 0
      intercept := 0
      interval_nonempty := by exact_mod_cast hq0.le
      interval_mem_primeCell := by
        intro t ht0 htq
        simp only [SuzukiPrimeCell, mem_Ico]
        constructor
        · simpa using ht0
        · convert htq.trans_lt hqlog using 1 <;> norm_num
      lowerBound_nonnegative := by simp
      lowerBound_le_shiftedPsi := by
        intro t ht0 htq
        simp only [Rat.cast_zero, zero_mul, zero_add,
          suzukiPsiShifted_zero_parameter]
        apply hnonneg t
        have ht0' : 0 ≤ t := by simpa using ht0
        rw [abs_of_nonneg ht0']
        exact htq.trans_lt hqa |>.le }
  refine ⟨q, ?_, hqlog, c, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact_mod_cast hq0

theorem exists_suzukiPsi_nonnegative_on_firstCertifiedInterval :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < Real.log 2 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ (q : ℝ) → 0 ≤ suzukiPsi t := by
  rcases exists_firstSuzukiCellLowerBoundCertificate with
    ⟨q, hq0, hqlog, c, hcω, hcl, hcr, _, _, _⟩
  refine ⟨q, hq0, hqlog, ?_⟩
  intro t ht0 htq
  have hcert := c.shiftedPsi_nonnegative
    (t := t) (by simpa [hcl] using ht0) (by simpa [hcr] using htq)
  simpa [hcω] using hcert

/-- A tail certificate remains the genuinely global component that finite
cell checking cannot supply. -/
def SuzukiPsiTailCertificate : Prop :=
  ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ suzukiPsi t

end RHGarden
