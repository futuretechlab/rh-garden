import RHGarden.SuzukiShiftedHerglotz
import RHGarden.SuzukiLocalPositive

noncomputable section

open Set MeasureTheory
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

/-! ## Exact cell-interior regularity -/

/-- The unshifted Suzuki function is differentiable away from the prime
thresholds.  On an open prime cell its arithmetic part is a fixed finite
affine sum. -/
theorem differentiableAt_suzukiPsi_primeCellInterior
    {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo (Real.log n) (Real.log (n + 1))) :
    DifferentiableAt ℝ suzukiPsi t := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have ht0 : 0 < t := lt_of_le_of_lt hlogn ht.1
  let F : ℝ → ℝ := fun y =>
    suzukiPsiArchimedean y -
      ∑ k ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (y - Real.log k)
  have hF : DifferentiableAt ℝ F t := by
    dsimp [F]
    apply (differentiableAt_suzukiPsiArchimedean_of_pos ht0).sub
    fun_prop
  apply hF.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2,
      eventually_gt_nhds ht0] with y hyn hyn' hy0
  rw [suzukiPsi_eq_primeSide, suzukiPsiPrimeSide, abs_of_pos hy0,
    suzukiPsiPrimeSideNonneg,
    suzukiPsiPrimeContribution_eq_fixed_sum_on_cell hn ⟨hyn.le, hyn'⟩]

/-- Cell-interior differentiability in set form, suitable for critical-point
and convexity certificates. -/
theorem differentiableOn_suzukiPsi_primeCellInterior
    (n : ℕ) (hn : 0 < n) :
    DifferentiableOn ℝ suzukiPsi
      (Set.Ioo (Real.log n) (Real.log (n + 1))) := by
  intro t ht
  exact (differentiableAt_suzukiPsi_primeCellInterior hn ht).differentiableWithinAt

/-- A Suzuki shift is differentiable at a positive point whenever its input
is continuous globally and differentiable there.  Rewriting the second
Volterra term as `t * J₀(t) - J₁(t)` keeps the proof one-dimensional. -/
theorem differentiableAt_SuzukiShift_of_pos
    (ω : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hft : DifferentiableAt ℝ f t) :
    DifferentiableAt ℝ (SuzukiShift ω f) t := by
  let h : ℝ → ℝ := fun u => Real.exp (-ω * u) * f u
  have hh : Continuous h := by
    dsimp [h]
    fun_prop
  have huh : Continuous (fun u : ℝ => u * h u) := by fun_prop
  let H₀ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, h u
  let H₁ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, u * h u
  have hH₀ : Differentiable ℝ H₀ :=
    intervalIntegral.differentiable_integral_of_continuous hh
  have hH₁ : Differentiable ℝ H₁ :=
    intervalIntegral.differentiable_integral_of_continuous huh
  let G : ℝ → ℝ := fun x =>
    Real.exp (-ω * x) * f x + 2 * ω * H₀ x +
      ω ^ 2 * (x * H₀ x - H₁ x)
  have hG : DifferentiableAt ℝ G t := by
    dsimp [G]
    fun_prop
  apply hG.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with x hx
  simp only [SuzukiShift, abs_of_pos hx]
  dsimp [G, H₀, H₁, h]
  congr 2
  have hx₀ : IntervalIntegrable
      (fun u : ℝ => x * (Real.exp (-ω * u) * f u)) volume 0 x :=
    (continuous_const.mul hh).intervalIntegrable 0 x
  have hx₁ : IntervalIntegrable
      (fun u : ℝ => u * (Real.exp (-ω * u) * f u)) volume 0 x :=
    huh.intervalIntegrable 0 x
  calc
    (∫ u in (0 : ℝ)..x, (x - u) * Real.exp (-ω * u) * f u) =
        ∫ u in (0 : ℝ)..x,
          x * (Real.exp (-ω * u) * f u) -
            u * (Real.exp (-ω * u) * f u) := by
          apply intervalIntegral.integral_congr
          intro u _
          ring
    _ = (∫ u in (0 : ℝ)..x, x * (Real.exp (-ω * u) * f u)) -
        ∫ u in (0 : ℝ)..x, u * (Real.exp (-ω * u) * f u) :=
      intervalIntegral.integral_sub hx₀ hx₁
    _ = x * (∫ u in (0 : ℝ)..x, Real.exp (-ω * u) * f u) -
        ∫ u in (0 : ℝ)..x, u * (Real.exp (-ω * u) * f u) := by
      rw [intervalIntegral.integral_const_mul]

/-- Every shifted Suzuki function is differentiable in the interior of a
prime cell. -/
theorem differentiableOn_suzukiPsiShifted_primeCellInterior
    (ω : ℝ) (n : ℕ) (hn : 0 < n) :
    DifferentiableOn ℝ (suzukiPsiShifted ω)
      (Set.Ioo (Real.log n) (Real.log (n + 1))) := by
  intro t ht
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  have ht0 : 0 < t := lt_of_le_of_lt
    (Real.log_nonneg (by exact_mod_cast hn1)) ht.1
  exact (differentiableAt_SuzukiShift_of_pos ω continuous_suzukiPsi ht0
    (differentiableAt_suzukiPsi_primeCellInterior hn ht)).differentiableWithinAt

/-! ## Exact minimum-bracket certificates -/

/-- A generic certificate verifier for a minimum bracket.  To bound a
continuous differentiable function on `[l,r]`, it is enough to certify that
it decreases up to `a`, has the desired bound throughout `[a,b]`, and
increases from `b` onward. -/
theorem lowerBound_on_Icc_of_deriv_signs
    {f : ℝ → ℝ} {l a b r L : ℝ}
    (hla : l < a) (hab : a ≤ b) (hbr : b < r)
    (hcont : ContinuousOn f (Set.Icc l r))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo l r))
    (hleft : ∀ x ∈ Set.Ioo l a, deriv f x ≤ 0)
    (hright : ∀ x ∈ Set.Ioo b r, 0 ≤ deriv f x)
    (hbracket : ∀ x ∈ Set.Icc a b, L ≤ f x) :
    ∀ x ∈ Set.Icc l r, L ≤ f x := by
  have hanti : AntitoneOn f (Set.Icc l a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc l a)
    · exact hcont.mono (Set.Icc_subset_Icc_right (hab.trans hbr.le))
    · rw [interior_Icc]
      intro x hx
      exact (hdiff x ⟨hx.1, hx.2.trans (hab.trans_lt hbr)⟩).mono
        (fun _ hy => ⟨hy.1, hy.2.trans (hab.trans_lt hbr)⟩)
    · rw [interior_Icc]
      exact hleft
  have hmono : MonotoneOn f (Set.Icc b r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b r)
    · exact hcont.mono (Set.Icc_subset_Icc_left (hla.le.trans hab))
    · rw [interior_Icc]
      intro x hx
      exact (hdiff x ⟨hla.trans_le (hab.trans hx.1.le), hx.2⟩).mono
        (fun _ hy => ⟨hla.trans_le (hab.trans hy.1.le), hy.2⟩)
    · rw [interior_Icc]
      exact hright
  intro x hx
  rcases le_total x a with hxa | hax
  · exact (hbracket a ⟨le_rfl, hab⟩).trans
      (hanti ⟨hx.1, hxa⟩ ⟨hla.le, le_rfl⟩ hxa)
  rcases le_total b x with hbx | hxb
  · exact (hbracket b ⟨hab, le_rfl⟩).trans
      (hmono ⟨le_rfl, hbx.trans hx.2⟩ ⟨hbx, hx.2⟩ hbx)
  · exact hbracket x ⟨hax, hxb⟩

/-- Convexity-oriented form of the minimum-bracket verifier.  Monotonicity
of the derivative (which can itself be certified from a nonnegative second
derivative) reduces the two flank obligations to signs at the bracket
endpoints. -/
theorem lowerBound_on_Icc_of_monotone_deriv
    {f : ℝ → ℝ} {l a b r L : ℝ}
    (hla : l < a) (hab : a ≤ b) (hbr : b < r)
    (hcont : ContinuousOn f (Set.Icc l r))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo l r))
    (hmono : MonotoneOn (deriv f) (Set.Ioo l r))
    (hda : deriv f a ≤ 0) (hdb : 0 ≤ deriv f b)
    (hbracket : ∀ x ∈ Set.Icc a b, L ≤ f x) :
    ∀ x ∈ Set.Icc l r, L ≤ f x := by
  apply lowerBound_on_Icc_of_deriv_signs hla hab hbr hcont hdiff
  · intro x hx
    exact (hmono ⟨hx.1, (hx.2.trans_le hab).trans hbr⟩
      ⟨hla, hab.trans_lt hbr⟩ hx.2.le).trans hda
  · intro x hx
    exact hdb.trans (hmono ⟨hla.trans_le hab, hbr⟩
      ⟨(hla.trans_le hab).trans hx.1, hx.2⟩ hx.1.le)
  · exact hbracket

/-- Rational metadata plus exact analytic obligations for certifying one
whole Suzuki prime cell.  Explorer output supplies candidate rationals; an
object of this type exists only after Lean proves every sign and bound. -/
structure SuzukiCellConvexCertificate where
  omega : ℚ
  primeCell : ℕ
  bracketLeft : ℚ
  bracketRight : ℚ
  lowerBound : ℚ
  primeCell_pos : 0 < primeCell
  bracket_inside :
    Real.log primeCell < (bracketLeft : ℝ) ∧
      (bracketLeft : ℝ) ≤ (bracketRight : ℝ) ∧
      (bracketRight : ℝ) < Real.log (primeCell + 1)
  deriv_nonpos_left : ∀ t : ℝ,
    t ∈ Set.Ioo (Real.log primeCell) (bracketLeft : ℝ) →
      deriv (suzukiPsiShifted (omega : ℝ)) t ≤ 0
  deriv_nonneg_right : ∀ t : ℝ,
    t ∈ Set.Ioo (bracketRight : ℝ) (Real.log (primeCell + 1)) →
      0 ≤ deriv (suzukiPsiShifted (omega : ℝ)) t
  lowerBound_on_bracket : ∀ t : ℝ,
    t ∈ Set.Icc (bracketLeft : ℝ) (bracketRight : ℝ) →
      (lowerBound : ℝ) ≤ suzukiPsiShifted (omega : ℝ) t
  lowerBound_nonnegative : (0 : ℝ) ≤ (lowerBound : ℝ)

/-- A completed convex/minimum-bracket certificate proves nonnegativity on
the entire closed prime cell, including both threshold endpoints. -/
theorem SuzukiCellConvexCertificate.shiftedPsi_nonnegative_on_cell
    (c : SuzukiCellConvexCertificate) :
    ∀ t : ℝ,
      t ∈ Set.Icc (Real.log c.primeCell) (Real.log (c.primeCell + 1)) →
      0 ≤ suzukiPsiShifted (c.omega : ℝ) t := by
  intro t ht
  apply c.lowerBound_nonnegative.trans
  apply lowerBound_on_Icc_of_deriv_signs
    c.bracket_inside.1 c.bracket_inside.2.1 c.bracket_inside.2.2
  · exact (continuous_suzukiPsiShifted (c.omega : ℝ)).continuousOn
  · exact differentiableOn_suzukiPsiShifted_primeCellInterior
      (c.omega : ℝ) c.primeCell c.primeCell_pos
  · exact c.deriv_nonpos_left
  · exact c.deriv_nonneg_right
  · exact c.lowerBound_on_bracket
  · exact ht

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
