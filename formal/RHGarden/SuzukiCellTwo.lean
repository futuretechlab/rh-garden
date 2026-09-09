import RHGarden.SuzukiConvexity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

open Set
open scoped BigOperators

namespace RHGarden

/-! ## The second Suzuki prime cell -/

/-- On the second prime cell the only nonzero Mangoldt ramp is the one at
`2`.  The possible term at the right endpoint `3` is absent here because
the cell is half-open. -/
theorem suzukiPsiPrimeContribution_cell_two
    {t : ℝ} (ht2 : Real.log 2 ≤ t) (ht3 : t < Real.log 3) :
    suzukiPsiPrimeContribution t =
      Real.log 2 / Real.sqrt 2 * (t - Real.log 2) := by
  have ht3' : t < Real.log ((2 : ℝ) + 1) := by
    convert ht3 using 1 <;> norm_num
  rw [suzukiPsiPrimeContribution_eq_fixed_sum_on_cell (n := 2) (by norm_num)
    ⟨ht2, ht3'⟩]
  have hIoc : Finset.Ioc 0 2 = {1, 2} := by decide
  rw [hIoc]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- The exact prime-side formula on `[log 2, log 3)`, with its finite sum
fully evaluated. -/
theorem suzukiPsi_eq_archimedean_sub_twoRamp
    {t : ℝ} (ht2 : Real.log 2 ≤ t) (ht3 : t < Real.log 3) :
    suzukiPsi t = suzukiPsiArchimedean t -
      Real.log 2 / Real.sqrt 2 * (t - Real.log 2) := by
  have ht0 : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht2
  rw [suzukiPsi_eq_primeSide, suzukiPsiPrimeSide, abs_of_pos ht0,
    suzukiPsiPrimeSideNonneg, suzukiPsiPrimeContribution_cell_two ht2 ht3]

/-- The exact first derivative on the open second prime cell. -/
theorem deriv_suzukiPsi_cell_two
    {t : ℝ} (ht2 : Real.log 2 < t) (ht3 : t < Real.log 3) :
    deriv suzukiPsi t =
      suzukiPsiPrimeFreeDerivative t - Real.log 2 / Real.sqrt 2 := by
  have ht3' : t < Real.log ((2 : ℝ) + 1) := by
    convert ht3 using 1 <;> norm_num
  have h := hasDerivAt_suzukiPsi_on_primeCell (n := 2) (by norm_num)
    (t := t) ⟨ht2, ht3'⟩
  rw [h.deriv]
  congr 1
  unfold suzukiPrimeCellSlope
  have hIoc : Finset.Ioc 0 2 = {1, 2} := by decide
  rw [hIoc]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-! ## Exact and rational constant control -/

/-- The classical exact quarter-value of the digamma function, derived from
the pinned Gamma reflection and duplication formulae. -/
theorem digamma_one_fourth :
    Complex.digamma (1 / 4 : ℂ) =
      -(Real.eulerMascheroniConstant : ℂ) - (Real.pi : ℂ) / 2 -
        3 * Complex.log 2 := by
  let q : ℂ := 1 / 4
  have hqnp : ∀ n : ℕ, q ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    dsimp [q] at hr
    norm_num at hr
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have honenp : ∀ n : ℕ, 1 - q ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    dsimp [q] at hr
    norm_num at hr
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hthreenp : ∀ n : ℕ, q + 1 / 2 ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    dsimp [q] at hr
    norm_num at hr
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hhalfnp : ∀ n : ℕ, 2 * q ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    dsimp [q] at hr
    norm_num at hr
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hqGamma : Complex.Gamma q ≠ 0 := Complex.Gamma_ne_zero hqnp
  have honeGamma : Complex.Gamma (1 - q) ≠ 0 := Complex.Gamma_ne_zero honenp
  have hthreeGamma : Complex.Gamma (q + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero hthreenp
  have hhalfGamma : Complex.Gamma (2 * q) ≠ 0 := Complex.Gamma_ne_zero hhalfnp
  have hdq : DifferentiableAt ℂ Complex.Gamma q :=
    Complex.differentiableAt_Gamma q hqnp
  have hdone : DifferentiableAt ℂ Complex.Gamma (1 - q) :=
    Complex.differentiableAt_Gamma _ honenp
  have hdthree : DifferentiableAt ℂ Complex.Gamma (q + 1 / 2) :=
    Complex.differentiableAt_Gamma _ hthreenp
  have hdhalf : DifferentiableAt ℂ Complex.Gamma (2 * q) :=
    Complex.differentiableAt_Gamma _ hhalfnp
  have hreflect :
      Complex.digamma q - Complex.digamma (1 - q) = -(Real.pi : ℂ) := by
    have heq : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
        fun z => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by
      funext z
      exact Complex.Gamma_mul_Gamma_one_sub z
    have hld := congrArg (fun F : ℂ → ℂ => logDeriv F q) heq
    have hleft : logDeriv
        (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) q =
        Complex.digamma q - Complex.digamma (1 - q) := by
      calc
        _ = logDeriv Complex.Gamma q +
              logDeriv (fun z : ℂ => Complex.Gamma (1 - z)) q :=
            logDeriv_mul q hqGamma honeGamma hdq
              (hdone.comp q (by fun_prop))
        _ = Complex.digamma q - Complex.digamma (1 - q) := by
          rw [show (fun z : ℂ => Complex.Gamma (1 - z)) =
                Complex.Gamma ∘ fun z : ℂ => 1 - z by rfl,
              logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => 1 - z)
                hdone (by fun_prop)]
          simp [Complex.digamma_def]
          ring
    have hright : logDeriv
        (fun z : ℂ => (Real.pi : ℂ) /
          Complex.sin ((Real.pi : ℂ) * z)) q = -(Real.pi : ℂ) := by
      have hsin : Complex.sin ((Real.pi : ℂ) * q) ≠ 0 := by
        dsimp [q]
        rw [show (Real.pi : ℂ) * (1 / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_sin, Real.sin_pi_div_four]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      have hcot : Complex.cot ((Real.pi : ℂ) * q) = 1 := by
        rw [Complex.cot]
        have harg : (Real.pi : ℂ) * q = ((Real.pi / 4 : ℝ) : ℂ) := by
          dsimp [q]
          push_cast
          ring
        rw [harg, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
          Real.sin_pi_div_four, Real.cos_pi_div_four]
        field_simp
      rw [logDeriv_div q (by exact_mod_cast Real.pi_ne_zero) hsin
        (by fun_prop) (by fun_prop)]
      simp only [logDeriv_const, Pi.zero_apply, zero_sub]
      rw [show (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) =
            Complex.sin ∘ fun z : ℂ => (Real.pi : ℂ) * z by rfl,
        logDeriv_comp (f := Complex.sin)
          (g := fun z : ℂ => (Real.pi : ℂ) * z)
          Complex.differentiableAt_sin (by fun_prop)]
      rw [Complex.logDeriv_sin]
      have hlin : deriv (fun z : ℂ => (Real.pi : ℂ) * z) q =
          (Real.pi : ℂ) := by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id q).const_mul (Real.pi : ℂ)).deriv
      rw [hlin]
      rw [hcot]
      simp
    rw [hleft, hright] at hld
    exact hld
  have hduplicate :
      Complex.digamma q + Complex.digamma (q + 1 / 2) =
        2 * Complex.digamma (2 * q) - 2 * Complex.log 2 := by
    have heq :
        (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) =
          fun z => Complex.Gamma (2 * z) *
            (2 : ℂ) ^ (1 - 2 * z) * (Real.sqrt Real.pi : ℂ) := by
      funext z
      exact Complex.Gamma_mul_Gamma_add_half z
    have hld := congrArg (fun F : ℂ → ℂ => logDeriv F q) heq
    have hleft : logDeriv
        (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) q =
        Complex.digamma q + Complex.digamma (q + 1 / 2) := by
      calc
        _ = logDeriv Complex.Gamma q +
              logDeriv (fun z : ℂ => Complex.Gamma (z + 1 / 2)) q :=
            logDeriv_mul q hqGamma hthreeGamma hdq
              (hdthree.comp q (by fun_prop))
        _ = Complex.digamma q + Complex.digamma (q + 1 / 2) := by
          rw [show (fun z : ℂ => Complex.Gamma (z + 1 / 2)) =
                Complex.Gamma ∘ fun z : ℂ => z + 1 / 2 by rfl,
              logDeriv_comp (f := Complex.Gamma)
                (g := fun z : ℂ => z + 1 / 2) hdthree (by fun_prop)]
          simp [Complex.digamma_def]
    have hright : logDeriv
        (fun z : ℂ => Complex.Gamma (2 * z) *
          (2 : ℂ) ^ (1 - 2 * z) * (Real.sqrt Real.pi : ℂ)) q =
        2 * Complex.digamma (2 * q) - 2 * Complex.log 2 := by
      have hpow_ne : (2 : ℂ) ^ (1 - 2 * q) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
      have hsqrt_ne : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
      have hGdiff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (2 * z)) q :=
        hdhalf.comp q (by fun_prop)
      have hPdiff : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) q :=
        by fun_prop
      calc
        _ = logDeriv (fun z : ℂ => Complex.Gamma (2 * z) *
              (2 : ℂ) ^ (1 - 2 * z)) q +
              logDeriv (fun _ : ℂ => (Real.sqrt Real.pi : ℂ)) q :=
            logDeriv_mul q (mul_ne_zero hhalfGamma hpow_ne) hsqrt_ne
              (hGdiff.mul hPdiff) (by fun_prop)
        _ = logDeriv (fun z : ℂ => Complex.Gamma (2 * z)) q +
              logDeriv (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) q := by
            rw [logDeriv_mul q hhalfGamma hpow_ne hGdiff hPdiff]
            simp
        _ = 2 * Complex.digamma (2 * q) - 2 * Complex.log 2 := by
          rw [show (fun z : ℂ => Complex.Gamma (2 * z)) =
                Complex.Gamma ∘ fun z : ℂ => 2 * z by rfl,
              logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => 2 * z)
                hdhalf (by fun_prop)]
          have hlin2 : deriv (fun z : ℂ => 2 * z) q = 2 :=
            by simpa only [id_eq, mul_one] using
              ((hasDerivAt_id q).const_mul (2 : ℂ)).deriv
          rw [hlin2]
          have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - 2 * z) q := by
            fun_prop
          have hpderiv : deriv (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) q =
              Complex.log 2 * deriv (fun z : ℂ => 1 - 2 * z) q *
                (2 : ℂ) ^ (1 - 2 * q) :=
            Complex.deriv_const_cpow hinner (2 : ℂ)
          have hinner' : deriv (fun z : ℂ => 1 - 2 * z) q = -2 := by
            have h := ((hasDerivAt_id q).const_mul (2 : ℂ)).const_sub 1
            simpa only [id_eq, mul_one] using h.deriv
          have hPlog : logDeriv (fun z : ℂ => (2 : ℂ) ^ (1 - 2 * z)) q =
              -2 * Complex.log 2 := by
            rw [logDeriv_apply, hpderiv, hinner']
            field_simp [hpow_ne]
          rw [hPlog, Complex.digamma_def, logDeriv_apply]
          ring
    rw [hleft, hright] at hld
    exact hld
  have hthree : Complex.digamma (q + 1 / 2) =
      Complex.digamma q + (Real.pi : ℂ) := by
    have hqrel : 1 - q = q + 1 / 2 := by norm_num [q]
    rw [hqrel] at hreflect
    linear_combination -hreflect
  rw [hthree] at hduplicate
  have hhalf : Complex.digamma (2 * q) =
      -2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) := by
    have h2q : 2 * q = (1 / 2 : ℂ) := by norm_num [q]
    rw [h2q]
    exact Complex.digamma_one_half
  rw [hhalf] at hduplicate
  linear_combination hduplicate / 2

/-- Real form of the exact quarter-digamma value. -/
theorem re_digamma_one_fourth :
    (Complex.digamma (1 / 4 : ℂ)).re =
      -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
  have h := congrArg Complex.re digamma_one_fourth
  have hlog : (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_re,
    Complex.mul_re] at h
  rw [hlog] at h
  norm_num at h
  convert h using 1 <;> ring

/-- A small exact exponential interval used by the cell-two certificate. -/
theorem exp_nine_twentieth_mem_Ioo :
    (156831 : ℝ) / 100000 < Real.exp (9 / 20) ∧
      Real.exp (9 / 20) < (156832 : ℝ) / 100000 := by
  have h := Real.exp_bound (x := (9 / 20 : ℝ)) (n := 10)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, abs_le] at h ⊢
  constructor <;> linarith

/-- The reciprocal exponential interval, proved independently from the same
Taylor remainder theorem. -/
theorem exp_neg_nine_twentieth_mem_Ioo :
    (63762 : ℝ) / 100000 < Real.exp (-9 / 20) ∧
      Real.exp (-9 / 20) < (319 : ℝ) / 500 := by
  have h := Real.exp_bound (x := (-9 / 20 : ℝ)) (n := 10)
    (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, abs_le] at h ⊢
  constructor <;> linarith

theorem eulerMascheroniConstant_lt_fifty_nine_hundredths :
    Real.eulerMascheroniConstant < (59 : ℝ) / 100 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 50
  rw [Real.eulerMascheroniSeq'] at h
  norm_num at h
  rw [show Real.log 50 = Real.log 2 + 2 * Real.log 5 by
    rw [show (50 : ℝ) = 2 * 5 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring] at h
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

theorem one_lt_log_pi : (1 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  exact Real.exp_one_lt_three.trans Real.pi_gt_three

theorem log_pi_lt_twenty_three_twentieths :
    Real.log Real.pi < (23 : ℝ) / 20 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  rw [show (23 : ℝ) / 20 = 1 + 3 / 20 by norm_num, Real.exp_add]
  have h := Real.exp_bound (x := (3 / 20 : ℝ)) (n := 8)
    (by norm_num) (by norm_num)
  have he : (1161834 : ℝ) / 1000000 < Real.exp (3 / 20) := by
    norm_num [Finset.sum_range_succ, abs_le] at h ⊢
    linarith
  calc
    Real.pi < (31416 : ℝ) / 10000 := by
      convert Real.pi_lt_d4 using 1 <;> norm_num
    _ < (27182818283 : ℝ) / 10000000000 *
        ((1161834 : ℝ) / 1000000) := by norm_num
    _ < Real.exp 1 * Real.exp (3 / 20) := by
      have he1 : (27182818283 : ℝ) / 10000000000 < Real.exp 1 := by
        convert Real.exp_one_gt_d9 using 1 <;> norm_num
      exact mul_lt_mul he1 he.le (by norm_num) (Real.exp_pos _).le

theorem sqrt_two_mem_Ioo_rational :
    (7071 : ℝ) / 5000 < Real.sqrt 2 ∧
      Real.sqrt 2 < (14143 : ℝ) / 10000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

/-- Rational enclosure for the only constant combination appearing in the
cell value and derivative. -/
theorem digammaLogPi_mem_Ioo_rational :
    (-5391 : ℝ) / 1000 <
        (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi ∧
      (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi <
        (-103 : ℝ) / 20 := by
  rw [re_digamma_one_fourth]
  constructor
  · have hpi : Real.pi < (31416 : ℝ) / 10000 := by
      convert Real.pi_lt_d4 using 1 <;> norm_num
    have hlog2 : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
      convert Real.log_two_lt_d9 using 1 <;> norm_num
    linarith [eulerMascheroniConstant_lt_fifty_nine_hundredths,
      log_pi_lt_twenty_three_twentieths]
  · have hpi : (31415 : ℝ) / 10000 < Real.pi := by
      convert Real.pi_gt_d4 using 1 <;> norm_num
    have hlog2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
      convert Real.log_two_gt_d9 using 1 <;> norm_num
    linarith [Real.one_half_lt_eulerMascheroniConstant, one_lt_log_pi]

/-- The archimedean expression written as its positive quarter-lattice
series. -/
theorem suzukiPsiArchimedean_eq_quarter_tsum {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsiArchimedean t =
      4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
        t / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        1 / 4 * (∑' n : ℕ,
          (1 / ((n : ℝ) + 1 / 4) ^ 2) *
            (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t))) := by
  unfold suzukiPsiArchimedean
  rw [tsum_quarter_reciprocal_sq_one_sub_exp ht]

/-- A finite, exact 20-term certificate for the positive quarter-lattice
piece at the rational sample `9/10`. -/
theorem quarter_value_tsum_at_nine_tenths_gt :
    (6867 : ℝ) / 1000 <
      ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10))) := by
  let f : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1 / 4) ^ 2) *
    (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)))
  have hsbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    rw [show (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) =
        fun n : ℕ => 1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ) by
      funext n
      simp [sq_abs]]
    exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)
  have hs : Summable f := by
    exact Summable.of_nonneg_of_le
      (fun n => by
        dsimp [f]
        have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        positivity)
      (fun n => by
        dsimp [f]
        have he0 : 0 ≤ Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)) :=
          Real.exp_nonneg _
        have hc : 0 ≤ 1 / ((n : ℝ) + 1 / 4) ^ 2 := by positivity
        nlinarith)
      hsbase
  have hpartial : ∑ n ∈ Finset.range 20, f n ≤ ∑' n, f n :=
    hs.sum_le_tsum (Finset.range 20) (fun n _ => by
      dsimp [f]
      have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      positivity)
  have hr := exp_neg_nine_twentieth_mem_Ioo.2
  have hterm : ∀ n ∈ Finset.range 20,
      (1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - ((319 : ℝ) / 500) ^ (4 * n + 1)) ≤ f n := by
    intro n _
    have hexp : Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)) =
        Real.exp (-9 / 20) ^ (4 * n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    dsimp [f]
    rw [hexp]
    have hp := pow_le_pow_left₀ (Real.exp_nonneg (-9 / 20)) hr.le (4 * n + 1)
    have hc : 0 ≤ 1 / ((n : ℝ) + 1 / 4) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hc
  have hsum := Finset.sum_le_sum hterm
  calc
    (6867 : ℝ) / 1000 < ∑ n ∈ Finset.range 20,
        (1 / ((n : ℝ) + 1 / 4) ^ 2) *
          (1 - ((319 : ℝ) / 500) ^ (4 * n + 1)) := by norm_num
    _ ≤ ∑ n ∈ Finset.range 20, f n := hsum
    _ ≤ ∑' n, f n := hpartial

theorem cell_two_ramp_at_nine_tenths_lt :
    Real.log 2 / Real.sqrt 2 * ((9 : ℝ) / 10 - Real.log 2) <
      (51 : ℝ) / 500 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hslo := sqrt_two_mem_Ioo_rational.1
  have hloglo : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
    convert Real.log_two_gt_d9 using 1 <;> norm_num
  have hloghi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    convert Real.log_two_lt_d9 using 1 <;> norm_num
  have hratio : Real.log 2 / Real.sqrt 2 < (491 : ℝ) / 1000 := by
    rw [div_lt_iff₀ hspos]
    nlinarith
  have hdiffpos : 0 < (9 : ℝ) / 10 - Real.log 2 := by linarith
  have hdiff : (9 : ℝ) / 10 - Real.log 2 < (207 : ℝ) / 1000 := by
    linarith
  calc
    _ < (491 : ℝ) / 1000 * ((9 : ℝ) / 10 - Real.log 2) :=
      mul_lt_mul_of_pos_right hratio hdiffpos
    _ < (491 : ℝ) / 1000 * ((207 : ℝ) / 1000) :=
      mul_lt_mul_of_pos_left hdiff (by norm_num)
    _ < (51 : ℝ) / 500 := by norm_num

/-- Certified value margin at the rational sample selected by the Explorer. -/
theorem suzukiPsi_nine_tenths_gt_one_hundredth :
    (1 : ℝ) / 100 < suzukiPsi (9 / 10) := by
  have ht2 : Real.log 2 ≤ (9 : ℝ) / 10 := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have ht3 : (9 : ℝ) / 10 < Real.log 3 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  rw [suzukiPsi_eq_archimedean_sub_twoRamp ht2 ht3,
    suzukiPsiArchimedean_eq_quarter_tsum (by norm_num)]
  have hE := exp_nine_twentieth_mem_Ioo.1
  have hR := exp_neg_nine_twentieth_mem_Ioo.1
  have hD := digammaLogPi_mem_Ioo_rational.1
  have hS := quarter_value_tsum_at_nine_tenths_gt
  have hRamp := cell_two_ramp_at_nine_tenths_lt
  norm_num at hE hR hD hS ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- The positive quarter-lattice derivative series at `9/10` has a compact
rational enclosure.  The zeroth term supplies the lower bound; a geometric
majorant controls every remaining term. -/
theorem quarter_derivative_tsum_at_nine_tenths_mem_Ioo :
    (51 : ℝ) / 10 <
        ∑' n : ℕ, (2 / ((n : ℝ) + 1 / 4)) *
          Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10)) ∧
      (∑' n : ℕ, (2 / ((n : ℝ) + 1 / 4)) *
          Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10))) <
        (531 : ℝ) / 100 := by
  let r : ℝ := Real.exp (-9 / 20)
  let f : ℕ → ℝ := fun n => (2 / ((n : ℝ) + 1 / 4)) *
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * (9 / 10))
  let g : ℕ → ℝ := fun n => (8 / 5 : ℝ) * r ^ 5 * (r ^ 4) ^ n
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr := exp_neg_nine_twentieth_mem_Ioo
  have hr1 : r < 1 := by
    dsimp [r]
    linarith [hr.2]
  have hq : r ^ 4 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hg : Summable g := by
    exact ((summable_geometric_of_norm_lt_one
      (by simpa [abs_of_nonneg hr0] using hq)).mul_left
        ((8 / 5 : ℝ) * r ^ 5))
  have htail : ∀ n : ℕ, f (n + 1) ≤ g n := by
    intro n
    have hexp :
        Real.exp (-2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) * (9 / 10)) =
          r ^ (4 * n + 5) := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hcoef :
        2 / (((n + 1 : ℕ) : ℝ) + 1 / 4) ≤ (8 / 5 : ℝ) := by
      have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 / 4 := by positivity
      rw [div_le_iff₀ hd]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      nlinarith
    dsimp [f, g]
    rw [hexp, show r ^ (4 * n + 5) = r ^ 5 * (r ^ 4) ^ n by
      rw [show 4 * n + 5 = 5 + 4 * n by omega, pow_add, pow_mul]]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (pow_nonneg hr0 5) (pow_nonneg (pow_nonneg hr0 4) n))
  have hfTail : Summable (fun n => f (n + 1)) :=
    Summable.of_nonneg_of_le
      (fun n => by
        dsimp [f]
        positivity)
      htail hg
  have hf : Summable f :=
    (summable_nat_add_iff (f := f) 1).mp (by simpa using hfTail)
  have htailSum : (∑' n, f (n + 1)) ≤ ∑' n, g n :=
    hfTail.tsum_le_tsum htail hg
  have hgSum :
      (∑' n, g n) = (8 / 5 : ℝ) * r ^ 5 * (1 - r ^ 4)⁻¹ := by
    dsimp [g]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one
      (by simpa [abs_of_nonneg hr0] using hq)]
  have hr4 : r ^ 4 < (1 : ℝ) / 6 := by
    have hp := pow_le_pow_left₀ hr0 hr.2.le 4
    norm_num at hp ⊢
    linarith
  have hr5 : r ^ 5 < (53 : ℝ) / 500 := by
    have hp := pow_le_pow_left₀ hr0 hr.2.le 5
    norm_num at hp ⊢
    linarith
  have hgeom :
      (8 / 5 : ℝ) * r ^ 5 * (1 - r ^ 4)⁻¹ < (51 : ℝ) / 250 := by
    have hden : (0 : ℝ) < 1 - r ^ 4 := by linarith
    rw [show (8 / 5 : ℝ) * r ^ 5 * (1 - r ^ 4)⁻¹ =
        ((8 / 5 : ℝ) * r ^ 5) / (1 - r ^ 4) by
          simp only [div_eq_mul_inv],
      div_lt_iff₀ hden]
    nlinarith
  constructor
  · rw [hf.tsum_eq_zero_add]
    have htailNonneg : 0 ≤ ∑' n, f (n + 1) := tsum_nonneg (fun n => by
      dsimp [f]
      positivity)
    have hf0 : f 0 = 8 * r := by
      dsimp [f, r]
      ring
    rw [hf0]
    have hrlo : (63762 : ℝ) / 100000 < r := by
      exact hr.1
    nlinarith
  · rw [hf.tsum_eq_zero_add]
    have hf0 : f 0 = 8 * r := by
      dsimp [f, r]
      ring
    rw [hf0]
    have hrhi : r < (319 : ℝ) / 500 := by
      exact hr.2
    calc
      8 * r + ∑' n, f (n + 1) ≤ 8 * r + ∑' n, g n :=
        add_le_add_right htailSum _
      _ = 8 * r + (8 / 5 : ℝ) * r ^ 5 * (1 - r ^ 4)⁻¹ := by rw [hgSum]
      _ < (531 : ℝ) / 100 := by nlinarith [hgeom]

/-- The derivative at the rational sample is small enough for the
strong-convexity certificate. -/
theorem abs_deriv_suzukiPsi_nine_tenths_le :
    |deriv suzukiPsi (9 / 10)| ≤ (13 : ℝ) / 100 := by
  have ht2 : Real.log 2 < (9 : ℝ) / 10 := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have ht3 : (9 : ℝ) / 10 < Real.log 3 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  rw [deriv_suzukiPsi_cell_two ht2 ht3,
    suzukiPsiPrimeFreeDerivative_eq_quarter_tsum (by norm_num)]
  have hE := exp_nine_twentieth_mem_Ioo
  have hR := exp_neg_nine_twentieth_mem_Ioo
  have hD := digammaLogPi_mem_Ioo_rational
  have hS := quarter_derivative_tsum_at_nine_tenths_mem_Ioo
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hslo := sqrt_two_mem_Ioo_rational.1
  have hshi := sqrt_two_mem_Ioo_rational.2
  have hloglo : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
    convert Real.log_two_gt_d9 using 1 <;> norm_num
  have hloghi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    convert Real.log_two_lt_d9 using 1 <;> norm_num
  have hslopeLo : (49 : ℝ) / 100 < Real.log 2 / Real.sqrt 2 := by
    rw [lt_div_iff₀ hspos]
    nlinarith
  have hslopeHi : Real.log 2 / Real.sqrt 2 < (491 : ℝ) / 1000 := by
    rw [div_lt_iff₀ hspos]
    nlinarith
  rw [abs_le]
  constructor <;> norm_num at hE hR hD hS ⊢ <;> nlinarith

/-! ## The first certified unshifted prime cell -/

/-- An exact strong-convexity certificate for the whole second prime cell
of the unshifted Suzuki function.  Its rational margin is
`1/100 - (13/100)^2/2 = 31/20000`. -/
def suzukiCellTwoStrongConvexCertificate :
    SuzukiStrongConvexCellCertificate where
  omega := 0
  cell := 2
  sampleX := 9 / 10
  curvatureLower := 1
  valueLower := 1 / 100
  derivAbsUpper := 13 / 100
  cell_ge_two := by norm_num
  sample_mem := by
    constructor
    · have h := Real.log_two_lt_d9
      norm_num at h ⊢
      linarith
    · have h := Real.log_three_gt_d9
      norm_num at h ⊢
      linarith
  curvature_pos := by norm_num
  value_bound := by
    simpa using suzukiPsi_nine_tenths_gt_one_hundredth.le
  deriv_bound := by
    norm_num
    change |deriv (suzukiPsiShifted 0) (9 / 10)| ≤ (13 : ℝ) / 100
    have hzero : suzukiPsiShifted 0 = suzukiPsi := by
      funext t
      exact suzukiPsiShifted_zero_parameter t
    rw [hzero]
    exact abs_deriv_suzukiPsi_nine_tenths_le
  curvature_bound := by
    intro t ht
    norm_num
    change 1 ≤ deriv (deriv (suzukiPsiShifted 0)) t
    have hzero : suzukiPsiShifted 0 = suzukiPsi := by
      funext u
      exact suzukiPsiShifted_zero_parameter u
    rw [hzero]
    exact one_le_secondDeriv_suzukiPsi_on_primeCell
      (n := 2) (by norm_num) ht
  certificate_positive := by norm_num

/-- Unconditional strict positivity on the complete second prime cell of
the actual (`omega = 0`) RH-equivalent Suzuki function. -/
theorem suzukiPsi_pos_cell_two :
    ∀ t : ℝ, Real.log 2 ≤ t → t ≤ Real.log 3 → 0 < suzukiPsi t := by
  intro t ht2 ht3
  have h := suzukiCellTwoStrongConvexCertificate.positive_on_cell t
  have ht : t ∈ Icc (Real.log suzukiCellTwoStrongConvexCertificate.cell)
      (Real.log (suzukiCellTwoStrongConvexCertificate.cell + 1)) := by
    constructor
    · norm_num [suzukiCellTwoStrongConvexCertificate]
      exact ht2
    · norm_num [suzukiCellTwoStrongConvexCertificate]
      exact ht3
  have hpos := h ht
  norm_num [suzukiCellTwoStrongConvexCertificate] at hpos
  simpa only [suzukiPsiShifted_zero_parameter] using hpos

/-- Explicit metadata predicate for prime cells whose strict positivity has
been independently certified in Lean. -/
def SuzukiCertifiedPrimeCell (omega : ℚ) (cell : ℕ) : Prop :=
  ∀ t ∈ Icc (Real.log cell) (Real.log (cell + 1)),
    0 < suzukiPsiShifted (omega : ℝ) t

/-- Cell 2 at `omega=0` is the first certified prime cell of the actual
RH-equivalent Suzuki function. -/
theorem suzukiCertifiedPrimeCell_zero_two :
    SuzukiCertifiedPrimeCell 0 2 := by
  intro t ht
  have h := suzukiCellTwoStrongConvexCertificate.positive_on_cell t
  simpa [SuzukiCertifiedPrimeCell, suzukiCellTwoStrongConvexCertificate] using h ht

end RHGarden
