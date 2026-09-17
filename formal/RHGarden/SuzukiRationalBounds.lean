import RHGarden.SuzukiConcreteEvents
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Small rational enclosures needed for finite Suzuki certificates. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RHGarden
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- A specialized rational-log checker from Mathlib's atanh series, with
its proved remainder. Rational inequalities are discharged by the kernel. -/
theorem log_rational_bounds {x l h : ℝ} (hx : 1 ≤ x) (n : ℕ)
    (hl : l ≤ 2 * ∑ i ∈ Finset.range n,
      ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1))
    (hh : 2 * ((∑ i ∈ Finset.range n,
      ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      ((x - 1) / (x + 1)) ^ (2 * n + 1) /
        (1 - ((x - 1) / (x + 1)) ^ 2)) ≤ h) :
    l ≤ Real.log x ∧ Real.log x ≤ h := by
  have hd : 0 < x + 1 := by linarith
  have hz : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) hd.le
  have ho : (x - 1) / (x + 1) < 1 := (div_lt_one hd).mpr (by linarith)
  have he : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hz ho n
  have hhi := Real.log_div_le_sum_range_add hz ho n
  rw [he] at hlo hhi
  constructor <;> linarith

theorem log_pi_mem_tight : (114472 : ℝ) / 100000 ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (114474 : ℝ) / 100000 := by
  have hlow := log_rational_bounds (x := (314159 : ℝ) / 100000)
    (l := 114472 / 100000) (h := 114474 / 100000) (by norm_num) 16
    (by norm_num) (by norm_num)
  have hhigh := log_rational_bounds (x := (314160 : ℝ) / 100000)
    (l := 114472 / 100000) (h := 114474 / 100000) (by norm_num) 16
    (by norm_num) (by norm_num)
  constructor
  · exact hlow.1.trans (Real.log_le_log (by norm_num) (by
      have h := Real.pi_gt_d6
      norm_num at h ⊢
      linarith))
  · exact (Real.log_le_log Real.pi_pos (by
      have h := Real.pi_lt_d6
      norm_num at h ⊢
      linarith)).trans hhigh.2

theorem eulerMascheroni_mem_tight : (57526 : ℝ) / 100000 ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ (57917 : ℝ) / 100000 := by
  have hl := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 255
  have hh := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  have he : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    Nat.cast_ofNat, show ¬ (256 : ℕ) = 0 by decide, if_false,
    show (255 : ℝ) + 1 = 256 by norm_num] at hl hh
  rw [he] at hl hh
  norm_num at hl hh
  have h2l := Real.log_two_gt_d9
  have h2h := Real.log_two_lt_d9
  norm_num at h2l h2h
  constructor <;> linarith

theorem digammaLogPi_mem_tight :
    (-53743 : ℝ) / 10000 ≤ (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi ∧
    (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi ≤ (-53700 : ℝ) / 10000 := by
  rw [re_digamma_one_fourth]
  have hπlo := Real.pi_gt_d6
  have hπhi := Real.pi_lt_d6
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have he := eulerMascheroni_mem_tight
  have hl := log_pi_mem_tight
  norm_num at hπlo hπhi h2lo h2hi
  constructor <;> linarith

def suzukiQuarterCoeff (n : ℕ) : ℝ := 4 / (4 * n + 1) ^ 2

theorem summable_suzukiQuarterCoeff : Summable suzukiQuarterCoeff := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    simpa [sq_abs] using (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)
  apply (h.mul_left (1 / 4)).congr
  intro n
  unfold suzukiQuarterCoeff
  field_simp <;> ring

theorem suzukiQuarterTotal_bounds :
    (42954 : ℝ) / 10000 ≤ ∑' n, suzukiQuarterCoeff n ∧
    (∑' n, suzukiQuarterCoeff n) ≤ (429934 : ℝ) / 100000 := by
  constructor
  · have h := summable_suzukiQuarterCoeff.sum_le_tsum (Finset.range 64)
      (fun n _ => by unfold suzukiQuarterCoeff; positivity)
    have hn : (42954 : ℝ) / 10000 ≤ ∑ n ∈ Finset.range 64, suzukiQuarterCoeff n := by
      norm_num [suzukiQuarterCoeff]
    exact hn.trans h
  · have hstep (n : ℕ) : suzukiQuarterCoeff (n + 32) ≤
        1 / (4 * (n + 32 : ℕ) - 1 : ℝ) - 1 / (4 * (n + 33 : ℕ) - 1 : ℝ) := by
      unfold suzukiQuarterCoeff
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 0 < 4 * ((n : ℝ) + 32) - 1 := by linarith
      have h2 : 0 < 4 * ((n : ℝ) + 33) - 1 := by linarith
      have h3 : 0 < (4 * ((n : ℝ) + 32) + 1) ^ 2 := by positivity
      field_simp
      nlinarith
    have hfinite (k : ℕ) : (∑ n ∈ Finset.range k, suzukiQuarterCoeff (n + 32)) ≤
        1 / 127 - 1 / (4 * (k + 32 : ℕ) - 1 : ℝ) := by
      induction k with
      | zero => norm_num
      | succ k ih =>
          rw [Finset.sum_range_succ]
          have h := hstep k
          calc
            _ ≤ (1 / 127 - 1 / (4 * (k + 32 : ℕ) - 1 : ℝ)) +
                (1 / (4 * (k + 32 : ℕ) - 1 : ℝ) -
                  1 / (4 * (k + 33 : ℕ) - 1 : ℝ)) := add_le_add ih h
            _ = _ := by push_cast; ring
    have htail : (∑' n, suzukiQuarterCoeff (n + 32)) ≤ (1 : ℝ) / 127 := by
      apply Real.tsum_le_of_sum_range_le (fun n => by unfold suzukiQuarterCoeff; positivity)
      intro k
      have hd : 0 ≤ (4 * (k + 32 : ℕ) - 1 : ℝ) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      exact (hfinite k).trans (sub_le_self _ (div_nonneg (by norm_num) hd))
    have he := summable_suzukiQuarterCoeff.sum_add_tsum_nat_add 32
    have hn : (∑ n ∈ Finset.range 32, suzukiQuarterCoeff n) + 1 / 127 ≤
        (429934 : ℝ) / 100000 := by norm_num [suzukiQuarterCoeff]
    linarith

/-- Geometric enclosure for the exponentially small quarter-lattice tail. -/
theorem quarterPowerTail {w c : ℝ} {f : ℕ → ℝ}
    (hw : 0 ≤ w) (hw1 : w < 1) (hf : ∀ n, 0 ≤ f n)
    (hc : ∀ n, f (n + 1) ≤ c) :
    Summable (fun n => f n * w ^ (4 * n + 1)) ∧
    0 ≤ (∑' n, f n * w ^ (4 * n + 1)) - f 0 * w ∧
    (∑' n, f n * w ^ (4 * n + 1)) - f 0 * w ≤ c * w ^ 5 / (1 - w ^ 4) := by
  have hq : ‖w ^ 4‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw _)]
    exact pow_lt_one₀ hw hw1 (by norm_num)
  have hg := (summable_geometric_of_norm_lt_one hq).mul_left (c * w ^ 5)
  have hbound (n : ℕ) : f (n + 1) * w ^ (4 * (n + 1) + 1) ≤
      c * w ^ 5 * (w ^ 4) ^ n := by
    rw [show 4 * (n + 1) + 1 = 5 + 4 * n by omega, pow_add, pow_mul]
    nlinarith [mul_le_mul_of_nonneg_right (hc n)
      (mul_nonneg (pow_nonneg hw 5) (pow_nonneg (pow_nonneg hw 4) n))]
  have ht : Summable (fun n => f (n + 1) * w ^ (4 * (n + 1) + 1)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hf _) (pow_nonneg hw _)) hbound hg
  have hs : Summable (fun n => f n * w ^ (4 * n + 1)) :=
    (summable_nat_add_iff 1).mp ht
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one] at he
  refine ⟨hs, ?_, ?_⟩
  · have hp : 0 ≤ ∑' n, f (n + 1) * w ^ (4 * (n + 1) + 1) :=
      tsum_nonneg (fun n => mul_nonneg (hf (n + 1)) (pow_nonneg hw _))
    linarith
  · have hb := ht.tsum_le_tsum hbound hg
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq] at hb
    rw [div_eq_mul_inv]
    linarith

theorem exp_neg_root_quarter {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * (2 * Real.log u)) =
      (u⁻¹) ^ (4 * n + 1) := by
  rw [← Real.exp_log hu, ← Real.exp_neg, ← Real.exp_nat_mul, Real.log_exp]
  congr 1
  push_cast
  ring

theorem arch_root_quarter_series {u : ℝ} (hu : 1 ≤ u) :
    suzukiPsiArchimedean (2 * Real.log u) =
      4 * (u + u⁻¹ - 2) + Real.log u *
        ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        ∑' n, suzukiQuarterCoeff n * (1 - (u⁻¹) ^ (4 * n + 1)) := by
  have hp : 0 < u := lt_of_lt_of_le (by norm_num) hu
  rw [suzukiPsiArchimedean_eq_quarter_tsum (mul_nonneg (by norm_num) (Real.log_nonneg hu))]
  have he1 : Real.exp (2 * Real.log u / 2) = u := by
    rw [mul_div_cancel_left₀ _ (by norm_num), Real.exp_log hp]
  have he2 : Real.exp (-(2 * Real.log u) / 2) = u⁻¹ := by
    rw [show -(2 * Real.log u) / 2 = -Real.log u by ring, Real.exp_neg, Real.exp_log hp]
  rw [he1, he2, ← tsum_mul_left]
  congr 1
  · ring
  · apply tsum_congr
    intro n
    rw [exp_neg_root_quarter hp]
    unfold suzukiQuarterCoeff
    field_simp <;> ring

theorem arch_root_rational_enclosure {u : ℝ} (hu : 1 < u) :
    4 * u - 8 + (-53743 / 10000 : ℝ) * Real.log u + 42954 / 10000 -
        (4 / 25 : ℝ) * (u⁻¹) ^ 5 / (1 - (u⁻¹) ^ 4) ≤
      suzukiPsiArchimedean (2 * Real.log u) ∧
    suzukiPsiArchimedean (2 * Real.log u) ≤
      4 * u - 8 + (-53700 / 10000 : ℝ) * Real.log u + 429934 / 100000 := by
  have hu0 : 0 < u := by linarith
  have hw : 0 ≤ u⁻¹ := inv_nonneg.mpr hu0.le
  have hw1 : u⁻¹ < 1 := (inv_lt_one₀ hu0).mpr hu
  have hf : ∀ n, 0 ≤ suzukiQuarterCoeff n := fun n => by unfold suzukiQuarterCoeff; positivity
  have hc (n : ℕ) : suzukiQuarterCoeff (n + 1) ≤ (4 : ℝ) / 25 := by
    unfold suzukiQuarterCoeff
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith
  obtain ⟨hs, hlo, hhi⟩ := quarterPowerTail hw hw1 hf hc
  have he : (∑' n, suzukiQuarterCoeff n * (1 - (u⁻¹) ^ (4 * n + 1))) =
      (∑' n, suzukiQuarterCoeff n) - ∑' n, suzukiQuarterCoeff n * (u⁻¹) ^ (4 * n + 1) := by
    rw [← summable_suzukiQuarterCoeff.tsum_sub hs]
    apply tsum_congr
    intro n
    ring
  rw [arch_root_quarter_series hu.le, he]
  rw [show suzukiQuarterCoeff 0 = 4 by norm_num [suzukiQuarterCoeff]] at hlo hhi
  have hl := mul_le_mul_of_nonneg_right digammaLogPi_mem_tight.1 (Real.log_nonneg hu.le)
  have hh := mul_le_mul_of_nonneg_right digammaLogPi_mem_tight.2 (Real.log_nonneg hu.le)
  constructor <;> nlinarith [suzukiQuarterTotal_bounds.1, suzukiQuarterTotal_bounds.2]

theorem rootSlope_quarter_series {u : ℝ} (hu : 1 < u) :
    suzukiRootArchSlope u = 2 * (u - u⁻¹) +
      ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) / 2 +
      ∑' n : ℕ, (2 / (4 * (n : ℝ) + 1)) * (u⁻¹) ^ (4 * n + 1) := by
  have hp : 0 < u := by linarith
  unfold suzukiRootArchSlope
  rw [(hasDerivAt_suzukiPsiArchimedean_of_pos
    (mul_pos (by norm_num) (Real.log_pos hu))).deriv,
    suzukiPsiPrimeFreeDerivative_eq_quarter_tsum
      (mul_pos (by norm_num) (Real.log_pos hu))]
  rw [show 2 * Real.log u / 2 = Real.log u by ring,
    show -(2 * Real.log u) / 2 = -Real.log u by ring,
    Real.exp_log hp, Real.exp_neg, Real.exp_log hp, ← tsum_mul_left]
  congr 1
  · ring
  · apply tsum_congr
    intro n
    rw [exp_neg_root_quarter hp]
    field_simp <;> ring

theorem rootSlope_rational_enclosure {u : ℝ} (hu : 1 < u) :
    2 * u - (53743 / 20000 : ℝ) ≤ suzukiRootArchSlope u ∧
    suzukiRootArchSlope u ≤ 2 * u - (53700 / 20000 : ℝ) +
      (2 / 5 : ℝ) * (u⁻¹) ^ 5 / (1 - (u⁻¹) ^ 4) := by
  have hp : 0 < u := by linarith
  have hf (n : ℕ) : 0 ≤ (2 : ℝ) / (4 * (n : ℝ) + 1) := by positivity
  have hc (n : ℕ) : (2 : ℝ) / (4 * ((n + 1 : ℕ) : ℝ) + 1) ≤ 2 / 5 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    push_cast
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  obtain ⟨_, hlo, hhi⟩ := quarterPowerTail (inv_nonneg.mpr hp.le)
    ((inv_lt_one₀ hp).mpr hu) hf hc
  norm_num only [Nat.cast_zero, mul_zero, zero_add, div_one] at hlo hhi
  rw [rootSlope_quarter_series hu]
  constructor <;> linarith [digammaLogPi_mem_tight.1, digammaLogPi_mem_tight.2]

/-- A fresh local affine-state reserve bound. The sample need not lie in the
event cell; unit archimedean curvature controls its slope residual. -/
theorem affine_state_lower_of_sample {x y T I A d : ℝ}
    (hx : Real.log 2 ≤ x) (hy : Real.log 2 ≤ y)
    (ha : A ≤ suzukiPsiArchimedean x - T * x + I)
    (hd : |deriv suzukiPsiArchimedean x - T| ≤ d) :
    A - d ^ 2 / 2 ≤ suzukiPsiArchimedean y - T * y + I := by
  have h := suzukiArchimedean_strong_tangent_lower hx hy
  have hp : 0 ≤ d := (abs_nonneg _).trans hd
  have hs : (deriv suzukiPsiArchimedean x - T) ^ 2 ≤ d ^ 2 := by
    have hh := abs_le.mp hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (show 0 ≤ d +
      (deriv suzukiPsiArchimedean x - T) by linarith [hh.1])]
  nlinarith [sq_nonneg (y - x + (deriv suzukiPsiArchimedean x - T))]

end RHGarden
