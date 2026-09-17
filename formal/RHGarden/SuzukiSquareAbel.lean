import RHGarden.SuzukiSurchargeSummability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Real-endpoint Abel summation and a finite, anchored theta-error estimate.
Both endpoint errors are retained. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace RHGarden

def suzukiPrimeReciprocalWindow (y z : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p / p

theorem intervalIntegrable_theta_div_sq {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    IntervalIntegrable (fun x => Chebyshev.theta x / x ^ 2) volume y z := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hyz]
  have hi : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Icc y z) := by
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero _ (hy.trans_le hx.1).ne')).continuousWithinAt
  have h := integrableOn_mul_sum_Icc (m := 0) (fun n : ℕ => if n.Prime then Real.log n else 0) hy.le hi
  simpa [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, div_eq_mul_inv, mul_comm] using h

/-- Abel summation at arbitrary positive real endpoints, with the lower endpoint excluded. -/
theorem primeReciprocalWindow_eq_abel {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    suzukiPrimeReciprocalWindow y z =
      Chebyshev.theta z / z - Chebyshev.theta y / y +
        ∫ x in y..z, Chebyshev.theta x / x ^ 2 := by
  have hd : ∀ x ∈ Icc y z, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) x := by
    intro x hx
    exact differentiableAt_inv (hy.trans_le hx.1).ne'
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Icc y z) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact (((continuousAt_id.pow 2).inv₀
      (pow_ne_zero _ (hy.trans_le hx.1).ne')).neg).continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => if n.Prime then Real.log n else 0) hy.le hyz hd hi
  rw [← intervalIntegral.integral_of_le hyz] at h
  have hl : (∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊z⌋₊,
      (k : ℝ)⁻¹ * (if k.Prime then Real.log k else 0)) =
      suzukiPrimeReciprocalWindow y z := by
    simp [suzukiPrimeReciprocalWindow, Finset.sum_filter, mul_ite, div_eq_mul_inv, mul_comm]
  rw [hl] at h
  simp only [← Finset.sum_filter, ← Chebyshev.theta_eq_sum_Icc] at h
  have he : (∫ x in y..z, deriv (fun t : ℝ => t⁻¹) x * Chebyshev.theta x) =
      -(∫ x in y..z, Chebyshev.theta x / x ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    simp [deriv_inv, div_eq_mul_inv, mul_comm]
  rw [he] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem primeReciprocalWindow_error {y z epsilon : ℝ}
    (hy : 0 < y) (hyz : y ≤ z) (_hepsilon : 0 ≤ epsilon)
    (htheta : ∀ x ∈ Icc y z, |Chebyshev.theta x - x| ≤ epsilon * x) :
    |suzukiPrimeReciprocalWindow y z - Real.log (z / y)| ≤
      epsilon * (2 + Real.log (z / y)) := by
  have hz : 0 < z := hy.trans_le hyz
  have hn : (0 : ℝ) ∉ uIcc y z := by
    rw [uIcc_of_le hyz]
    intro h
    exact (not_le.mpr hy) h.1
  have hiInv : IntervalIntegrable (fun x : ℝ => 1 / x) volume y z := by
    apply ContinuousOn.intervalIntegrable_of_Icc hyz
    intro x hx
    exact (continuousAt_const.div continuousAt_id (hy.trans_le hx.1).ne').continuousWithinAt
  have hiTheta := intervalIntegrable_theta_div_sq hy hyz
  have hiErr : IntervalIntegrable (fun x => (Chebyshev.theta x - x) / x ^ 2) volume y z := by
    apply (hiTheta.sub hiInv).congr
    intro x hx
    rw [uIoc_of_le hyz] at hx
    dsimp
    field_simp
  have hErrInt : (∫ x in y..z, (Chebyshev.theta x - x) / x ^ 2) =
      (∫ x in y..z, Chebyshev.theta x / x ^ 2) - Real.log (z / y) := by
    rw [← integral_one_div hn, ← intervalIntegral.integral_sub hiTheta hiInv]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hyz] at hx
    have hx0 := (hy.trans_le hx.1).ne'
    field_simp
  have hb (x : ℝ) (hx : x ∈ Icc y z) :
      |(Chebyshev.theta x - x) / x ^ 2| ≤ epsilon * (1 / x) := by
    have hx0 : 0 < x := hy.trans_le hx.1
    rw [abs_div, abs_of_nonneg (sq_nonneg x)]
    calc
      _ ≤ (epsilon * x) / x ^ 2 := div_le_div_of_nonneg_right (htheta x hx) (sq_nonneg x)
      _ = _ := by field_simp
  have hIntegral : |∫ x in y..z, (Chebyshev.theta x - x) / x ^ 2| ≤
      epsilon * Real.log (z / y) := by
    calc
      _ ≤ ∫ x in y..z, |(Chebyshev.theta x - x) / x ^ 2| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := fun x =>
            (Chebyshev.theta x - x) / x ^ 2) hyz)
      _ ≤ ∫ x in y..z, epsilon * (1 / x) :=
        intervalIntegral.integral_mono_on hyz hiErr.abs (hiInv.const_mul epsilon) hb
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_one_div hn]
  have hend (x : ℝ) (hx : x ∈ Icc y z) : |Chebyshev.theta x / x - 1| ≤ epsilon := by
    have hx0 : 0 < x := hy.trans_le hx.1
    rw [← div_self hx0.ne', ← sub_div, abs_div, abs_of_pos hx0]
    exact (div_le_iff₀ hx0).mpr (htheta x hx)
  have hidentity : suzukiPrimeReciprocalWindow y z - Real.log (z / y) =
      (Chebyshev.theta z / z - 1) - (Chebyshev.theta y / y - 1) +
        ∫ x in y..z, (Chebyshev.theta x - x) / x ^ 2 := by
    rw [primeReciprocalWindow_eq_abel hy hyz, hErrInt]
    ring
  rw [hidentity]
  calc
    _ ≤ |Chebyshev.theta z / z - 1| + |Chebyshev.theta y / y - 1| +
        |∫ x in y..z, (Chebyshev.theta x - x) / x ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ epsilon + epsilon + epsilon * Real.log (z / y) :=
      add_le_add (add_le_add (hend z ⟨hyz, le_rfl⟩) (hend y ⟨le_rfl, hyz⟩)) hIntegral
    _ = _ := by ring

end RHGarden
