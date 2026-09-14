import RHGarden.SuzukiBusyPeriods

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

namespace RHGarden

/-! ## Chebyshev-error coordinates for Suzuki busy periods -/

/-- The classical Chebyshev remainder, expressed using RH Garden's existing
finite Mangoldt sum. -/
noncomputable def suzukiChebyshevError (x : ℝ) : ℝ :=
  suzukiChebyshevPsi x - x

theorem suzukiChebyshevPsi_eq_self_add_error (x : ℝ) :
    suzukiChebyshevPsi x = x + suzukiChebyshevError x := by
  simp [suzukiChebyshevError]

theorem suzukiChebyshevPsi_mono : Monotone suzukiChebyshevPsi := by
  intro x y hxy
  unfold suzukiChebyshevPsi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc (by rfl) (by gcongr)
  · simp

private theorem chebyshevAbelKernel_intervalIntegrable
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x)
      volume a b := by
  have hpsi : IntervalIntegrable suzukiChebyshevPsi volume a b :=
    suzukiChebyshevPsi_mono.intervalIntegrable
  apply hpsi.continuousOn_mul
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact (Real.continuousAt_rpow_const x _
    (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (ha.trans hx.1))))).continuousWithinAt

/-- The interval form of the exact Abel identity. -/
theorem weightedMangoldtInterval_eq_chebyshevInterval
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiWeightedMangoldtInterval m n =
      (n : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi n -
        (m : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi m +
      2⁻¹ * ∫ x : ℝ in (m : ℝ)..(n : ℝ),
        x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x := by
  rw [weightedMangoldtInterval_eq_chebyshevPartialSummation hm hmn]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h1m := chebyshevAbelKernel_intervalIntegrable (a := (1 : ℝ))
    (b := (m : ℝ)) le_rfl hm'
  have h1n := chebyshevAbelKernel_intervalIntegrable (a := (1 : ℝ))
    (b := (n : ℝ)) le_rfl hn'
  rw [← intervalIntegral.integral_of_le hn',
    ← intervalIntegral.integral_of_le hm']
  have hsub :
      (∫ x : ℝ in (1 : ℝ)..(n : ℝ),
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) -
        ∫ x : ℝ in (1 : ℝ)..(m : ℝ),
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x =
        ∫ x : ℝ in (m : ℝ)..(n : ℝ),
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x :=
    intervalIntegral.integral_interval_sub_left h1n h1m
  rw [← hsub]
  ring

private theorem chebyshev_square_kernel
    {u : ℝ} (hu : 0 < u) :
    (u ^ 2) ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi (u ^ 2) * (2 * u) =
      2 * (suzukiChebyshevPsi (u ^ 2) / u ^ 2) := by
  have hpow : (u ^ 2) ^ (-(2⁻¹ : ℝ) - 1) = (u ^ 3)⁻¹ := by
    rw [show -(2⁻¹ : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg (sq_nonneg u), div_eq_mul_inv,
      ← Real.rpow_natCast u 2,
      ← Real.rpow_mul (le_of_lt hu)]
    norm_num
  rw [hpow]
  field_simp

private theorem half_chebyshevKernel_integral_eq_root
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    2⁻¹ * ∫ x : ℝ in (m : ℝ)..(n : ℝ),
        x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x =
      ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
        suzukiChebyshevPsi (u ^ 2) / u ^ 2 := by
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt (m : ℝ)) (b := Real.sqrt (n : ℝ))
    (f := fun u : ℝ => u ^ 2) (f' := fun u : ℝ => 2 * u)
    (g := fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x)
    (continuous_pow 2).continuousOn
    (fun u _hu => by simpa using (hasDerivAt_pow 2 u))
    (fun u hu => by
      rw [min_eq_left hsqrt] at hu
      exact mul_nonneg (by norm_num) (hsqrt_pos.le.trans hu.1.le))
  rw [Real.sq_sqrt (Nat.cast_nonneg m),
    Real.sq_sqrt (Nat.cast_nonneg n)] at hsub
  have hleft :
      (∫ u : ℝ in Real.sqrt m..Real.sqrt n,
          ((fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) ∘
              fun u : ℝ => u ^ 2) u * (2 * u)) =
        ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
          2 * (suzukiChebyshevPsi (u ^ 2) / u ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hsqrt] at hu
    exact chebyshev_square_kernel (hsqrt_pos.trans_le hu.1)
  rw [hleft, intervalIntegral.integral_const_mul] at hsub
  linarith

private theorem rootChebyshevQuotient_intervalIntegrable
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntervalIntegrable
      (fun u : ℝ => suzukiChebyshevPsi (u ^ 2) / u ^ 2)
      volume (Real.sqrt m) (Real.sqrt n) := by
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hkernel := chebyshevAbelKernel_intervalIntegrable
    (a := (m : ℝ)) (b := (n : ℝ)) (by exact_mod_cast hm) (by exact_mod_cast hmn)
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.sqrt (m : ℝ)) (b := Real.sqrt (n : ℝ))
    (f := fun u : ℝ => u ^ 2) (f' := fun u : ℝ => 2 * u)
    (g := fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x)
    (continuous_pow 2).continuousOn
    (fun u _hu => by simpa using (hasDerivAt_pow 2 u))
    (fun u hu => by
      rw [min_eq_left hsqrt] at hu
      exact mul_nonneg (by norm_num) (hsqrt_pos.le.trans hu.1.le))
  rw [Real.sq_sqrt (Nat.cast_nonneg m),
    Real.sq_sqrt (Nat.cast_nonneg n)] at hiff
  have hcomp := hiff.mpr hkernel
  have htwo : IntervalIntegrable
      (fun u : ℝ => 2 * (suzukiChebyshevPsi (u ^ 2) / u ^ 2))
      volume (Real.sqrt m) (Real.sqrt n) := by
    refine hcomp.congr ?_
    intro u hu
    have hu' : 0 < u := by
      rw [uIoc_of_le hsqrt] at hu
      exact hsqrt_pos.trans_le hu.1.le
    exact chebyshev_square_kernel hu'
  simpa using htwo.const_mul (2⁻¹ : ℝ)

/-- Exact root-coordinate Abel summation.  Arithmetic arrivals are a linear
reference flow plus a transformed one-sided Chebyshev error profile. -/
theorem weightedMangoldtInterval_eq_rootChebyshevError
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    suzukiWeightedMangoldtInterval m n =
      2 * (Real.sqrt n - Real.sqrt m) +
      suzukiChebyshevError n / Real.sqrt n -
      suzukiChebyshevError m / Real.sqrt m +
      ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
        suzukiChebyshevError (u ^ 2) / u ^ 2 := by
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hmpos : (0 : ℝ) < Real.sqrt m :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hnpos : (0 : ℝ) < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hm.trans hmn)
  have hpow_m : (m : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt m)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg m)]
    norm_num
  have hpow_n : (n : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg n)]
    norm_num
  have hroot := rootChebyshevQuotient_intervalIntegrable hm hmn
  have herror : IntervalIntegrable
      (fun u : ℝ => suzukiChebyshevError (u ^ 2) / u ^ 2)
      volume (Real.sqrt m) (Real.sqrt n) := by
    have hone : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) volume
        (Real.sqrt m) (Real.sqrt n) := intervalIntegrable_const
    have hsub := hroot.sub hone
    refine hsub.congr ?_
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [uIoc_of_le hsqrt] at hu
      exact ne_of_gt (hmpos.trans_le hu.1.le)
    simp only [suzukiChebyshevError]
    field_simp
  have hsplit :
      (∫ u : ℝ in Real.sqrt m..Real.sqrt n,
          suzukiChebyshevPsi (u ^ 2) / u ^ 2) =
        (Real.sqrt n - Real.sqrt m) +
          ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
            suzukiChebyshevError (u ^ 2) / u ^ 2 := by
    calc
      (∫ u : ℝ in Real.sqrt m..Real.sqrt n,
          suzukiChebyshevPsi (u ^ 2) / u ^ 2) =
          ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
            (1 + suzukiChebyshevError (u ^ 2) / u ^ 2) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hsqrt] at hu
        have hu0 : u ≠ 0 := ne_of_gt (hmpos.trans_le hu.1)
        simp only [suzukiChebyshevError]
        field_simp
        ring
      _ = (∫ _u : ℝ in Real.sqrt m..Real.sqrt n, (1 : ℝ)) +
          ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
            suzukiChebyshevError (u ^ 2) / u ^ 2 :=
        intervalIntegral.integral_add intervalIntegrable_const herror
      _ = (Real.sqrt n - Real.sqrt m) +
          ∫ u : ℝ in Real.sqrt m..Real.sqrt n,
            suzukiChebyshevError (u ^ 2) / u ^ 2 := by simp
  rw [weightedMangoldtInterval_eq_chebyshevInterval hm hmn,
    half_chebyshevKernel_integral_eq_root hm hmn, hpow_m, hpow_n, hsplit]
  simp only [inv_mul_eq_div]
  have hm_sq := Real.sq_sqrt (Nat.cast_nonneg m)
  have hn_sq := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [suzukiChebyshevPsi_eq_self_add_error,
    suzukiChebyshevPsi_eq_self_add_error]
  field_simp [ne_of_gt hmpos, ne_of_gt hnpos]
  nlinarith

private theorem weightedMangoldtPrefix_eq_chebyshevInterval
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    suzukiWeightedMangoldtInterval m ⌊u ^ 2⌋₊ =
      (u ^ 2) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi (u ^ 2) -
        (m : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi m +
      2⁻¹ * ∫ x : ℝ in (m : ℝ)..u ^ 2,
        x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x := by
  have hu0 : 0 < u := (Real.sqrt_pos.2 (by exact_mod_cast hm)).trans_le hmu
  have hmu_sq : (m : ℝ) ≤ u ^ 2 := by
    nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg m) hmu,
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hfloor : m ≤ ⌊u ^ 2⌋₊ := Nat.le_floor hmu_sq
  rw [suzukiWeightedMangoldtInterval_eq_prefix_sub hfloor]
  have hu2 : (1 : ℝ) ≤ u ^ 2 :=
    (by exact_mod_cast hm : (1 : ℝ) ≤ m).trans hmu_sq
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have huPrefix := sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi hu2
  have hmPrefix := sum_vonMangoldt_div_sqrt_eq_suzukiChebyshevPsi hm'
  have hprefix :
      suzukiWeightedMangoldtInterval 0 ⌊u ^ 2⌋₊ -
          suzukiWeightedMangoldtInterval 0 m =
        ((u ^ 2) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi (u ^ 2) +
          2⁻¹ * ∫ x : ℝ in Set.Ioc 1 (u ^ 2),
            x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) -
        ((m : ℝ) ^ (-(2⁻¹ : ℝ)) * suzukiChebyshevPsi m +
          2⁻¹ * ∫ x : ℝ in Set.Ioc 1 (m : ℝ),
            x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) := by
    simpa [suzukiWeightedMangoldtInterval, Nat.floor_natCast] using
      congrArg₂ (· - ·) huPrefix hmPrefix
  rw [hprefix]
  have h1m := chebyshevAbelKernel_intervalIntegrable (a := (1 : ℝ))
    (b := (m : ℝ)) le_rfl hm'
  have h1u := chebyshevAbelKernel_intervalIntegrable (a := (1 : ℝ))
    (b := u ^ 2) le_rfl hu2
  rw [← intervalIntegral.integral_of_le hu2,
    ← intervalIntegral.integral_of_le hm']
  have hsub :
      (∫ x : ℝ in (1 : ℝ)..u ^ 2,
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) -
        ∫ x : ℝ in (1 : ℝ)..(m : ℝ),
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x =
        ∫ x : ℝ in (m : ℝ)..u ^ 2,
          x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x :=
    intervalIntegral.integral_interval_sub_left h1u h1m
  rw [← hsub]
  ring

private theorem half_chebyshevKernel_integral_eq_root_prefix
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    2⁻¹ * ∫ x : ℝ in (m : ℝ)..u ^ 2,
        x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x =
      ∫ v : ℝ in Real.sqrt m..u,
        suzukiChebyshevPsi (v ^ 2) / v ^ 2 := by
  have hmpos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt (m : ℝ)) (b := u)
    (f := fun v : ℝ => v ^ 2) (f' := fun v : ℝ => 2 * v)
    (g := fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x)
    (continuous_pow 2).continuousOn
    (fun v _hv => by simpa using (hasDerivAt_pow 2 v))
    (fun v hv => by
      rw [min_eq_left hmu] at hv
      exact mul_nonneg (by norm_num) (hmpos.le.trans hv.1.le))
  rw [Real.sq_sqrt (Nat.cast_nonneg m)] at hsub
  have hleft :
      (∫ v : ℝ in Real.sqrt m..u,
          ((fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x) ∘
              fun v : ℝ => v ^ 2) v * (2 * v)) =
        ∫ v : ℝ in Real.sqrt m..u,
          2 * (suzukiChebyshevPsi (v ^ 2) / v ^ 2) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hmu] at hv
    exact chebyshev_square_kernel (hmpos.trans_le hv.1)
  rw [hleft, intervalIntegral.integral_const_mul] at hsub
  linarith

private theorem rootChebyshevQuotient_prefix_intervalIntegrable
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    IntervalIntegrable
      (fun v : ℝ => suzukiChebyshevPsi (v ^ 2) / v ^ 2)
      volume (Real.sqrt m) u := by
  have hmpos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hmu_sq : (m : ℝ) ≤ u ^ 2 := by
    nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg m) hmu,
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hkernel := chebyshevAbelKernel_intervalIntegrable
    (a := (m : ℝ)) (b := u ^ 2) (by exact_mod_cast hm) hmu_sq
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.sqrt (m : ℝ)) (b := u)
    (f := fun v : ℝ => v ^ 2) (f' := fun v : ℝ => 2 * v)
    (g := fun x : ℝ => x ^ (-(2⁻¹ : ℝ) - 1) * suzukiChebyshevPsi x)
    (continuous_pow 2).continuousOn
    (fun v _hv => by simpa using (hasDerivAt_pow 2 v))
    (fun v hv => by
      rw [min_eq_left hmu] at hv
      exact mul_nonneg (by norm_num) (hmpos.le.trans hv.1.le))
  rw [Real.sq_sqrt (Nat.cast_nonneg m)] at hiff
  have hcomp := hiff.mpr hkernel
  have htwo : IntervalIntegrable
      (fun v : ℝ => 2 * (suzukiChebyshevPsi (v ^ 2) / v ^ 2))
      volume (Real.sqrt m) u := by
    refine hcomp.congr ?_
    intro v hv
    have hv' : 0 < v := by
      rw [uIoc_of_le hmu] at hv
      exact hmpos.trans_le hv.1.le
    exact chebyshev_square_kernel hv'
  simpa using htwo.const_mul (2⁻¹ : ℝ)

/-- Prefix form of root-coordinate Abel summation, valid at every root
coordinate rather than only at event roots. -/
theorem weightedMangoldtPrefix_eq_rootChebyshevError
    {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hmu : Real.sqrt m ≤ u) :
    suzukiWeightedMangoldtInterval m ⌊u ^ 2⌋₊ =
      2 * (u - Real.sqrt m) +
      suzukiChebyshevError (u ^ 2) / u -
      suzukiChebyshevError m / Real.sqrt m +
      ∫ v : ℝ in Real.sqrt m..u,
        suzukiChebyshevError (v ^ 2) / v ^ 2 := by
  have hmpos : (0 : ℝ) < Real.sqrt m :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hupos : 0 < u := hmpos.trans_le hmu
  have hpow_m : (m : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt m)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg m)]
    norm_num
  have hpow_u : (u ^ 2) ^ (-(2⁻¹ : ℝ)) = u⁻¹ := by
    rw [show -(2⁻¹ : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (sq_nonneg u), div_eq_mul_inv,
      ← Real.rpow_natCast u 2,
      ← Real.rpow_mul hupos.le]
    norm_num
  have hroot := rootChebyshevQuotient_prefix_intervalIntegrable hm hmu
  have herror : IntervalIntegrable
      (fun v : ℝ => suzukiChebyshevError (v ^ 2) / v ^ 2)
      volume (Real.sqrt m) u := by
    have hone : IntervalIntegrable (fun _v : ℝ => (1 : ℝ)) volume
        (Real.sqrt m) u := intervalIntegrable_const
    have hsub := hroot.sub hone
    refine hsub.congr ?_
    intro v hv
    have hv0 : v ≠ 0 := by
      rw [uIoc_of_le hmu] at hv
      exact ne_of_gt (hmpos.trans_le hv.1.le)
    simp only [suzukiChebyshevError]
    field_simp
  have hsplit :
      (∫ v : ℝ in Real.sqrt m..u,
          suzukiChebyshevPsi (v ^ 2) / v ^ 2) =
        (u - Real.sqrt m) +
          ∫ v : ℝ in Real.sqrt m..u,
            suzukiChebyshevError (v ^ 2) / v ^ 2 := by
    calc
      (∫ v : ℝ in Real.sqrt m..u,
          suzukiChebyshevPsi (v ^ 2) / v ^ 2) =
          ∫ v : ℝ in Real.sqrt m..u,
            (1 + suzukiChebyshevError (v ^ 2) / v ^ 2) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hmu] at hv
        have hv0 : v ≠ 0 := ne_of_gt (hmpos.trans_le hv.1)
        simp only [suzukiChebyshevError]
        field_simp
        ring
      _ = (∫ _v : ℝ in Real.sqrt m..u, (1 : ℝ)) +
          ∫ v : ℝ in Real.sqrt m..u,
            suzukiChebyshevError (v ^ 2) / v ^ 2 :=
        intervalIntegral.integral_add intervalIntegrable_const herror
      _ = (u - Real.sqrt m) +
          ∫ v : ℝ in Real.sqrt m..u,
            suzukiChebyshevError (v ^ 2) / v ^ 2 := by simp
  rw [weightedMangoldtPrefix_eq_chebyshevInterval hm hmu,
    half_chebyshevKernel_integral_eq_root_prefix hm hmu,
    hpow_m, hpow_u, hsplit]
  simp only [inv_mul_eq_div]
  have hm_sq := Real.sq_sqrt (Nat.cast_nonneg m)
  rw [suzukiChebyshevPsi_eq_self_add_error,
    suzukiChebyshevPsi_eq_self_add_error]
  field_simp [ne_of_gt hmpos, ne_of_gt hupos]
  nlinarith

/-! ## Exact archimedean service defect -/

noncomputable def suzukiRootArchDefect (a b : ℝ) : ℝ :=
  ∫ u in a..b, 2 / (u ^ 2 * (u ^ 4 - 1))

private theorem archDefect_integrand_eq
    {u : ℝ} (hu : Real.sqrt 2 ≤ u) :
    2 / (u ^ 2 * (u ^ 4 - 1)) =
      2 * (1 - suzukiCurvatureFactor u) := by
  have hu0 : u ≠ 0 := ne_of_gt ((Real.sqrt_pos.2 (by norm_num)).trans_le hu)
  have hu4 : u ^ 4 - 1 ≠ 0 := by
    have hsq : (2 : ℝ) ≤ u ^ 2 := by
      nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg 2) hu,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg (u ^ 2 - 2)]
  rw [suzukiCurvatureFactor]
  field_simp
  ring

private theorem suzukiRootArchDefect_intervalIntegrable
    {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => 2 / (u ^ 2 * (u ^ 4 - 1))) volume a b := by
  have halt : IntervalIntegrable
      (fun u => 2 * (1 - suzukiCurvatureFactor u)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (by
      intro u hu
      exact (continuousAt_const.mul
        (continuousAt_const.sub
          (continuousAt_suzukiCurvatureFactor (ha.trans hu.1)))).continuousWithinAt)
  refine halt.congr ?_
  intro u hu
  have hau : a ≤ u := by
    rw [uIoc_of_le hab] at hu
    exact hu.1.le
  exact (archDefect_integrand_eq (ha.trans hau)).symm

theorem rootService_eq_linear_sub_archDefect
    {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) :
    suzukiRootService a b =
      2 * (b - a) - suzukiRootArchDefect a b := by
  rw [suzukiRootService_eq_integral ha hab]
  have hdefect : IntervalIntegrable
      (fun u => 2 / (u ^ 2 * (u ^ 4 - 1))) volume a b :=
    suzukiRootArchDefect_intervalIntegrable ha hab
  rw [show (∫ u in a..b, 2 * suzukiCurvatureFactor u) =
      ∫ u in a..b, (2 - 2 / (u ^ 2 * (u ^ 4 - 1))) by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    change 2 * suzukiCurvatureFactor u =
      2 - 2 / (u ^ 2 * (u ^ 4 - 1))
    rw [archDefect_integrand_eq (ha.trans hu.1)]
    ring]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hdefect]
  simp [suzukiRootArchDefect]
  ring

theorem suzukiRootArchDefect_nonneg
    {a b : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) :
    0 ≤ suzukiRootArchDefect a b := by
  unfold suzukiRootArchDefect
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  rw [archDefect_integrand_eq (ha.trans hu.1)]
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (le_of_lt (suzukiCurvatureFactor_lt_one (ha.trans hu.1))))

theorem suzukiRootArchDefect_mono_right
    {a b c : ℝ} (ha : Real.sqrt 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    suzukiRootArchDefect a b ≤ suzukiRootArchDefect a c := by
  rw [show suzukiRootArchDefect a c =
      suzukiRootArchDefect a b + suzukiRootArchDefect b c by
    unfold suzukiRootArchDefect
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact suzukiRootArchDefect_intervalIntegrable ha hab
    · exact suzukiRootArchDefect_intervalIntegrable (ha.trans hab) hbc]
  exact le_add_of_nonneg_right (suzukiRootArchDefect_nonneg (ha.trans hab) hbc)

/-! ## Exact Chebyshev excess and backlog profiles -/

/-- The canonical transformed Chebyshev-error profile from the event root
`sqrt m` to an arbitrary later root coordinate. -/
noncomputable def suzukiChebyshevExcessProfile (m : ℕ) (u : ℝ) : ℝ :=
  suzukiChebyshevError (u ^ 2) / u -
    suzukiChebyshevError m / Real.sqrt m +
    (∫ v : ℝ in Real.sqrt m..u,
      suzukiChebyshevError (v ^ 2) / v ^ 2) +
    suzukiRootArchDefect (Real.sqrt m) u

/-- Exact decomposition of every cumulative arrival/service prefix. -/
theorem arrivalServiceExcess_eq_chebyshevError
    {m : ℕ} {u : ℝ} (hm : 2 ≤ m) (hmu : Real.sqrt m ≤ u) :
    suzukiWeightedMangoldtInterval m ⌊u ^ 2⌋₊ -
        suzukiRootService (Real.sqrt m) u =
      suzukiChebyshevExcessProfile m u := by
  have hsqrt2 : Real.sqrt 2 ≤ Real.sqrt m :=
    Real.sqrt_le_sqrt (by exact_mod_cast hm)
  rw [weightedMangoldtPrefix_eq_rootChebyshevError
      (show 1 ≤ m from hm.trans' (by norm_num)) hmu,
    rootService_eq_linear_sub_archDefect hsqrt2 hmu]
  unfold suzukiChebyshevExcessProfile
  ring

theorem suzukiArrivalServiceExcess_eq_chebyshevError
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    suzukiArrivalServiceExcess m n =
      suzukiChebyshevError n / Real.sqrt n -
        suzukiChebyshevError m / Real.sqrt m +
        (∫ u : ℝ in Real.sqrt m..Real.sqrt n,
          suzukiChebyshevError (u ^ 2) / u ^ 2) +
        suzukiRootArchDefect (Real.sqrt m) (Real.sqrt n) := by
  have hsqrt2 : Real.sqrt 2 ≤ Real.sqrt m :=
    Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  rw [suzukiArrivalServiceExcess,
    weightedMangoldtInterval_eq_rootChebyshevError
      (show 1 ≤ m from hm.trans' (by norm_num)) hmn,
    rootService_eq_linear_sub_archDefect hsqrt2 hsqrt]
  ring

/-- Between Mangoldt events the arithmetic arrival is constant while smooth
service increases.  Thus a prefix excess can attain a new maximum only at a
right-continuous event root; no continuum of interior checks is needed. -/
theorem arrivalServiceExcess_max_at_event
    {q r : ℕ} (h : IsMangoldtBlock q r) (hq : 2 ≤ q)
    {u : ℝ} (hqu : Real.sqrt q ≤ u) (hur : u < Real.sqrt r) :
    suzukiWeightedMangoldtInterval q ⌊u ^ 2⌋₊ -
        suzukiRootService (Real.sqrt q) u ≤ 0 := by
  have hu0 : 0 ≤ u := (Real.sqrt_nonneg q).trans hqu
  have hfloor : q ≤ ⌊u ^ 2⌋₊ := by
    apply Nat.le_floor
    nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg q) hqu,
      Real.sq_sqrt (Nat.cast_nonneg q)]
  have hslopeRoot := suzukiRootMangoldtSlope_eq_on_block h hqu hur
  have hslope : suzukiMangoldtSlope ⌊u ^ 2⌋₊ = suzukiMangoldtSlope q := by
    simpa [suzukiRootMangoldtSlope] using hslopeRoot
  have harrival := suzukiMangoldtSlope_sub_eq_weightedInterval
    (show 1 ≤ q from hq.trans' (by norm_num)) hfloor
  have harrivalZero : suzukiWeightedMangoldtInterval q ⌊u ^ 2⌋₊ = 0 := by
    linarith
  have hservice := suzukiRootService_nonneg hq hqu
  rw [harrivalZero]
  linarith

/-- At the beginning of a negative excursion, the entire subsequent backlog
is the positive part of one explicit Chebyshev-error profile. -/
theorem rootSlopeBacklog_eq_chebyshevProfile
    {m : ℕ} {u : ℝ} (hm : 2 ≤ m) (hmu : Real.sqrt m ≤ u)
    (hstart : suzukiRootSlopeDiscrepancy (Real.sqrt m) ≤ 0) :
    suzukiRootSlopeBacklog u =
      max (suzukiRootSlopeBacklog (Real.sqrt m) +
        suzukiChebyshevExcessProfile m u) 0 := by
  have hbalance := rootSlopeDiscrepancy_sub_sqrt_eq_service_sub_arrival
    (show 1 ≤ m from hm.trans' (by norm_num)) hmu
  have hprofile := arrivalServiceExcess_eq_chebyshevError hm hmu
  have hstart_backlog : suzukiRootSlopeBacklog (Real.sqrt m) =
      -suzukiRootSlopeDiscrepancy (Real.sqrt m) := by
    rw [suzukiRootSlopeBacklog, max_eq_left]
    linarith
  rw [suzukiRootSlopeBacklog, hstart_backlog]
  congr 1
  linarith

/-- Exact weighted loss functional attached to a Chebyshev profile. -/
noncomputable def suzukiChebyshevProfileLoss (m : ℕ) (b : ℝ) : ℝ :=
  ∫ u in Real.sqrt m..b,
    2 / u * max (suzukiRootSlopeBacklog (Real.sqrt m) +
      suzukiChebyshevExcessProfile m u) 0

/-- On a complete negative block excursion, the exact Suzuki drawdown is the
weighted positive part of the Chebyshev-error profile. -/
theorem busyPeriodLoss_eq_chebyshevProfile
    {q r : ℕ} (h : IsMangoldtBlock q r) (hq : 2 ≤ q)
    (hexc : IsSuzukiRootNegativeExcursion (Real.sqrt q) (Real.sqrt r)) :
    suzukiBusyPeriodLoss (Real.sqrt q) (Real.sqrt r) =
      suzukiChebyshevProfileLoss q (Real.sqrt r) := by
  rw [suzukiBusyPeriodLoss_eq_integral_backlog h le_rfl le_rfl hexc]
  unfold suzukiChebyshevProfileLoss
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hexc.1] at hu
  change 2 / u * suzukiRootSlopeBacklog u =
    2 / u * max (suzukiRootSlopeBacklog (Real.sqrt q) +
      suzukiChebyshevExcessProfile q u) 0
  rw [rootSlopeBacklog_eq_chebyshevProfile hq hu.1
    (hexc.2 _ ⟨le_rfl, hexc.1⟩)]

/-! ## One-sided Chebyshev envelope certificates -/

/-- A one-sided Chebyshev error envelope on the integer/root range relevant
to one busy period.  No lower or absolute error estimate is requested. -/
def SuzukiChebyshevErrorUpperEnvelope
    (m : ℕ) (b : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (m : ℝ) (b ^ 2), suzukiChebyshevError x ≤ U x

/-- Profile obtained by replacing the moving Chebyshev error by a certified
one-sided upper envelope.  The start value remains exact. -/
noncomputable def suzukiChebyshevUpperProfile
    (m : ℕ) (U : ℝ → ℝ) (u : ℝ) : ℝ :=
  U (u ^ 2) / u - suzukiChebyshevError m / Real.sqrt m +
    (∫ v : ℝ in Real.sqrt m..u, U (v ^ 2) / v ^ 2) +
    suzukiRootArchDefect (Real.sqrt m) u

theorem chebyshevExcessProfile_le_upperProfile
    {m : ℕ} {b u : ℝ} {U : ℝ → ℝ}
    (hm : 2 ≤ m) (hub : u ∈ Icc (Real.sqrt m) b)
    (hUb : SuzukiChebyshevErrorUpperEnvelope m b U)
    (hUintegrable : IntervalIntegrable
      (fun v : ℝ => U (v ^ 2) / v ^ 2) volume (Real.sqrt m) u) :
    suzukiChebyshevExcessProfile m u ≤
      suzukiChebyshevUpperProfile m U u := by
  have hmpos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm.trans' (by norm_num))
  have hmu_sq : (m : ℝ) ≤ u ^ 2 := by
    nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg m) hub.1,
      Real.sq_sqrt (Nat.cast_nonneg m)]
  have hub_sq : u ^ 2 ≤ b ^ 2 := by
    have hu0 : 0 ≤ u := hmpos.le.trans hub.1
    have hb0 : 0 ≤ b := hu0.trans hub.2
    nlinarith [mul_self_le_mul_self hu0 hub.2]
  have hpoint := hUb (u ^ 2) ⟨hmu_sq, hub_sq⟩
  have herror := rootChebyshevQuotient_prefix_intervalIntegrable
    (show 1 ≤ m from hm.trans' (by norm_num)) hub.1
  have hone : IntervalIntegrable (fun _v : ℝ => (1 : ℝ)) volume
      (Real.sqrt m) u := intervalIntegrable_const
  have herrorInt : IntervalIntegrable
      (fun v : ℝ => suzukiChebyshevError (v ^ 2) / v ^ 2)
      volume (Real.sqrt m) u := by
    have hsub := herror.sub hone
    refine hsub.congr ?_
    intro v hv
    rw [uIoc_of_le hub.1] at hv
    have hv0 : v ≠ 0 := ne_of_gt (hmpos.trans_le hv.1.le)
    simp only [suzukiChebyshevError]
    field_simp
  have hintegral :
      (∫ v : ℝ in Real.sqrt m..u,
        suzukiChebyshevError (v ^ 2) / v ^ 2) ≤
      ∫ v : ℝ in Real.sqrt m..u, U (v ^ 2) / v ^ 2 := by
    apply intervalIntegral.integral_mono_on hub.1 herrorInt hUintegrable
    intro v hv
    have hvpos : 0 < v := hmpos.trans_le hv.1
    have hvm : (m : ℝ) ≤ v ^ 2 := by
      nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg m) hv.1,
        Real.sq_sqrt (Nat.cast_nonneg m)]
    have hvb : v ^ 2 ≤ b ^ 2 := by
      have hb0 : 0 ≤ b := (hmpos.le.trans hub.1).trans hub.2
      nlinarith [mul_self_le_mul_self hvpos.le (hv.2.trans hub.2)]
    exact div_le_div_of_nonneg_right (hUb (v ^ 2) ⟨hvm, hvb⟩) (sq_pos_of_pos hvpos).le
  unfold suzukiChebyshevExcessProfile suzukiChebyshevUpperProfile
  have hu0 : 0 < u := hmpos.trans_le hub.1
  have hterminal := div_le_div_of_nonneg_right hpoint hu0.le
  linarith

/-- A tail theorem may be supplied as a one-sided error estimate; this is
strictly weaker data than an absolute PNT error bound. -/
def SuzukiChebyshevTailEnvelope (U : ℝ → ℝ) (X : ℝ) : Prop :=
  ∀ x, X ≤ x → suzukiChebyshevError x ≤ U x

/-- A theorem-backed one-sided tail estimate supplies exactly the local
arithmetic field needed by every busy-period certificate starting beyond its
threshold.  No estimate for `|psi(x)-x|` is introduced. -/
theorem SuzukiChebyshevTailEnvelope.toErrorUpperEnvelope
    {U : ℝ → ℝ} {X b : ℝ} {m : ℕ}
    (htail : SuzukiChebyshevTailEnvelope U X)
    (hmX : X ≤ m) :
    SuzukiChebyshevErrorUpperEnvelope m b U := by
  intro x hx
  exact htail x (hmX.trans hx.1)

/-- Proof-carrying profile certificate.  Floating-point Explorer output
cannot construct this structure. -/
structure SuzukiChebyshevBusyPeriodCertificate where
  startEvent : ℕ
  endRoot : ℝ
  envelope : ℝ → ℝ
  reserveLower : ℝ
  startEvent_ge_two : 2 ≤ startEvent
  roots_ordered : Real.sqrt startEvent ≤ endRoot
  start_negative : suzukiRootSlopeDiscrepancy (Real.sqrt startEvent) ≤ 0
  error_upper : SuzukiChebyshevErrorUpperEnvelope startEvent endRoot envelope
  envelope_integrable : ∀ u ∈ Icc (Real.sqrt startEvent) endRoot,
    IntervalIntegrable (fun v : ℝ => envelope (v ^ 2) / v ^ 2)
      volume (Real.sqrt startEvent) u
  reserve_bound : reserveLower ≤ suzukiPsiRoot (Real.sqrt startEvent)
  profile_loss_bound : ∀ u ∈ Icc (Real.sqrt startEvent) endRoot,
    (∫ v in Real.sqrt startEvent..u,
      2 / v * max (suzukiRootSlopeBacklog (Real.sqrt startEvent) +
        suzukiChebyshevUpperProfile startEvent envelope v) 0) ≤ reserveLower
  exact_loss_bound : ∀ u ∈ Icc (Real.sqrt startEvent) endRoot,
    suzukiPsiRoot (Real.sqrt startEvent) - suzukiPsiRoot u ≤
      ∫ v in Real.sqrt startEvent..u, 2 / v * suzukiRootSlopeBacklog v
  backlog_integrable : ∀ u ∈ Icc (Real.sqrt startEvent) endRoot,
    IntervalIntegrable (fun v => 2 / v * suzukiRootSlopeBacklog v)
      volume (Real.sqrt startEvent) u
  upper_integrable : ∀ u ∈ Icc (Real.sqrt startEvent) endRoot,
    IntervalIntegrable
      (fun v => 2 / v * max (suzukiRootSlopeBacklog (Real.sqrt startEvent) +
        suzukiChebyshevUpperProfile startEvent envelope v) 0)
      volume (Real.sqrt startEvent) u

theorem SuzukiChebyshevBusyPeriodCertificate.psiRoot_nonnegative
    (certificate : SuzukiChebyshevBusyPeriodCertificate) :
    ∀ u ∈ Icc (Real.sqrt certificate.startEvent) certificate.endRoot,
      0 ≤ suzukiPsiRoot u := by
  intro u hu
  have hprofile := chebyshevExcessProfile_le_upperProfile
    certificate.startEvent_ge_two hu
    certificate.error_upper (certificate.envelope_integrable u hu)
  have hbackEq := rootSlopeBacklog_eq_chebyshevProfile
    certificate.startEvent_ge_two hu.1 certificate.start_negative
  have hback : suzukiRootSlopeBacklog u ≤
      max (suzukiRootSlopeBacklog (Real.sqrt certificate.startEvent) +
        suzukiChebyshevUpperProfile certificate.startEvent certificate.envelope u) 0 := by
    rw [hbackEq]
    exact max_le_max_right 0 (by linarith)
  have hmpos : 0 < Real.sqrt (certificate.startEvent : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast certificate.startEvent_ge_two.trans' (by norm_num))
  have hintegral :
      (∫ v in Real.sqrt certificate.startEvent..u,
        2 / v * suzukiRootSlopeBacklog v) ≤
      ∫ v in Real.sqrt certificate.startEvent..u,
        2 / v * max (suzukiRootSlopeBacklog (Real.sqrt certificate.startEvent) +
          suzukiChebyshevUpperProfile certificate.startEvent certificate.envelope v) 0 := by
    apply intervalIntegral.integral_mono_on hu.1
      (certificate.backlog_integrable u hu) (certificate.upper_integrable u hu)
    intro v hv
    have hvpos : 0 < v := hmpos.trans_le hv.1
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hvpos.le)
    have hvall : v ∈ Icc (Real.sqrt certificate.startEvent) certificate.endRoot :=
      ⟨hv.1, hv.2.trans hu.2⟩
    have hvprofile := chebyshevExcessProfile_le_upperProfile
      certificate.startEvent_ge_two hvall
      certificate.error_upper (certificate.envelope_integrable v hvall)
    rw [rootSlopeBacklog_eq_chebyshevProfile
      certificate.startEvent_ge_two hv.1 certificate.start_negative]
    exact max_le_max_right 0 (by linarith)
  linarith [certificate.exact_loss_bound u hu,
    certificate.profile_loss_bound u hu, certificate.reserve_bound]

/-- Canonical one-sided Chebyshev-error certificate interface.  Its sole
arithmetic field is `error_upper`; all remaining fields are analytic loss
accounting checked independently by Lean. -/
theorem busyPeriod_safe_of_chebyshev_error_profile
    (certificate : SuzukiChebyshevBusyPeriodCertificate) :
    ∀ u ∈ Icc (Real.sqrt certificate.startEvent) certificate.endRoot,
      0 ≤ suzukiPsiRoot u :=
  certificate.psiRoot_nonnegative

end RHGarden
