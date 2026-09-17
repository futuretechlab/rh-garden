import RHGarden.SuzukiAnchoredIntegral

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Two-scale integration: a long-prefix increment premise controls the contribution
of shorter prefixes, not their endpoint safety. No arithmetic premise is discharged here. -/
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace RHGarden

theorem anchoredError_le_twoScale {m : ℕ} {H h epsilon : ℝ}
    (_hH : 0 < H) (hHh : H ≤ h) (_he : 0 ≤ epsilon)
    (harith : ∀ t ∈ Icc H h, suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (1 + epsilon) * t)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    suzukiAnchoredError m (m + t) ≤ epsilon * t + (1 + epsilon) * max (H - t) 0 := by
  unfold suzukiAnchoredError
  by_cases hHt : H ≤ t
  · rw [max_eq_right (by linarith : H - t ≤ 0)]
    nlinarith [harith t ⟨hHt, ht.2⟩]
  · rw [max_eq_left (by linarith : 0 ≤ H - t)]
    have hp := suzukiChebyshevPsi_mono (show (m : ℝ) + t ≤ m + H by linarith)
    nlinarith [harith H ⟨le_rfl, hHh⟩]

theorem integratedKernel_antitone {x y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hzx : z ≤ x) :
    suzukiIntegratedKernel x z ≤ suzukiIntegratedKernel x y := by
  have hz := hy.trans_le hyz
  have hx := hz.trans_le hzx
  have hl : Real.log (x / z) ≤ Real.log (x / y) :=
    Real.log_le_log (div_pos hx hz) (div_le_div_of_nonneg_left hx.le hy hyz)
  have hn : 0 ≤ 1 + (1 / 2 : ℝ) * Real.log (x / z) := by
    have := Real.log_nonneg ((one_le_div hz).mpr hzx); positivity
  have hd : y * Real.sqrt y ≤ z * Real.sqrt z :=
    mul_le_mul hyz (Real.sqrt_le_sqrt hyz) (Real.sqrt_nonneg _) hz.le
  exact (div_le_div_of_nonneg_left hn (by positivity) hd).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

theorem integratedKernel_ge_terminal {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    1 / (x * Real.sqrt x) ≤ suzukiIntegratedKernel x y := by
  have h := integratedKernel_antitone hy hyx le_rfl
  simpa [suzukiIntegratedKernel, (hy.trans_le hyx).ne'] using h

def suzukiShiftedIntegratedKernel (m : ℕ) (h t : ℝ) : ℝ :=
  suzukiIntegratedKernel (m + h) (m + t)

theorem shiftedIntegratedKernel_nonneg {m : ℕ} {h t : ℝ} (hm : 1 ≤ m) (ht : t ∈ Icc 0 h) :
    0 ≤ suzukiShiftedIntegratedKernel m h t := by
  apply integratedKernel_nonneg
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    linarith [ht.1]
  · linarith [ht.2]

theorem shiftedIntegratedKernel_le_initial {m : ℕ} {h t : ℝ} (hm : 1 ≤ m) (ht : t ∈ Icc 0 h) :
    suzukiShiftedIntegratedKernel m h t ≤ suzukiShiftedIntegratedKernel m h 0 := by
  unfold suzukiShiftedIntegratedKernel
  rw [add_zero]
  exact integratedKernel_antitone (by exact_mod_cast hm) (by linarith [ht.1]) (by linarith [ht.2])

theorem integral_shiftedIntegratedKernel_moment {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 ≤ h) :
    (∫ t in 0..h, t * suzukiShiftedIntegratedKernel m h t) = suzukiIntegratedMainTerm m (m + h) := by
  have hs := intervalIntegral.integral_comp_add_left
    (fun y => (y - m) * suzukiIntegratedKernel (m + h) y) (m : ℝ) (a := 0) (b := h)
  simp only [add_zero, add_sub_cancel_left] at hs
  unfold suzukiShiftedIntegratedKernel
  rw [hs, integral_linear_integratedKernel (by exact_mod_cast hm) (by linarith)]
  rfl

theorem anchoredIntegral_eq_shifted {m : ℕ} (h : ℝ) :
    suzukiAnchoredIntegral m (m + h) =
      ∫ t in 0..h, suzukiAnchoredError m (m + t) * suzukiShiftedIntegratedKernel m h t := by
  symm
  simpa [suzukiAnchoredIntegral, suzukiShiftedIntegratedKernel] using
    intervalIntegral.integral_comp_add_left
      (fun y => suzukiAnchoredError m y * suzukiIntegratedKernel (m + h) y) (m : ℝ) (a := 0) (b := h)

theorem continuousOn_shiftedIntegratedKernel {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 ≤ h) :
    ContinuousOn (suzukiShiftedIntegratedKernel m h) (Icc 0 h) := by
  exact (continuousOn_integratedKernel (m := (m : ℝ)) (x := (m : ℝ) + h)
    (by exact_mod_cast hm) (by linarith)).comp
    (continuous_const.add continuous_id).continuousOn (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem integral_positive_triangle {H h : ℝ} (hH : 0 ≤ H) (hHh : H ≤ h) :
    (∫ t in 0..h, max (H - t) 0) = H ^ 2 / 2 := by
  have hc : Continuous (fun t : ℝ => max (H - t) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 H) (hc.intervalIntegrable H h)]
  have he : (∫ t in 0..H, max (H - t) 0) = ∫ t in 0..H, H - t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hH] at ht
    exact max_eq_left (by linarith [ht.2])
  have hz : (∫ t in H..h, max (H - t) 0) = 0 := by
    calc
      _ = ∫ _t in H..h, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hHh] at ht
        exact max_eq_right (by linarith [ht.1])
      _ = 0 := by simp
  rw [he, hz, add_zero, intervalIntegral.integral_sub intervalIntegrable_const (by exact continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id]
  simp
  ring

/-- Finite two-scale transfer; the only arithmetic premise starts at H. -/
theorem anchoredIntegral_le_twoScale {m : ℕ} {H h epsilon : ℝ}
    (hm : 1 ≤ m) (hH : 0 < H) (hHh : H ≤ h) (he : 0 ≤ epsilon)
    (harith : ∀ t ∈ Icc H h, suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (1 + epsilon) * t) :
    suzukiAnchoredIntegral m (m + h) ≤ epsilon * suzukiIntegratedMainTerm m (m + h) +
      (1 + epsilon) * (H ^ 2 / 2) * suzukiIntegratedKernel (m + h) m := by
  have hh : 0 ≤ h := hH.le.trans hHh
  have hw := continuousOn_shiftedIntegratedKernel hm hh
  have htw : IntervalIntegrable (fun t => t * suzukiShiftedIntegratedKernel m h t) volume 0 h :=
    (continuous_id.continuousOn.mul hw).intervalIntegrable_of_Icc hh
  have hb : Continuous (fun t : ℝ => (1 + epsilon) * max (H - t) 0 * suzukiIntegratedKernel (m + h) m) :=
    (continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const)).mul continuous_const
  have hi : IntervalIntegrable
      (fun t => suzukiAnchoredError m (m + t) * suzukiShiftedIntegratedKernel m h t) volume 0 h := by
    have h := (intervalIntegrable_anchoredIntegral hm (show (m : ℝ) ≤ m + h by linarith)).comp_add_left (m : ℝ)
    simpa [suzukiShiftedIntegratedKernel] using h
  rw [anchoredIntegral_eq_shifted]
  calc
    _ ≤ ∫ t in 0..h, epsilon * (t * suzukiShiftedIntegratedKernel m h t) +
        (1 + epsilon) * max (H - t) 0 * suzukiIntegratedKernel (m + h) m := by
      apply intervalIntegral.integral_mono_on hh hi ((htw.const_mul epsilon).add (hb.intervalIntegrable _ _))
      intro t ht
      have hn := shiftedIntegratedKernel_nonneg hm ht
      have hb0 : 0 ≤ (1 + epsilon) * max (H - t) 0 := by positivity
      have hpoint := mul_le_mul_of_nonneg_right (anchoredError_le_twoScale hH hHh he harith ht) hn
      have hdec := mul_le_mul_of_nonneg_left (shiftedIntegratedKernel_le_initial hm ht) hb0
      simp only [suzukiShiftedIntegratedKernel, add_zero] at hdec
      unfold suzukiShiftedIntegratedKernel at hpoint ⊢
      nlinarith
    _ = _ := by
      rw [intervalIntegral.integral_add (htw.const_mul epsilon) (hb.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, integral_shiftedIntegratedKernel_moment hm hh,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_positive_triangle hH.le hHh]

theorem integratedMainTerm_lower {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 ≤ h) :
    h ^ 2 / (2 * ((m : ℝ) + h) * Real.sqrt (m + h)) ≤ suzukiIntegratedMainTerm m (m + h) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hw := continuousOn_shiftedIntegratedKernel hm hh
  rw [← integral_shiftedIntegratedKernel_moment hm hh]
  calc
    _ = ∫ t in 0..h, t * (1 / (((m : ℝ) + h) * Real.sqrt (m + h))) := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      simp
      field_simp
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on hh
        ((continuous_id.mul continuous_const).intervalIntegrable _ _)
        ((continuous_id.continuousOn.mul hw).intervalIntegrable_of_Icc hh)
      intro t ht
      exact mul_le_mul_of_nonneg_left (integratedKernel_ge_terminal (by linarith [ht.1]) (by linarith [ht.2])) ht.1

theorem integratedMainTerm_pos {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 < h) :
    0 < suzukiIntegratedMainTerm m (m + h) := by
  apply lt_of_lt_of_le _ (integratedMainTerm_lower hm hh.le)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem log_one_add_width_le {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 ≤ h) :
    Real.log (((m : ℝ) + h) / m) ≤ h / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : ((m : ℝ) + h) / m - 1 = h / m := by field_simp; ring
  exact he ▸ Real.log_le_sub_one_of_pos (div_pos (by linarith) hm0)

theorem integratedKernel_geometry {m : ℕ} {h : ℝ} (hm : 1 ≤ m)
    (hh : 0 ≤ h) (hhm : h ≤ (m : ℝ) / 8) :
    (((m : ℝ) + h) * Real.sqrt (m + h)) * suzukiIntegratedKernel (m + h) m ≤ 3 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 < (m : ℝ) + h := by linarith
  have hmS := Real.sqrt_pos.mpr hm0
  have hxS := Real.sqrt_pos.mpr hx0
  have hxbound : (m : ℝ) + h ≤ (9 / 8 : ℝ) * m := by linarith
  have hsbound : Real.sqrt (m + h) ≤ (9 / 8 : ℝ) * Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm0.le, Real.sq_sqrt hx0.le]
  have hprod : ((m : ℝ) + h) * Real.sqrt (m + h) ≤ (81 / 64 : ℝ) * (m * Real.sqrt m) := by
    have hp := mul_le_mul hxbound hsbound hxS.le (by positivity : (0 : ℝ) ≤ 9 / 8 * m)
    nlinarith
  have hl := log_one_add_width_le hm hh
  have hfrac : h / (m : ℝ) ≤ 1 / 8 := (div_le_iff₀ hm0).mpr (by linarith)
  have hn : 0 ≤ 1 + (1 / 2 : ℝ) * Real.log (((m : ℝ) + h) / m) := by
    have := Real.log_nonneg ((one_le_div hm0).mpr (by linarith : (m : ℝ) ≤ m + h))
    positivity
  have hb := mul_le_mul hprod (show 1 + (1 / 2 : ℝ) * Real.log (((m : ℝ) + h) / m) ≤ 17 / 16 by linarith)
    hn (by positivity : (0 : ℝ) ≤ 81 / 64 * (m * Real.sqrt m))
  unfold suzukiIntegratedKernel
  rw [← mul_div_assoc, div_le_iff₀ (mul_pos hm0 hmS)]
  nlinarith [mul_pos hm0 hmS]

theorem anchoredIntegral_div_main_le_twoScale {m : ℕ} {H h epsilon : ℝ}
    (hm : 1 ≤ m) (hH : 0 < H) (hHh : H ≤ h) (hhm : h ≤ (m : ℝ) / 8) (he : 0 ≤ epsilon)
    (harith : ∀ t ∈ Icc H h, suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (1 + epsilon) * t) :
    suzukiAnchoredIntegral m (m + h) / suzukiIntegratedMainTerm m (m + h) ≤
      epsilon + (3 / 2 : ℝ) * (1 + epsilon) * (H / h) ^ 2 := by
  have hh : 0 < h := hH.trans_le hHh
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hC := integratedMainTerm_pos hm hh
  have hA : 0 < ((m : ℝ) + h) * Real.sqrt (m + h) := by positivity
  have hw : 0 ≤ suzukiIntegratedKernel (m + h) m := integratedKernel_nonneg hm0 (by linarith)
  have hb := anchoredIntegral_le_twoScale hm hH hHh he harith
  have hl := integratedMainTerm_lower hm hh.le
  have hg := integratedKernel_geometry hm hh.le hhm
  have hB : 0 ≤ (1 + epsilon) * (H ^ 2 / 2) * suzukiIntegratedKernel (m + h) m := by positivity
  calc
    _ ≤ epsilon + ((1 + epsilon) * (H ^ 2 / 2) * suzukiIntegratedKernel (m + h) m) /
        suzukiIntegratedMainTerm m (m + h) := by
      apply (div_le_iff₀ hC).mpr
      field_simp
      nlinarith
    _ ≤ epsilon + ((1 + epsilon) * (H ^ 2 / 2) * suzukiIntegratedKernel (m + h) m) /
        (h ^ 2 / (2 * ((m : ℝ) + h) * Real.sqrt (m + h))) := by
      gcongr
    _ = epsilon + (1 + epsilon) * (H / h) ^ 2 *
        ((((m : ℝ) + h) * Real.sqrt (m + h)) * suzukiIntegratedKernel (m + h) m) := by
      field_simp
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_left hg (show 0 ≤ (1 + epsilon) * (H / h) ^ 2 by positivity)
      nlinarith

theorem anchoredIntegral_le_onePercent_of_twoScale {m : ℕ} {H h : ℝ}
    (hm : 1 ≤ m) (hH : 0 < H) (hHh : H ≤ h) (hhm : h ≤ (m : ℝ) / 8)
    (hratio : H / h ≤ 1 / 20)
    (harith : ∀ t ∈ Icc H h, suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (201 / 200 : ℝ) * t) :
    suzukiAnchoredIntegral m (m + h) ≤ (1403 / 160000 : ℝ) * suzukiIntegratedMainTerm m (m + h) := by
  have hh : 0 < h := hH.trans_le hHh
  have hC := integratedMainTerm_pos hm hh
  have hb := anchoredIntegral_div_main_le_twoScale hm hH hHh hhm (by norm_num : (0 : ℝ) ≤ 1 / 200)
    (by convert harith using 1 <;> norm_num)
  have hs : (H / h) ^ 2 ≤ (1 / 20 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hH.le hh.le) hratio 2
  have hdiv : suzukiAnchoredIntegral m (m + h) / suzukiIntegratedMainTerm m (m + h) ≤ 1403 / 160000 := by
    nlinarith
  exact (div_le_iff₀ hC).mp hdiv

theorem twoScale_coefficient_lt_onePercent : (1403 / 160000 : ℝ) < 1 / 100 := by norm_num

theorem shiftedIntegratedKernel_eq_rpow {m : ℕ} {h t : ℝ} (hm : 1 ≤ m) (ht : 0 ≤ t) :
    suzukiShiftedIntegratedKernel m h t = ((m : ℝ) + t) ^ (-(3 / 2 : ℝ)) *
      (1 + (1 / 2 : ℝ) * Real.log (((m : ℝ) + h) / (m + t))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [suzukiShiftedIntegratedKernel, integratedKernel_eq_rpow (by linarith),
    Real.rpow_neg (by linarith : 0 ≤ (m : ℝ) + t)]
  ring

theorem anchoredIntegral_le_twoScale_explicit {m : ℕ} {H h epsilon : ℝ}
    (hm : 1 ≤ m) (hH : 0 < H) (hHh : H ≤ h) (he : 0 ≤ epsilon)
    (harith : ∀ t ∈ Icc H h, suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (1 + epsilon) * t) :
    suzukiAnchoredIntegral m (m + h) ≤ epsilon * suzukiIntegratedMainTerm m (m + h) +
      (1 + epsilon) * H ^ 2 / (2 * (m : ℝ) ^ (3 / 2 : ℝ)) *
        (1 + (1 / 2 : ℝ) * Real.log (1 + h / m)) := by
  have hb := anchoredIntegral_le_twoScale hm hH hHh he harith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [integratedKernel_eq_rpow hm0] at hb
  have heq : ((m : ℝ) + h) / m = 1 + h / m := by field_simp
  rw [heq] at hb
  convert hb using 1 <;> ring

theorem integratedMainTerm_lower_rpow {m : ℕ} {h : ℝ} (hm : 1 ≤ m) (hh : 0 ≤ h) :
    h ^ 2 / (2 * ((m : ℝ) + h) ^ (3 / 2 : ℝ)) ≤ suzukiIntegratedMainTerm m (m + h) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : ((m : ℝ) + h) ^ (3 / 2 : ℝ) = ((m : ℝ) + h) * Real.sqrt (m + h) := by
    calc
      _ = ((m : ℝ) + h) ^ (1 : ℝ) * ((m : ℝ) + h) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith : 0 < (m : ℝ) + h)]
        norm_num
      _ = _ := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  simpa [hp, mul_assoc] using integratedMainTerm_lower hm hh

/-- 20^15 is only a geometric scale threshold, not an arithmetic PNT threshold. -/
theorem threeFifths_twoThirds_scale {m : ℕ} {h : ℝ}
    (hm : 20 ^ 15 ≤ m) (hh : (m : ℝ) ^ (2 / 3 : ℝ) ≤ h) :
    (m : ℝ) ^ (3 / 5 : ℝ) / h ≤ 1 / 20 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hh0 : 0 < h := (Real.rpow_pos_of_pos hm0 _).trans_le hh
  have hpow : (20 : ℝ) ≤ (m : ℝ) ^ (1 / 15 : ℝ) := by
    have hbase : (20 : ℝ) ^ 15 ≤ m := by exact_mod_cast hm
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 20 ^ 15) hbase (by norm_num : (0 : ℝ) ≤ 1 / 15)
    have he : ((20 : ℝ) ^ 15) ^ (1 / 15 : ℝ) = 20 := by
      rw [← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rwa [he] at h
  have hh' : 20 * (m : ℝ) ^ (3 / 5 : ℝ) ≤ h := by
    have hp := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hm0.le (3 / 5 : ℝ))
    rw [← Real.rpow_add hm0, show (1 / 15 : ℝ) + 3 / 5 = 2 / 3 by norm_num] at hp
    exact hp.trans hh
  apply (div_le_iff₀ hh0).mpr
  linarith

theorem anchoredIntegral_lt_onePercent_of_shortInterval {m : ℕ} {h : ℝ}
    (hm : 20 ^ 15 ≤ m) (hh : (m : ℝ) ^ (2 / 3 : ℝ) ≤ h) (hhm : h ≤ (m : ℝ) / 8)
    (harith : ∀ t ∈ Icc ((m : ℝ) ^ (3 / 5 : ℝ)) ((m : ℝ) / 8),
      suzukiChebyshevPsi (m + t) - suzukiChebyshevPsi m ≤ (201 / 200 : ℝ) * t) :
    suzukiAnchoredIntegral m (m + h) < suzukiIntegratedMainTerm m (m + h) / 100 := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hh0 : 0 < h := (Real.rpow_pos_of_pos hm0 _).trans_le hh
  have hH : 0 < (m : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hm0 _
  have hr := threeFifths_twoThirds_scale hm hh
  have hHh : (m : ℝ) ^ (3 / 5 : ℝ) ≤ h := by
    have := (div_le_iff₀ hh0).mp hr
    linarith
  have hb := anchoredIntegral_le_onePercent_of_twoScale hm1 hH hHh hhm hr
    (fun t ht => harith t ⟨ht.1, ht.2.trans hhm⟩)
  have hc := integratedMainTerm_pos hm1 hh0
  nlinarith [twoScale_coefficient_lt_onePercent]

/-- A fixed density charge scales like sqrt(m), not like a vanishing reserve. -/
theorem integratedMainTerm_fixed_ratio {m : ℕ} {r : ℝ} (hm : 1 ≤ m) (_hr : 0 ≤ r) :
    suzukiIntegratedMainTerm m (m + r * m) = Real.sqrt m *
      (4 * (Real.sqrt (1 + r) - 1) - 2 * Real.log (1 + r)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (m : ℝ) + r * m = m * (1 + r) := by ring
  unfold suzukiIntegratedMainTerm
  rw [he, Real.sqrt_mul hm0.le]
  have hd : (m : ℝ) * (1 + r) / m = 1 + r := by field_simp
  rw [hd]
  ring

end RHGarden
