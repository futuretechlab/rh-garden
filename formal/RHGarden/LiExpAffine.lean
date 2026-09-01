import RHGarden.LiHadamardGrowth
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace RHGarden

/-!
This proof follows the analytic strategy of `ExpPoly.lean` from
`leibniz-rs/PrimeNumberTheoremAnd`, commit
`8dc50485d7166be58b05ee0d54216c06a4b3aef9` (Apache-2.0): integrate
`H'/H`, identify `H` with the exponential of the resulting entire logarithm,
then combine Borel--Caratheodory with Cauchy's estimate.  The implementation
here is native to RH Garden's pinned Mathlib and specializes the last step to
the real exponent `7/4 < 2`, so it concludes affine linearity directly.
-/

/-- A zero-free entire function has a global entire logarithm. -/
theorem zeroFreeEntire_eq_exp_entire {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hzero : ∀ z, H z ≠ 0) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, H z = Complex.exp (k z) := by
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := fun z =>
    ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := fun z => by
    dsimp only [L]
    exact (hderivH z).div (hH z) (hzero z)
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral 0 z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    let R : ℝ := ‖z‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hz : z ∈ ball (0 : ℂ) R := by simp [R, mem_ball, dist_zero_right]
    have hc : Complex.IsConservativeOn L (ball (0 : ℂ) R) :=
      hL.differentiableOn.isConservativeOn
    simpa [h] using hc.hasDerivAt_wedgeIntegral hL.continuous.continuousOn hz
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const _
  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF : Differentiable ℂ F := hk.cexp.div hH hzero
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hk' : HasDerivAt k (L z) z := by
        simpa [k] using (hh_deriv z).add_const (Complex.log (H 0))
      have he := hk'.cexp.div (hH z).hasDerivAt (hzero z)
      rw [show deriv F z =
          ((Complex.exp (k z) * L z) * H z -
            Complex.exp (k z) * deriv H z) / H z ^ 2 by
        change deriv ((fun w => Complex.exp (k w)) / H) z = _
        exact he.deriv]
      have hnum :
          (Complex.exp (k z) * L z) * H z -
            Complex.exp (k z) * deriv H z = 0 := by
        dsimp [L]
        field_simp [hzero z]
        ring
      simp [hnum]
    have hconst : ∀ z, F z = F 0 := fun z =>
      is_const_of_deriv_eq_zero hF hF_deriv z 0
    have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
    have hF0 : F 0 = 1 := by
      simp [F, k, hh0, Complex.exp_log (hzero 0), hzero 0]
    intro z
    have hzF : Complex.exp (k z) / H z = 1 := by
      simpa [F, hF0] using hconst z
    exact (div_eq_one_iff_eq (hzero z)).mp hzF |>.symm
  exact ⟨k, hk, hk_exp⟩

/-- Specialize the common subquadratic growth interface to the fixed exponent
`7/4`. -/
theorem subquadraticGrowth_specialize_seven_fourths {H : ℂ → ℂ}
    (hgrowth : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (7 / 4 : ℝ)) := by
  convert hgrowth (1 / 4) (by norm_num) using 1 <;> norm_num [xiGrowthOrder]

/-- The real part of an entire logarithm inherits the upper growth bound of
its exponential. -/
theorem re_entireLog_le_of_exp_growth {H k : ℂ → ℂ} {C p : ℝ}
    (hzero : ∀ z, H z ≠ 0) (hexp : ∀ z, H z = Complex.exp (k z))
    (hgrowth : ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ p)) :
    ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ p := by
  intro z
  have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr (hzero z)
  have hlog := Real.log_le_log hpos (hgrowth z)
  rw [hexp z, Complex.norm_exp, Real.log_exp, Real.log_exp] at hlog
  exact hlog

/-- Borel--Caratheodory bounds a centered entire logarithm on a half-radius
ball using only an upper bound for its real part. -/
theorem norm_centered_entireLog_le {k : ℂ → ℂ} (hk : Differentiable ℂ k)
    {C : ℝ} (hC : 0 < C)
    (hre : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ (7 / 4 : ℝ))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖k (c + z) - k c‖ ≤
      2 * (C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) + ‖k c‖ + 1) := by
  let f : ℂ → ℂ := fun w => k (c + w) - k c
  let M : ℝ := C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) + ‖k c‖ + 1
  have hf : Differentiable ℂ f :=
    (hk.comp ((differentiable_const c).add differentiable_id)).sub_const _
  have hf0 : f 0 = 0 := by simp [f]
  have hbase : 0 ≤ 1 + ‖c‖ + R := by positivity
  have hM : 0 < M := by
    dsimp [M]
    have : 0 ≤ C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) :=
      mul_nonneg hC.le (Real.rpow_nonneg hbase _)
    positivity
  have hmaps : Set.MapsTo f (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    have hwR : ‖w‖ < R := by simpa [mem_ball, dist_zero_right] using hw
    have hnorm : ‖c + w‖ ≤ ‖c‖ + R :=
      (norm_add_le c w).trans (by linarith)
    have hpow : (1 + ‖c + w‖) ^ (7 / 4 : ℝ) ≤
        (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hk0 : -(k c).re ≤ ‖k c‖ :=
      (neg_le_abs (k c).re).trans (Complex.abs_re_le_norm _)
    dsimp [f, M]
    have := hre (c + w)
    nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]
  have hzball : z ∈ ball (0 : ℂ) R := by
    simp only [mem_ball, dist_zero_right]
    linarith
  have hbc := Complex.borelCaratheodory_zero hM hf.differentiableOn hmaps hR hzball hf0
  dsimp [f] at hbc ⊢
  have hden : R - ‖z‖ > 0 := by
    have : ‖z‖ < R := by linarith
    linarith
  calc
    ‖k (c + z) - k c‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M := by
      apply (div_le_iff₀ hden).2
      have hM0 : 0 ≤ M := hM.le
      nlinarith
    _ = 2 * (C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) + ‖k c‖ + 1) := rfl

/-- The Cauchy estimate and the strict inequality `7/4 < 2` force the second
derivative of the entire logarithm to vanish everywhere. -/
theorem iteratedDeriv_two_eq_zero_of_re_growth {k : ℂ → ℂ}
    (hk : Differentiable ℂ k) {C : ℝ} (hC : 0 < C)
    (hre : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ (7 / 4 : ℝ)) :
    ∀ c : ℂ, iteratedDeriv 2 k c = 0 := by
  intro c
  let f : ℂ → ℂ := fun z => k (c + z) - k c
  have hf : Differentiable ℂ f :=
    (hk.comp ((differentiable_const c).add differentiable_id)).sub_const _
  have hcauchy : ∀ R : ℝ, 0 < R →
      ‖iteratedDeriv 2 f 0‖ ≤
        (2 : ℕ).factorial *
          (2 * (C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) + ‖k c‖ + 1)) /
            (R / 2) ^ 2 := by
    intro R hR
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
      (by positivity) hf.diffContOnCl
    intro z hz
    apply norm_centered_entireLog_le hk hC hre c hR
    have : ‖z‖ = R / 2 := by simpa [mem_sphere, dist_zero_right] using hz
    exact this.le
  let RHS : ℝ → ℝ := fun R =>
    (2 : ℕ).factorial *
      (2 * (C * (1 + ‖c‖ + R) ^ (7 / 4 : ℝ) + ‖k c‖ + 1)) /
        (R / 2) ^ 2
  have hRHS : Tendsto RHS atTop (𝓝 0) := by
    let a : ℝ := 1 + ‖c‖
    let K : ℝ := ‖k c‖ + 1
    have hratioBase : Tendsto (fun R : ℝ => (a + R) / R) atTop (𝓝 1) := by
      have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have heq : (fun R : ℝ => (a + R) / R) =ᶠ[atTop]
          fun R => a * R⁻¹ + 1 := by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR0
        field_simp [hR0]
      exact (tendsto_congr' heq).2 <| by simpa using tendsto_const_nhds.mul hinv |>.add tendsto_const_nhds
    have hratioPow : Tendsto (fun R : ℝ => ((a + R) / R) ^ (7 / 4 : ℝ))
        atTop (𝓝 1) := by
      convert hratioBase.rpow tendsto_const_nhds (Or.inl one_ne_zero) using 1 <;> norm_num
    have hneg : Tendsto (fun R : ℝ => R ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
      convert tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4) using 1 <;>
        ring_nf
    have hmain : Tendsto
        (fun R : ℝ => (a + R) ^ (7 / 4 : ℝ) / (R / 2) ^ 2)
        atTop (𝓝 0) := by
      have heq : (fun R : ℝ => (a + R) ^ (7 / 4 : ℝ) / (R / 2) ^ 2) =ᶠ[atTop]
          fun R => 4 * (((a + R) / R) ^ (7 / 4 : ℝ) * R ^ (-1 / 4 : ℝ)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        have hpq : R ^ (7 / 4 : ℝ) * R ^ (1 / 4 : ℝ) = R ^ 2 := by
          rw [← Real.rpow_add hR]
          norm_num [Real.rpow_two]
        calc
          (a + R) ^ (7 / 4 : ℝ) / (R / 2) ^ 2 =
              4 * ((a + R) ^ (7 / 4 : ℝ) / R ^ 2) := by
                field_simp [hR.ne']
                ring
          _ = 4 * ((a + R) ^ (7 / 4 : ℝ) /
              (R ^ (7 / 4 : ℝ) * R ^ (1 / 4 : ℝ))) := by rw [hpq]
          _ = 4 * (((a + R) / R) ^ (7 / 4 : ℝ) * R ^ (-1 / 4 : ℝ)) := by
                rw [Real.div_rpow (by positivity) hR.le]
                rw [show R ^ (-1 / 4 : ℝ) = (R ^ (1 / 4 : ℝ))⁻¹ by
                  convert Real.rpow_neg hR.le (1 / 4 : ℝ) using 1 <;> ring]
                field_simp [Real.rpow_pos_of_pos hR]
      apply (tendsto_congr' heq).2
      simpa using tendsto_const_nhds.mul (hratioPow.mul hneg)
    have hden : Tendsto (fun R : ℝ => ((R / 2) ^ 2)⁻¹) atTop (𝓝 0) := by
      have ht : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
        tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      have hp : Tendsto (fun R : ℝ => (R / 2) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp ht
      exact hp.inv_tendsto_atTop
    have hbase : Tendsto
        (fun R : ℝ => (C * (a + R) ^ (7 / 4 : ℝ) + K) / (R / 2) ^ 2)
        atTop (𝓝 0) := by
      have h1 : Tendsto
          (fun R : ℝ => C * ((a + R) ^ (7 / 4 : ℝ) / (R / 2) ^ 2))
          atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hmain :
          Tendsto (fun R : ℝ => C * ((a + R) ^ (7 / 4 : ℝ) / (R / 2) ^ 2))
            atTop (𝓝 (C * 0)))
      have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ 2)⁻¹)
          atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hden :
          Tendsto (fun R : ℝ => K * ((R / 2) ^ 2)⁻¹) atTop (𝓝 (K * 0)))
      have hs := h1.add h2
      convert hs using 1
      funext R
      simp only [div_eq_mul_inv]
      ring
      simp
    have hscaled : Tendsto
        (fun R : ℝ => 4 * ((C * (a + R) ^ (7 / 4 : ℝ) + K) / (R / 2) ^ 2))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hbase :
        Tendsto
          (fun R : ℝ => 4 * ((C * (a + R) ^ (7 / 4 : ℝ) + K) / (R / 2) ^ 2))
          atTop (𝓝 (4 * 0)))
    convert hscaled using 1 <;> simp [RHS, a, K, div_eq_mul_inv] <;> ring
  have hf_eq : iteratedDeriv 2 f 0 = iteratedDeriv 2 k c := by
    have hkcd : ContDiffAt ℂ 2 (fun z : ℂ => k (c + z)) 0 :=
      (hk.analyticAt c).comp_of_eq (by fun_prop) (by simp) |>.contDiffAt
    have hconst : ContDiffAt ℂ 2 (fun _ : ℂ => k c) 0 := contDiffAt_const
    rw [show iteratedDeriv 2 f 0 =
        iteratedDeriv 2 (fun z : ℂ => k (c + z)) 0 -
          iteratedDeriv 2 (fun _ : ℂ => k c) 0 by
      change iteratedDeriv 2
          ((fun z : ℂ => k (c + z)) - (fun _ : ℂ => k c)) 0 = _
      exact iteratedDeriv_sub hkcd hconst]
    rw [iteratedDeriv_comp_const_add]
    simp [iteratedDeriv_const]
  rw [← hf_eq]
  by_contra hnz
  have hpos : 0 < ‖iteratedDeriv 2 f 0‖ := norm_pos_iff.mpr hnz
  have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv 2 f 0‖ / 2 :=
    (tendsto_order.1 hRHS).2 _ (half_pos hpos)
  have hbound : ∀ᶠ R in atTop, ‖iteratedDeriv 2 f 0‖ ≤ RHS R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hcauchy R hR
  obtain ⟨R, hle, hlt⟩ := (hbound.and hsmall).exists
  have : ‖iteratedDeriv 2 f 0‖ < ‖iteratedDeriv 2 f 0‖ :=
    (lt_of_le_of_lt hle hlt).trans (half_lt_self hpos)
  exact (lt_irrefl _ this)

/-- An entire function with vanishing second derivative is affine. -/
theorem entire_eq_affine_of_iteratedDeriv_two_eq_zero {k : ℂ → ℂ}
    (hk : Differentiable ℂ k) (h2 : ∀ z, iteratedDeriv 2 k z = 0) :
    ∀ z, k z = k 0 + deriv k 0 * z := by
  have hdk : Differentiable ℂ (deriv k) := fun z =>
    ((hk.analyticAt z).deriv).differentiableAt
  have hderiv2 : ∀ z, deriv (deriv k) z = 0 := by
    intro z
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2 z
  have hconst : ∀ z, deriv k z = deriv k 0 := fun z =>
    is_const_of_deriv_eq_zero hdk hderiv2 z 0
  let g : ℂ → ℂ := fun z => k z - (k 0 + deriv k 0 * z)
  have hg : Differentiable ℂ g := hk.sub
    (differentiable_const (k 0) |>.add (differentiable_const (deriv k 0) |>.mul differentiable_id))
  have hgd : ∀ z, deriv g z = 0 := by
    intro z
    rw [show deriv g z = deriv k z - deriv k 0 by
      apply HasDerivAt.deriv
      exact (hk z).hasDerivAt.sub (by
        convert ((hasDerivAt_id z).const_mul (deriv k 0)).const_add (k 0) using 1 <;>
          simp [mul_comm])]
    simp [hconst z]
  intro z
  have := is_const_of_deriv_eq_zero hg hgd z 0
  exact sub_eq_zero.mp (by simpa [g] using this)

/-- A zero-free entire function of the RH Garden subquadratic growth shape is
the exponential of an affine function. -/
theorem subquadratic_zeroFree_entire_is_exp_affine {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hzero : ∀ z, H z ≠ 0)
    (hgrowth : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))) :
    ∃ A B : ℂ, ∀ z : ℂ, H z = Complex.exp (A + B * z) := by
  obtain ⟨C, hC, hgrowthC⟩ := subquadraticGrowth_specialize_seven_fourths hgrowth
  obtain ⟨k, hk, hexp⟩ := zeroFreeEntire_eq_exp_entire hH hzero
  have hre := re_entireLog_le_of_exp_growth hzero hexp hgrowthC
  have h2 := iteratedDeriv_two_eq_zero_of_re_growth hk hC hre
  have haffine := entire_eq_affine_of_iteratedDeriv_two_eq_zero hk h2
  exact ⟨k 0, deriv k 0, fun z => by rw [hexp z, haffine z]⟩

/-- The formerly open general analytic proposition is now discharged. -/
theorem subquadraticZeroFreeEntireIsExpAffine :
    SubquadraticZeroFreeEntireIsExpAffine := by
  intro H hH hzero hgrowth
  exact subquadratic_zeroFree_entire_is_exp_affine hH hzero hgrowth

end RHGarden
