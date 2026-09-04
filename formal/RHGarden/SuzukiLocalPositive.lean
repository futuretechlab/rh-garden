import RHGarden.SuzukiTriangle
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section

set_option maxHeartbeats 800000

open Complex Filter Function Set
open scoped BigOperators Topology

namespace RHGarden

/-! ## The prime-free derivative of Suzuki's function -/

/-- The constant regular term in the derivative of the archimedean side,
kept in the exact normalization supplied by the pinned explicit formula. -/
noncomputable def suzukiPsiDerivativeConstant : ℝ :=
  1 / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
    Real.pi / 2

/-- The closed derivative expression on the first, prime-free interval. -/
noncomputable def suzukiPsiPrimeFreeDerivative (t : ℝ) : ℝ :=
  2 * (Real.exp (t / 2) - Real.exp (-t / 2)) +
    suzukiPsiDerivativeConstant -
    Real.arctan (Real.exp (t / 2)) +
    Real.artanh (Real.exp (-t / 2))

private noncomputable def suzukiQuarterIncrement (n : ℕ) (t : ℝ) : ℝ :=
  let a := (n : ℝ) + 1 / 4
  (1 / a ^ 2) * (1 - Real.exp (-2 * a * t))

private noncomputable def suzukiQuarterDerivative (n : ℕ) (t : ℝ) : ℝ :=
  let a := (n : ℝ) + 1 / 4
  (2 / a) * Real.exp (-2 * a * t)

private theorem summable_quarter_reciprocal_sq :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
  rw [show (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 / 4) ^ 2) =
      fun n : ℕ ↦ 1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ) by
    funext n
    simp [sq_abs]]
  exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).mpr (by norm_num)

private theorem summable_suzukiQuarterIncrement {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ ↦ suzukiQuarterIncrement n t) := by
  have hb := summable_quarter_reciprocal_sq
  have hbe : Summable (fun n : ℕ ↦
      (1 / ((n : ℝ) + 1 / 4) ^ 2) *
        Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) := by
    exact Summable.of_nonneg_of_le
      (fun n ↦ by positivity)
      (fun n ↦ by
        have he : Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have ha : 0 ≤ (n : ℝ) + 1 / 4 := by positivity
          have hat : 0 ≤ ((n : ℝ) + 1 / 4) * t := mul_nonneg ha ht
          nlinarith
        exact mul_le_of_le_one_right (by positivity) he)
      hb
  exact (hb.sub hbe).congr (fun n ↦ by
    unfold suzukiQuarterIncrement
    ring)

private theorem hasDerivAt_suzukiQuarterIncrement (n : ℕ) (t : ℝ) :
    HasDerivAt (suzukiQuarterIncrement n) (suzukiQuarterDerivative n t) t := by
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : a ≠ 0 := by positivity
  have hlin : HasDerivAt (fun y : ℝ ↦ -2 * a * y) (-2 * a) t := by
    exact hasDerivAt_const_mul (-2 * a)
  have hexp := hlin.exp
  have hone : HasDerivAt (fun y : ℝ ↦ 1 - Real.exp (-2 * a * y))
      (- (Real.exp (-2 * a * t) * (-2 * a))) t :=
    hexp.const_sub 1
  have h := hone.const_mul (1 / a ^ 2)
  have hcoeff : (1 / a ^ 2) *
      -(Real.exp (-2 * a * t) * (-2 * a)) =
      (2 / a) * Real.exp (-2 * a * t) := by
    field_simp [ha]
  change HasDerivAt
    (fun y : ℝ ↦ (1 / a ^ 2) * (1 - Real.exp (-2 * a * y)))
    ((2 / a) * Real.exp (-2 * a * t)) t
  rwa [← hcoeff]

private theorem summable_suzukiQuarterDerivative_bound {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦
      8 * Real.exp (-t / 4) * Real.exp ((n : ℝ) * (-t))) := by
  exact (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _

private theorem hasDerivAt_tsum_suzukiQuarterIncrement {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun y : ℝ ↦ ∑' n : ℕ, suzukiQuarterIncrement n y)
      (∑' n : ℕ, suzukiQuarterDerivative n t) t := by
  let u : ℕ → ℝ := fun n ↦
    8 * Real.exp (-t / 4) * Real.exp ((n : ℝ) * (-t))
  apply hasDerivAt_tsum_of_isPreconnected
      (u := u) (t := Ioi (t / 2)) (y₀ := t)
  · exact summable_suzukiQuarterDerivative_bound ht
  · exact isOpen_Ioi
  · exact ordConnected_Ioi.isPreconnected
  · intro n y hy
    simp only [mem_Ioi] at hy
    exact hasDerivAt_suzukiQuarterIncrement n y
  · intro n y hy
    simp only [mem_Ioi] at hy
    have ha : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
    have hyt : t < 2 * y := by linarith
    have hexp : Real.exp (-2 * ((n : ℝ) + 1 / 4) * y) ≤
        Real.exp (-((n : ℝ) + 1 / 4) * t) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hfrac : 2 / ((n : ℝ) + 1 / 4) ≤ 8 := by
      apply (div_le_iff₀ ha).mpr
      nlinarith
    have hnonneg : 0 ≤ 2 / ((n : ℝ) + 1 / 4) := by positivity
    rw [show u n = 8 * Real.exp (-((n : ℝ) + 1 / 4) * t) by
      unfold u
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring]
    simp only [suzukiQuarterDerivative, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hnonneg (Real.exp_nonneg _))]
    exact (mul_le_mul hfrac hexp (Real.exp_nonneg _) (by norm_num)).trans_eq
      (by ring)
  · simp only [mem_Ioi]
    linarith
  · exact summable_suzukiQuarterIncrement ht.le
  · simp only [mem_Ioi]
    linarith

private theorem hasSum_artanh {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ ↦ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      (Real.artanh x) := by
  have hlog := Real.hasSum_log_sub_log_of_abs_lt_one
    (show |x| < 1 by simpa [abs_of_nonneg hx0] using hx1)
  have h := hlog.mul_left (1 / 2 : ℝ)
  have hfun : (fun n : ℕ ↦ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) =
      (fun n : ℕ ↦ 1 / 2 *
        (2 * (1 / (2 * (n : ℝ) + 1)) * x ^ (2 * n + 1))) := by
    funext n
    push_cast
    ring
  rw [hfun]
  rw [Real.artanh_eq_half_log (by constructor <;> linarith),
    Real.log_div (by linarith) (by linarith)]
  exact h

private theorem hasSum_quarter_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ ↦ 2 * x ^ (4 * n + 1) / (4 * n + 1 : ℝ))
      (Real.artanh x + Real.arctan x) := by
  let f : ℕ → ℝ := fun n ↦
    x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) +
      (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)
  have hfull : HasSum f (Real.artanh x + Real.arctan x) := by
    exact (hasSum_artanh hx0 hx1).add
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0]))
  have he : Summable (fun n : ℕ ↦ f (2 * n)) :=
    hfull.summable.comp_injective (fun _ _ h ↦ by omega)
  have ho : HasSum (fun n : ℕ ↦ f (2 * n + 1)) 0 := by
    have hzero : (fun n : ℕ ↦ f (2 * n + 1)) = fun _ : ℕ ↦ (0 : ℝ) := by
      funext n
      dsimp only [f]
      rw [Odd.neg_one_pow (show Odd (2 * n + 1) by exact ⟨n, by omega⟩)]
      push_cast
      ring
    rw [hzero]
    exact hasSum_zero
  have hall := he.hasSum.even_add_odd ho
  have heq : (∑' n : ℕ, f (2 * n)) = Real.artanh x + Real.arctan x := by
    simpa using hall.unique hfull
  have hev : HasSum (fun n : ℕ ↦ f (2 * n))
      (Real.artanh x + Real.arctan x) := by
    rw [← heq]
    exact he.hasSum
  convert hev using 1
  ext n
  simp only [f]
  push_cast
  rw [Even.neg_one_pow (show Even (2 * n) by exact ⟨n, by omega⟩)]
  ring

private theorem tsum_suzukiQuarterDerivative_eq {t : ℝ} (ht : 0 < t) :
    (1 / 4 : ℝ) * (∑' n : ℕ, suzukiQuarterDerivative n t) =
      Real.artanh (Real.exp (-t / 2)) +
        Real.arctan (Real.exp (-t / 2)) := by
  let x := Real.exp (-t / 2)
  have hx0 : 0 ≤ x := Real.exp_nonneg _
  have hx1 : x < 1 := by
    unfold x
    rw [Real.exp_lt_one_iff]
    linarith
  rw [← (hasSum_quarter_exp hx0 hx1).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp only [suzukiQuarterDerivative]
  unfold x
  have ha : (0 : ℝ) < n + 1 / 4 := by positivity
  rw [show Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) =
      Real.exp (-t / 2) ^ (4 * n + 1) by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring]
  field_simp

private theorem hasDerivAt_suzukiPsiArchimedean {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPsiArchimedean (suzukiPsiPrimeFreeDerivative t) t := by
  let S : ℝ → ℝ := fun y ↦ ∑' n : ℕ, suzukiQuarterIncrement n y
  have hS : HasDerivAt S (∑' n : ℕ, suzukiQuarterDerivative n t) t :=
    hasDerivAt_tsum_suzukiQuarterIncrement ht
  let E : ℝ → ℝ := fun y ↦
    4 * (Real.exp (y / 2) + Real.exp (-y / 2) - 2) +
      y / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
      1 / 4 * S y
  have hfirst : HasDerivAt
      (fun y : ℝ ↦ 4 *
        (Real.exp (y / 2) + Real.exp (-y / 2) - 2))
      (2 * (Real.exp (t / 2) - Real.exp (-t / 2))) t := by
    have hp := (hasDerivAt_const_mul (1 / 2 : ℝ) (x := t)).exp
    have hn := (hasDerivAt_const_mul (-1 / 2 : ℝ) (x := t)).exp
    have h := (hp.add hn).sub_const 2 |>.const_mul 4
    rw [show (fun y : ℝ ↦ 4 *
        (Real.exp (y / 2) + Real.exp (-y / 2) - 2)) =
        (fun y : ℝ ↦ 4 *
          (((fun x : ℝ ↦ Real.exp (1 / 2 * x)) +
            fun x : ℝ ↦ Real.exp (-1 / 2 * x)) y - 2)) by
      funext y
      dsimp only [Pi.add_apply]
      ring]
    exact h.congr_deriv (by ring)
  have hsecond : HasDerivAt
      (fun y : ℝ ↦ y / 2 *
        ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi))
      (1 / 2 *
        ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi)) t := by
    let D : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
    have h := hasDerivAt_mul_const (D / 2) (x := t)
    rw [show (fun y : ℝ ↦ y / 2 *
        ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi)) =
        (fun y : ℝ ↦ y * (D / 2)) by
      funext y
      unfold D
      ring]
    apply h.congr_deriv
    unfold D
    ring
  have hthird : HasDerivAt (fun y : ℝ ↦ 1 / 4 * S y)
      (1 / 4 * (∑' n : ℕ, suzukiQuarterDerivative n t)) t :=
    hS.const_mul (1 / 4)
  have hE : HasDerivAt E
      (2 * (Real.exp (t / 2) - Real.exp (-t / 2)) +
        1 / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        1 / 4 * (∑' n : ℕ, suzukiQuarterDerivative n t)) t := by
    exact hfirst.add hsecond |>.add hthird
  have hEA : E =ᶠ[nhds t] suzukiPsiArchimedean := by
    filter_upwards [eventually_gt_nhds ht] with y hy
    unfold E S suzukiPsiArchimedean
    simp only [suzukiQuarterIncrement]
    rw [tsum_quarter_reciprocal_sq_one_sub_exp hy.le]
  have harch := hE.congr_of_eventuallyEq hEA.symm
  rw [tsum_suzukiQuarterDerivative_eq ht] at harch
  have hatan : Real.arctan (Real.exp (-t / 2)) =
      Real.pi / 2 - Real.arctan (Real.exp (t / 2)) := by
    have hpos : 0 < Real.exp (-t / 2) := Real.exp_pos _
    have h := Real.arctan_inv_of_pos hpos
    rw [show (Real.exp (-t / 2))⁻¹ = Real.exp (t / 2) by
      rw [← Real.exp_neg]
      congr 1
      ring] at h
    linarith
  rw [hatan] at harch
  have hcoeff : suzukiPsiPrimeFreeDerivative t =
      2 * (Real.exp (t / 2) - Real.exp (-t / 2)) +
        1 / 2 * ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) +
        (Real.artanh (Real.exp (-t / 2)) +
          (Real.pi / 2 - Real.arctan (Real.exp (t / 2)))) := by
    unfold suzukiPsiPrimeFreeDerivative suzukiPsiDerivativeConstant
    ring
  rw [hcoeff]
  exact harch

/-- Exact derivative formula for Suzuki's zero/prime-side function before
the first prime enters the explicit formula. -/
theorem hasDerivAt_suzukiPsi_primeFree {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt suzukiPsi (suzukiPsiPrimeFreeDerivative t) t := by
  have harch := hasDerivAt_suzukiPsiArchimedean ht0
  apply harch.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht0, eventually_lt_nhds ht2] with y hy0 hy2
  exact suzukiPsi_eq_archimedean_of_lt_log_two hy0.le hy2

/-! ## Divergence of the singular term and positivity -/

/-- The regular (finite-limit) part of the prime-free derivative. -/
noncomputable def suzukiPsiPrimeFreeDerivativeRegular (t : ℝ) : ℝ :=
  2 * (Real.exp (t / 2) - Real.exp (-t / 2)) +
    suzukiPsiDerivativeConstant - Real.arctan (Real.exp (t / 2))

theorem continuous_suzukiPsiPrimeFreeDerivativeRegular :
    Continuous suzukiPsiPrimeFreeDerivativeRegular := by
  unfold suzukiPsiPrimeFreeDerivativeRegular
  fun_prop

/-- The inverse-hyperbolic-tangent term in Suzuki's derivative diverges
to `+∞` as the prime-free variable approaches zero from the right. -/
theorem tendsto_artanh_exp_neg_half_at_zero :
    Tendsto
      (fun t : ℝ ↦ Real.artanh (Real.exp (-t / 2)))
      (nhdsWithin 0 (Ioi 0)) atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-t / 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa only [zero_div, neg_zero, Real.exp_zero] using
        (show ContinuousAt (fun t : ℝ ↦ Real.exp (-t / 2)) 0 by fun_prop).tendsto)
  have hgt : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      Real.tanh b < Real.exp (-t / 2) :=
    hexp.eventually (eventually_gt_nhds (Real.tanh_lt_one b))
  filter_upwards [hgt, self_mem_nhdsWithin] with t htx ht0
  simp only [mem_Ioi] at ht0
  have hx1 : Real.exp (-t / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  exact le_of_lt <| calc
    b = Real.artanh (Real.tanh b) := (Real.artanh_tanh b).symm
    _ < Real.artanh (Real.exp (-t / 2)) :=
      Real.artanh_lt_artanh (Real.neg_one_lt_tanh b) hx1 htx

/-- The nonsingular part of the derivative is bounded on some neighborhood
of zero. -/
theorem exists_bound_suzukiPsiPrimeFreeDerivativeRegular :
    ∃ M δ : ℝ, 0 < δ ∧ 0 ≤ M ∧
      ∀ t : ℝ, |t| < δ →
        |suzukiPsiPrimeFreeDerivativeRegular t| ≤ M := by
  have hcont : ContinuousAt suzukiPsiPrimeFreeDerivativeRegular 0 :=
    continuous_suzukiPsiPrimeFreeDerivativeRegular.continuousAt
  have hevent : ∀ᶠ t in nhds (0 : ℝ),
      |suzukiPsiPrimeFreeDerivativeRegular t -
        suzukiPsiPrimeFreeDerivativeRegular 0| < 1 := by
    simpa only [Real.dist_eq] using
      hcont.tendsto.eventually (Metric.eventually_nhds_iff.mpr
        ⟨1, by norm_num, by intro y hy; simpa [Real.dist_eq] using hy⟩)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨δ, hδ, hsub⟩
  refine ⟨|suzukiPsiPrimeFreeDerivativeRegular 0| + 1, δ, hδ,
    by positivity, ?_⟩
  intro t ht
  have hdiff := hsub (by simpa [Real.dist_eq] using ht)
  change |suzukiPsiPrimeFreeDerivativeRegular t -
    suzukiPsiPrimeFreeDerivativeRegular 0| < 1 at hdiff
  calc
    |suzukiPsiPrimeFreeDerivativeRegular t| =
        |(suzukiPsiPrimeFreeDerivativeRegular t -
          suzukiPsiPrimeFreeDerivativeRegular 0) +
            suzukiPsiPrimeFreeDerivativeRegular 0| := by ring
    _ ≤
        |suzukiPsiPrimeFreeDerivativeRegular t -
          suzukiPsiPrimeFreeDerivativeRegular 0| +
            |suzukiPsiPrimeFreeDerivativeRegular 0| := abs_add_le _ _
    _ ≤ |suzukiPsiPrimeFreeDerivativeRegular 0| + 1 := by linarith

theorem tendsto_suzukiPsiPrimeFreeDerivative_at_zero :
    Tendsto suzukiPsiPrimeFreeDerivative
      (nhdsWithin 0 (Ioi 0)) atTop := by
  have hreg : Tendsto suzukiPsiPrimeFreeDerivativeRegular
      (nhdsWithin 0 (Ioi 0))
      (nhds (suzukiPsiPrimeFreeDerivativeRegular 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      continuous_suzukiPsiPrimeFreeDerivativeRegular.continuousAt.tendsto
  have hsum := tendsto_artanh_exp_neg_half_at_zero.atTop_add hreg
  apply hsum.congr'
  filter_upwards with t
  unfold suzukiPsiPrimeFreeDerivative suzukiPsiPrimeFreeDerivativeRegular
  ring

/-- An explicit punctured interval on which the prime-free derivative is
strictly positive. The endpoint is also chosen below the first prime. -/
theorem exists_suzukiPsi_deriv_pos_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.log 2 ∧
      ∀ t : ℝ, 0 < t → t < δ → 0 < deriv suzukiPsi t := by
  have hevent : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      0 < suzukiPsiPrimeFreeDerivative t := by
    have hge := tendsto_atTop.1
      tendsto_suzukiPsiPrimeFreeDerivative_at_zero 1
    filter_upwards [hge] with t ht
    linarith
  rcases Metric.mem_nhdsWithin_iff.mp hevent with ⟨ε, hε, hsub⟩
  let δ : ℝ := min (ε / 2) (Real.log 2 / 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by
    unfold δ
    positivity
  have hδlog : δ < Real.log 2 := by
    unfold δ
    exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδlog, ?_⟩
  intro t ht0 htδ
  have htεhalf : t < ε / 2 := htδ.trans_le (min_le_left _ _)
  have htε : t < ε := by linarith
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq, abs_of_pos ht0] using htε
  have hvalue : 0 < suzukiPsiPrimeFreeDerivative t :=
    hsub ⟨hball, ht0⟩
  rw [(hasDerivAt_suzukiPsi_primeFree ht0 (htδ.trans hδlog)).deriv]
  exact hvalue

/-- Suzuki's `Psi` is strictly increasing on a nontrivial interval to the
right of the origin. -/
theorem strictMonoOn_suzukiPsi_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ StrictMonoOn suzukiPsi (Icc 0 δ) := by
  rcases exists_suzukiPsi_deriv_pos_near_zero with
    ⟨δ, hδ, hδlog, hderiv⟩
  refine ⟨δ, hδ, strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
    continuous_suzukiPsi.continuousOn ?_⟩
  intro t ht
  rw [interior_Icc] at ht
  exact hderiv t ht.1 ht.2

/-- Unconditional strict positivity of Suzuki's function on some punctured
neighborhood of the origin. -/
theorem exists_suzukiPsi_pos_near_zero :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → 0 < suzukiPsi t := by
  rcases strictMonoOn_suzukiPsi_near_zero with ⟨δ, hδ, hmono⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have hlt := hmono (by exact ⟨le_rfl, hδ.le⟩)
    (by exact ⟨ht0.le, htδ.le⟩) ht0
  simpa only [suzukiPsi_zero] using hlt

/-- Local, symmetric nonnegativity of Suzuki's even function. -/
def SuzukiPsiNonnegativeOn (a : ℝ) : Prop :=
  ∀ t : ℝ, |t| ≤ a → 0 ≤ suzukiPsi t

theorem exists_suzukiPsi_nonnegativeOn :
    ∃ a : ℝ, 0 < a ∧ SuzukiPsiNonnegativeOn a := by
  rcases exists_suzukiPsi_pos_near_zero with ⟨δ, hδ, hpos⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simp
  have habs0 : 0 < |t| := abs_pos.mpr ht0
  have habsδ : |t| < δ := ht.trans_lt (by linarith)
  have hp : 0 < suzukiPsi |t| := hpos |t| habs0 habsδ
  by_cases htn : 0 ≤ t
  · simpa [abs_of_nonneg htn] using hp.le
  · have heven := suzukiPsi_neg t
    rw [abs_of_neg (lt_of_not_ge htn)] at hp
    rw [heven] at hp
    exact hp.le

/-- The screw kernel has an unconditionally nonnegative diagonal on a
nontrivial symmetric interval. This is diagonal positivity, not `KernelPSD`. -/
theorem exists_riemannScrewKernel_diagonal_nonneg :
    ∃ a : ℝ, 0 < a ∧
      ∀ t : ℝ, |t| ≤ a → 0 ≤ (riemannScrewKernel t t).re := by
  rcases exists_suzukiPsi_nonnegativeOn with ⟨a, ha, hpsi⟩
  refine ⟨a, ha, ?_⟩
  intro t ht
  have hpsi0 := hpsi t ht
  rw [riemannScrewKernel_self]
  norm_num
  linarith

end RHGarden
