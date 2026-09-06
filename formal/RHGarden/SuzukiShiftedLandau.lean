import RHGarden.SuzukiShiftTransform
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology Interval

namespace RHGarden

/-! ## Compact tails for eventually nonnegative Laplace transforms -/

/-- The translate of `f` whose nonnegative half-line is the tail of `f`
starting at `T`. -/
def laplaceTail (f : ℝ → ℝ) (T u : ℝ) : ℝ :=
  f (u + T)

theorem continuous_laplaceTail {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    Continuous (laplaceTail f T) := by
  exact hf.comp (continuous_id.add continuous_const)

theorem laplaceTail_nonneg_of_eventually_nonneg {f : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t : ℝ, T ≤ t → 0 ≤ f t) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ laplaceTail f T u := by
  exact hf (u + T) (by linarith)

/-- The compact initial part of a one-sided Laplace transform. -/
noncomputable def compactLaplaceInitial (f : ℝ → ℝ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..T,
    (f t : ℂ) * Complex.exp (-w * (t : ℂ))

/-- A finite initial segment has an entire Laplace transform. -/
theorem differentiable_compactLaplaceInitial {f : ℝ → ℝ}
    (hf : Continuous f) (T : ℝ) :
    Differentiable ℂ (compactLaplaceInitial f T) := by
  intro w
  let F : ℂ → ℝ → ℂ := fun z t =>
    (f t : ℂ) * Complex.exp (-z * (t : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (f t : ℂ) *
      (Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)))
  let C : ℝ := (‖w‖ + 1) * |T|
  let bound : ℝ → ℝ := fun t => |f t| * (Real.exp C * |T|)
  have hFmeas : ∀ᶠ z in 𝓝 w,
      AEStronglyMeasurable (F z)
        (volume.restrict (Ι (0 : ℝ) T)) := by
    filter_upwards with z
    exact ((Complex.continuous_ofReal.comp hf).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  have hFint : IntervalIntegrable (F w) volume 0 T := by
    exact ((Complex.continuous_ofReal.comp hf).mul
      (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable 0 T
  have hF'meas : AEStronglyMeasurable (F' w)
      (volume.restrict (Ι (0 : ℝ) T)) := by
    exact (((Complex.continuous_ofReal.comp hf).mul
      ((Complex.continuous_exp.comp (by fun_prop)).mul
        Complex.continuous_ofReal.neg))).aestronglyMeasurable
  have hbound : IntervalIntegrable bound volume 0 T := by
    apply Continuous.intervalIntegrable
    dsimp [bound]
    fun_prop
  have hmajor : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) T →
      ∀ z ∈ Metric.ball w 1, ‖F' z t‖ ≤ bound t := by
    filter_upwards with t ht z hz
    have htAbs : |t| ≤ |T| := by
      rcases (mem_uIoc.mp ht) with h | h
      · have ht0 : 0 ≤ t := h.1.le
        have htT : t ≤ T := h.2
        have hT0 : 0 ≤ T := ht0.trans htT
        simpa [abs_of_nonneg ht0, abs_of_nonneg hT0] using htT
      · have hTt : T ≤ t := h.1.le
        have ht0 : t ≤ 0 := h.2
        have hT0 : T ≤ 0 := hTt.trans ht0
        have habs : -t ≤ -T := neg_le_neg hTt
        simpa [abs_of_nonpos ht0, abs_of_nonpos hT0] using habs
    have hzw : ‖z - w‖ < 1 := by simpa [dist_eq_norm] using hz
    have hzNorm : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      calc
        ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
    have hzRe : |z.re| ≤ ‖w‖ + 1 := by
      calc
        |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        _ ≤ ‖z - w‖ + ‖w‖ := hzNorm
        _ ≤ ‖w‖ + 1 := by linarith
    have hexp : -z.re * t ≤ C := by
      dsimp [C]
      calc
        -z.re * t ≤ |-z.re * t| := le_abs_self _
        _ = |z.re| * |t| := by rw [abs_mul, abs_neg]
        _ ≤ (‖w‖ + 1) * |T| := by gcongr
    dsimp [F', bound]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      norm_neg]
    calc
      |f t| * (Real.exp (-z.re * t) * |t|) ≤
          |f t| * (Real.exp C * |T|) := by
        gcongr
      _ = |f t| * (Real.exp C * |T|) := rfl
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) T →
      ∀ z ∈ Metric.ball w 1,
        HasDerivAt (fun z => F z t) (F' z t) z := by
    filter_upwards with t ht z hz
    have hinner : HasDerivAt
        (fun u : ℂ => -u * (t : ℂ)) (-(t : ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (t : ℂ)
    have hexp := hinner.cexp
    dsimp [F, F']
    exact hexp.const_mul (f t : ℂ)
  have hderiv := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w zero_lt_one) hFmeas hFint hF'meas
    hmajor hbound hdiff
  exact hderiv.2.differentiableAt

/-- Translating the tail changes its Laplace transform by the expected
exponential factor. -/
theorem integral_laplaceTail_eq_exp_mul_tail
    (f : ℝ → ℝ) (T : ℝ) (w : ℂ) :
    (∫ u : ℝ in Ioi 0,
        (laplaceTail f T u : ℂ) *
          Complex.exp (-w * (u : ℂ))) =
      Complex.exp (w * (T : ℂ)) *
        ∫ t : ℝ in Ioi T,
          (f t : ℂ) * Complex.exp (-w * (t : ℂ)) := by
  let shift : ℝ → ℝ := fun u => u + T
  let g : ℝ → ℂ := fun t =>
    (f t : ℂ) * Complex.exp (-w * ((t - T : ℝ) : ℂ))
  have hmp := (measurePreserving_add_right volume T).restrict_preimage_emb
    (measurableEmbedding_addRight T) (Ioi T)
  have hpre : shift ⁻¹' Ioi T = Ioi 0 := by
    dsimp [shift]
    rw [preimage_add_const_Ioi]
    simp
  have hint : (∫ u : ℝ in Ioi 0, g (shift u)) =
      ∫ t : ℝ in Ioi T, g t := by
    rw [← hpre]
    exact hmp.integral_comp (measurableEmbedding_addRight T) g
  calc
    (∫ u : ℝ in Ioi 0,
        (laplaceTail f T u : ℂ) * Complex.exp (-w * (u : ℂ))) =
        ∫ u : ℝ in Ioi 0, g (shift u) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      dsimp [laplaceTail, shift, g]
      congr 2
      push_cast
      ring
    _ = ∫ t : ℝ in Ioi T, g t := hint
    _ = ∫ t : ℝ in Ioi T,
        Complex.exp (w * (T : ℂ)) *
          ((f t : ℂ) * Complex.exp (-w * (t : ℂ))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      dsimp [g]
      have hexp :
          Complex.exp (-w * ((t - T : ℝ) : ℂ)) =
            Complex.exp (w * (T : ℂ)) *
              Complex.exp (-w * (t : ℂ)) := by
        rw [← Complex.exp_add]
        push_cast
        congr 2
        ring
      rw [hexp]
      ring
    _ = Complex.exp (w * (T : ℂ)) *
        ∫ t : ℝ in Ioi T,
          (f t : ℂ) * Complex.exp (-w * (t : ℂ)) := by
      rw [MeasureTheory.integral_const_mul]

/-- The original tail transform in the orientation used by the compact
initial-segment decomposition. -/
theorem integral_tail_eq_exp_neg_mul_laplaceTail
    (f : ℝ → ℝ) (T : ℝ) (w : ℂ) :
    (∫ t : ℝ in Ioi T,
        (f t : ℂ) * Complex.exp (-w * (t : ℂ))) =
      Complex.exp (-w * (T : ℂ)) *
        ∫ u : ℝ in Ioi 0,
          (laplaceTail f T u : ℂ) *
            Complex.exp (-w * (u : ℂ)) := by
  rw [integral_laplaceTail_eq_exp_mul_tail]
  conv_rhs =>
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  simp only [neg_mul]

private noncomputable def laplaceKernel
    (f : ℝ → ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (f t : ℂ) * Complex.exp (-w * (t : ℂ))

/-- Integrability of a translated tail is equivalent to integrability of
the original Laplace kernel beyond the translation point. -/
theorem laplaceConvergesAt_laplaceTail_iff
    (f : ℝ → ℝ) (T σ : ℝ) :
    laplaceConvergesAt (laplaceTail f T) σ ↔
      IntegrableOn (laplaceKernel f (σ : ℂ)) (Ioi T) := by
  let shift : ℝ → ℝ := fun u => u + T
  let g : ℝ → ℂ := fun t =>
    (f t : ℂ) * Complex.exp (-(σ : ℂ) * ((t - T : ℝ) : ℂ))
  have hmp := (measurePreserving_add_right volume T).restrict_preimage_emb
    (measurableEmbedding_addRight T) (Ioi T)
  have hpre : shift ⁻¹' Ioi T = Ioi 0 := by
    dsimp [shift]
    rw [preimage_add_const_Ioi]
    simp
  have hiff : Integrable (g ∘ shift) (volume.restrict (Ioi 0)) ↔
      Integrable g (volume.restrict (Ioi T)) := by
    rw [← hpre]
    exact hmp.integrable_comp_emb (measurableEmbedding_addRight T)
  have hcomp : (g ∘ shift) = fun u : ℝ =>
      (laplaceTail f T u : ℂ) *
        Complex.exp (-(σ : ℂ) * (u : ℂ)) := by
    funext u
    dsimp [g, shift, laplaceTail]
    congr 2
    push_cast
    ring
  let c : ℂ := Complex.exp ((σ : ℂ) * (T : ℂ))
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hg : g = fun t : ℝ => c * laplaceKernel f (σ : ℂ) t := by
    funext t
    dsimp [g, c, laplaceKernel]
    have hexp :
        Complex.exp (-(σ : ℂ) * ((t - T : ℝ) : ℂ)) =
          Complex.exp ((σ : ℂ) * (T : ℂ)) *
            Complex.exp (-(σ : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      push_cast
      congr 2
      ring
    rw [hexp]
    ring
  change Integrable
      (fun u : ℝ => (laplaceTail f T u : ℂ) *
        Complex.exp (-(σ : ℂ) * (u : ℂ)))
      (volume.restrict (Ioi 0)) ↔ _
  rw [← hcomp, hiff, hg]
  constructor
  · intro h
    have h' := h.const_mul c⁻¹
    apply h'.congr
    filter_upwards with t
    dsimp [laplaceKernel]
    field_simp [hc]
  · intro h
    exact h.const_mul c

/-- Splitting the one-sided Laplace integral at a nonnegative point gives
the compact initial transform plus the translated tail. -/
theorem complexLaplaceIntegral_eq_compactInitial_add_tail
    {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T)
    {w : ℂ}
    (hfull : IntegrableOn (laplaceKernel f w) (Ioi 0)) :
    complexLaplaceIntegral f w =
      compactLaplaceInitial f T w +
        Complex.exp (-w * (T : ℂ)) *
          complexLaplaceIntegral (laplaceTail f T) w := by
  have hinit : IntegrableOn (laplaceKernel f w) (Ioc 0 T) := by
    have hc : Continuous (laplaceKernel f w) := by
      unfold laplaceKernel
      fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have htail : IntegrableOn (laplaceKernel f w) (Ioi T) :=
    hfull.mono_set (fun t ht => lt_of_le_of_lt hT ht)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    hinit htail
  rw [Ioc_union_Ioi_eq_Ioi hT] at hsplit
  have hsplit' :
      (∫ t : ℝ in Ioi 0,
          (f t : ℂ) * Complex.exp (-w * (t : ℂ))) =
        (∫ t : ℝ in Ioc 0 T,
          (f t : ℂ) * Complex.exp (-w * (t : ℂ))) +
        ∫ t : ℝ in Ioi T,
          (f t : ℂ) * Complex.exp (-w * (t : ℂ)) := by
    simpa [laplaceKernel] using hsplit
  rw [complexLaplaceIntegral, compactLaplaceInitial,
    intervalIntegral.integral_of_le hT]
  rw [hsplit', integral_tail_eq_exp_neg_mul_laplaceTail]
  rfl

/-- Tail convergence together with continuity recovers convergence of the
whole one-sided transform; the omitted initial segment is compact. -/
theorem laplaceConvergesAt_of_laplaceTail
    {f : ℝ → ℝ} (hf : Continuous f) {T σ : ℝ} (hT : 0 ≤ T)
    (htail : laplaceConvergesAt (laplaceTail f T) σ) :
    laplaceConvergesAt f σ := by
  have htail' : IntegrableOn (laplaceKernel f (σ : ℂ)) (Ioi T) :=
    (laplaceConvergesAt_laplaceTail_iff f T σ).mp htail
  have hinit : IntegrableOn (laplaceKernel f (σ : ℂ)) (Ioc 0 T) := by
    have hc : Continuous (laplaceKernel f (σ : ℂ)) := by
      unfold laplaceKernel
      fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hunion := hinit.union htail'
  rw [Ioc_union_Ioi_eq_Ioi hT] at hunion
  exact hunion

theorem laplaceConvergesAt_laplaceTail_of_convergesAt
    {f : ℝ → ℝ} {T σ : ℝ} (hT : 0 ≤ T)
    (hfull : laplaceConvergesAt f σ) :
    laplaceConvergesAt (laplaceTail f T) σ := by
  apply (laplaceConvergesAt_laplaceTail_iff f T σ).mpr
  exact hfull.mono_set (fun t ht => lt_of_le_of_lt hT ht)

/-- The continuation naturally associated with a translated Laplace tail. -/
noncomputable def laplaceTailContinuation
    (f : ℝ → ℝ) (F : ℂ → ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (w * (T : ℂ)) *
    (F w - compactLaplaceInitial f T w)

theorem meromorphic_laplaceTailContinuation {f : ℝ → ℝ}
    (hf : Continuous f) {F : ℂ → ℂ} (hF : Meromorphic F) (T : ℝ) :
    Meromorphic (laplaceTailContinuation f F T) := by
  have hinit : Meromorphic (compactLaplaceInitial f T) :=
    fun w => ((differentiable_compactLaplaceInitial hf T).analyticAt w).meromorphicAt
  exact (fun w => (by fun_prop : AnalyticAt ℂ
    (fun z : ℂ => Complex.exp (z * (T : ℂ))) w).meromorphicAt.mul
      ((hF w).sub (hinit w)))

theorem analyticAt_laplaceTailContinuation {f : ℝ → ℝ}
    (hf : Continuous f) {F : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (T : ℝ) :
    AnalyticAt ℂ (laplaceTailContinuation f F T) w := by
  exact (by fun_prop : AnalyticAt ℂ
    (fun z : ℂ => Complex.exp (z * (T : ℂ))) w).mul
      (hF.sub ((differentiable_compactLaplaceInitial hf T).analyticAt w))

theorem complexLaplaceIntegral_laplaceTail_eq_continuation
    {f : ℝ → ℝ} (hf : Continuous f) {F : ℂ → ℂ}
    {T σ : ℝ} (hT : 0 ≤ T)
    (hconv : laplaceConvergesAt f σ)
    (hagree : complexLaplaceIntegral f (σ : ℂ) = F (σ : ℂ)) :
    complexLaplaceIntegral (laplaceTail f T) (σ : ℂ) =
      laplaceTailContinuation f F T (σ : ℂ) := by
  have hsplit := complexLaplaceIntegral_eq_compactInitial_add_tail
    hf hT (w := (σ : ℂ)) hconv
  rw [hagree] at hsplit
  rw [laplaceTailContinuation]
  have htail :
      Complex.exp (-(σ : ℂ) * (T : ℂ)) *
          complexLaplaceIntegral (laplaceTail f T) (σ : ℂ) =
        F (σ : ℂ) - compactLaplaceInitial f T (σ : ℂ) := by
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using hsplit.symm
  calc
    complexLaplaceIntegral (laplaceTail f T) (σ : ℂ) =
        Complex.exp ((σ : ℂ) * (T : ℂ)) *
          (Complex.exp (-(σ : ℂ) * (T : ℂ)) *
            complexLaplaceIntegral (laplaceTail f T) (σ : ℂ)) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = Complex.exp ((σ : ℂ) * (T : ℂ)) *
        (F (σ : ℂ) - compactLaplaceInitial f T (σ : ℂ)) := by
      rw [htail]

/-- Landau's principle is unchanged by deleting a compact initial segment:
eventual nonnegativity is enough to force convergence at every positive
real parameter. -/
theorem eventuallyNonnegativeLaplaceBoundaryPrinciple
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a) (hf : Continuous f)
    (hf_eventual : ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → 0 ≤ f t)
    (hFmero : Meromorphic F)
    (hFanalytic : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F (σ : ℂ))
    (hconv : ∀ σ : ℝ, a < σ → laplaceConvergesAt f σ)
    (hagree : ∀ σ : ℝ, a < σ →
      complexLaplaceIntegral f (σ : ℂ) = F (σ : ℂ))
    {σ : ℝ} (hσ : 0 < σ) :
    laplaceConvergesAt f σ := by
  rcases hf_eventual with ⟨T₀, hT₀⟩
  let T : ℝ := max T₀ 0
  have hT : 0 ≤ T := le_max_right _ _
  have htail_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ laplaceTail f T u := by
    intro u hu
    apply laplaceTail_nonneg_of_eventually_nonneg
      (fun t ht => hT₀ t (le_trans (le_max_left _ _) ht)) hu
  have htail_cont : Continuous (laplaceTail f T) :=
    continuous_laplaceTail hf T
  have htail_conv : ∀ τ : ℝ, a < τ →
      laplaceConvergesAt (laplaceTail f T) τ := by
    intro τ hτ
    exact laplaceConvergesAt_laplaceTail_of_convergesAt hT (hconv τ hτ)
  have htail_agree : ∀ τ : ℝ, a < τ →
      complexLaplaceIntegral (laplaceTail f T) (τ : ℂ) =
        laplaceTailContinuation f F T (τ : ℂ) := by
    intro τ hτ
    exact complexLaplaceIntegral_laplaceTail_eq_continuation hf hT
      (hconv τ hτ) (hagree τ hτ)
  have htail_all := nonnegativeLaplaceBoundaryPrinciple
    (laplaceTail f T) (laplaceTailContinuation f F T) a ha
    htail_cont htail_nonneg
    (meromorphic_laplaceTailContinuation hf hFmero T)
    (fun τ hτ => analyticAt_laplaceTailContinuation hf (hFanalytic τ hτ) T)
    htail_conv htail_agree σ hσ
  exact laplaceConvergesAt_of_laplaceTail hf hT htail_all

/-! ## The shifted xi continuation -/

/-- Xi has no real zeros.  Reflection reduces the left half-axis to the
already checked right-half-axis theorem. -/
theorem riemannXi_real_ne_zero (x : ℝ) :
    riemannXi (x : ℂ) ≠ 0 := by
  by_cases hx : 1 / 2 ≤ x
  · have hcenter :
        ((((1 / 2 : ℝ) + (x - 1 / 2) : ℝ) : ℂ)) = (x : ℂ) := by
      push_cast
      ring
    rw [← hcenter]
    exact riemannXi_real_right_half_ne_zero (y := x - 1 / 2)
      (sub_nonneg.mpr hx)
  · have hy : 0 ≤ (1 - x) - 1 / 2 := by linarith
    have hright := riemannXi_real_right_half_ne_zero (y := (1 - x) - 1 / 2) hy
    have hreflect : riemannXi ((1 - x : ℝ) : ℂ) = riemannXi (x : ℂ) := by
      simpa using riemannXi_one_sub (x : ℂ)
    intro hzero
    apply hright
    rw [show (1 / 2 : ℝ) + ((1 - x) - 1 / 2) = 1 - x by ring]
    rw [hreflect, hzero]

/-- The explicit meromorphic continuation of the shifted Suzuki-Psi
Laplace transform. -/
noncomputable def suzukiPsiShiftedLaplaceContinuation
    (ω : ℝ) (w : ℂ) : ℂ :=
  (1 / w ^ 2) *
    logDeriv riemannXi ((((1 / 2 + ω : ℝ) : ℂ) + w))

theorem meromorphic_suzukiPsiShiftedLaplaceContinuation (ω : ℝ) :
    Meromorphic (suzukiPsiShiftedLaplaceContinuation ω) := by
  intro w
  have hxi : Meromorphic riemannXi :=
    fun z => (analyticAt_riemannXi z).meromorphicAt
  have hld : Meromorphic (logDeriv riemannXi) := hxi.logDeriv
  let coord : ℂ → ℂ := fun u => ((1 / 2 + ω : ℝ) : ℂ) + u
  have hcoord : AnalyticAt ℂ coord w := by
    dsimp [coord]
    fun_prop
  have hcomp : MeromorphicAt ((logDeriv riemannXi) ∘ coord) w :=
    (hld (coord w)).comp_analyticAt hcoord
  have hfac := (MeromorphicAt.const (1 : ℂ) w).div
    ((MeromorphicAt.id w).pow 2)
  have hproduct := hfac.mul hcomp
  apply hproduct.congr
  filter_upwards with u
  simp [suzukiPsiShiftedLaplaceContinuation, coord]

theorem analyticAt_suzukiPsiShiftedLaplaceContinuation_of_pos
    (ω : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    AnalyticAt ℂ (suzukiPsiShiftedLaplaceContinuation ω) (σ : ℂ) := by
  have hxi0 :
      riemannXi ((((1 / 2 + ω : ℝ) + σ : ℝ) : ℂ)) ≠ 0 :=
    riemannXi_real_ne_zero _
  have hxi : AnalyticAt ℂ riemannXi
      ((((1 / 2 + ω : ℝ) + σ : ℝ) : ℂ)) :=
    analyticAt_riemannXi _
  have hld : AnalyticAt ℂ (logDeriv riemannXi)
      ((((1 / 2 + ω : ℝ) + σ : ℝ) : ℂ)) := by
    rw [logDeriv]
    exact hxi.deriv.div hxi hxi0
  let coord : ℂ → ℂ := fun u => ((1 / 2 + ω : ℝ) : ℂ) + u
  have hcoord : AnalyticAt ℂ coord (σ : ℂ) := by
    dsimp [coord]
    fun_prop
  have hcomp : AnalyticAt ℂ ((logDeriv riemannXi) ∘ coord) (σ : ℂ) := by
    exact hld.comp_of_eq hcoord (by simp [coord])
  have hσc : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hfac : AnalyticAt ℂ (fun u : ℂ => 1 / u ^ 2) (σ : ℂ) := by
    exact analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hσc)
  have hproduct := hfac.mul hcomp
  apply hproduct.congr
  filter_upwards with u
  simp [suzukiPsiShiftedLaplaceContinuation, coord]

/-- The initial half-plane of absolute convergence of the shifted
Suzuki-Psi transform. -/
theorem laplaceConvergesAt_suzukiPsiShifted_initial
    (ω : ℝ) {σ : ℝ} (hσ : 0 < σ) (hstrip : 1 / 2 - ω < σ) :
    laplaceConvergesAt (suzukiPsiShifted ω) σ := by
  have hint := integrableOn_SuzukiShift_exp
    (ω := ω) (f := suzukiPsi) (z := Complex.I * (σ : ℂ))
    (by simpa [Complex.mul_im] using hσ)
    (integrableOn_suzukiPsi_exp (by
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      linarith))
  apply hint.congr
  filter_upwards with t
  congr 2
  simp [← mul_assoc]

theorem complexLaplaceIntegral_suzukiPsiShifted_eq_continuation
    (ω : ℝ) {σ : ℝ} (hσ : 0 < σ) (hstrip : 1 / 2 - ω < σ) :
    complexLaplaceIntegral (suzukiPsiShifted ω) (σ : ℂ) =
      suzukiPsiShiftedLaplaceContinuation ω (σ : ℂ) := by
  have h := integral_suzukiPsiShifted_exp_eq_logDeriv
    (ω := ω) (z := Complex.I * (σ : ℂ))
    (by simpa [Complex.mul_im] using hσ)
    (by simpa [Complex.mul_im] using hstrip)
  rw [complexLaplaceIntegral, suzukiPsiShiftedLaplaceContinuation]
  have hσc : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have harg :
      (((1 / 2 + ω : ℝ) : ℂ) -
          Complex.I * (Complex.I * (σ : ℂ))) =
        ((1 / 2 + ω : ℝ) : ℂ) + (σ : ℂ) := by
    simp [← mul_assoc]
  calc
    (∫ t : ℝ in Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (-(σ : ℂ) * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          (suzukiPsiShifted ω t : ℂ) *
            Complex.exp
              (Complex.I * (Complex.I * (σ : ℂ)) * (t : ℂ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      congr 2
      simp [← mul_assoc]
    _ = -(1 / (Complex.I * (σ : ℂ)) ^ 2) *
          logDeriv riemannXi
            (((1 / 2 + ω : ℝ) : ℂ) -
              Complex.I * (Complex.I * (σ : ℂ))) := h
    _ = 1 / (σ : ℂ) ^ 2 *
          logDeriv riemannXi
            (((1 / 2 + ω : ℝ) : ℂ) + (σ : ℂ)) := by
      rw [harg]
      field_simp [hσc]
      rw [Complex.I_sq]
      ring

/-- Complex right-half-plane version of the shifted transform identity. -/
theorem complexLaplaceIntegral_suzukiPsiShifted_eq_continuation_of_re
    (ω : ℝ) {w : ℂ} (hw : 0 < w.re)
    (hstrip : 1 / 2 - ω < w.re) :
    complexLaplaceIntegral (suzukiPsiShifted ω) w =
      suzukiPsiShiftedLaplaceContinuation ω w := by
  have h := integral_suzukiPsiShifted_exp_eq_logDeriv
    (ω := ω) (z := Complex.I * w)
    (by simpa [Complex.mul_im] using hw)
    (by simpa [Complex.mul_im] using hstrip)
  have hw0 : w ≠ 0 := by
    intro hzero
    subst w
    simp at hw
  have harg :
      (((1 / 2 + ω : ℝ) : ℂ) - Complex.I * (Complex.I * w)) =
        ((1 / 2 + ω : ℝ) : ℂ) + w := by
    simp [← mul_assoc]
  rw [complexLaplaceIntegral, suzukiPsiShiftedLaplaceContinuation]
  calc
    (∫ t : ℝ in Ioi 0,
        (suzukiPsiShifted ω t : ℂ) *
          Complex.exp (-w * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          (suzukiPsiShifted ω t : ℂ) *
            Complex.exp (Complex.I * (Complex.I * w) * (t : ℂ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      congr 2
      simp [← mul_assoc]
    _ = -(1 / (Complex.I * w) ^ 2) *
          logDeriv riemannXi
            (((1 / 2 + ω : ℝ) : ℂ) -
              Complex.I * (Complex.I * w)) := h
    _ = 1 / w ^ 2 *
          logDeriv riemannXi
            (((1 / 2 + ω : ℝ) : ℂ) + w) := by
      rw [harg]
      field_simp [hw0]
      rw [Complex.I_sq]
      ring

/-! ## Eventual positivity and the shifted xi half-plane -/

/-- Eventual nonnegativity of a shifted Suzuki function pushes its real
Laplace transform down to every positive decay parameter. -/
theorem laplaceConvergesAt_suzukiPsiShifted_of_eventual_nonneg
    {ω : ℝ} (h : SuzukiPsiShiftedEventuallyNonnegative ω)
    {σ : ℝ} (hσ : 0 < σ) :
    laplaceConvergesAt (suzukiPsiShifted ω) σ := by
  let a : ℝ := max (1 / 2 - ω) 0 + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [le_max_right (1 / 2 - ω) 0]
  apply eventuallyNonnegativeLaplaceBoundaryPrinciple
    (a := a) ha (continuous_suzukiPsiShifted ω) h
    (meromorphic_suzukiPsiShiftedLaplaceContinuation ω)
    (fun τ hτ =>
      analyticAt_suzukiPsiShiftedLaplaceContinuation_of_pos ω hτ)
    (fun τ haτ => ?_)
    (fun τ haτ => ?_) hσ
  · apply laplaceConvergesAt_suzukiPsiShifted_initial ω
    · dsimp [a] at haτ
      linarith [le_max_right (1 / 2 - ω) 0]
    · dsimp [a] at haτ
      linarith [le_max_left (1 / 2 - ω) 0]
  · apply complexLaplaceIntegral_suzukiPsiShifted_eq_continuation
    · dsimp [a] at haτ
      linarith [le_max_right (1 / 2 - ω) 0]
    · dsimp [a] at haτ
      linarith [le_max_left (1 / 2 - ω) 0]

theorem integrableOn_suzukiPsiShiftedLaplace_of_eventual_nonneg
    {ω : ℝ} (h : SuzukiPsiShiftedEventuallyNonnegative ω)
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => (suzukiPsiShifted ω t : ℂ) *
        Complex.exp (-w * (t : ℂ))) (Ioi 0) :=
  integrableOn_complex_laplace_of_convergesAt_re
    (continuous_suzukiPsiShifted ω)
    (laplaceConvergesAt_suzukiPsiShifted_of_eventual_nonneg h hw)

/-- Under eventual positivity, the shifted Laplace integral is analytic on
the complete open right half-plane. -/
theorem analyticOnNhd_suzukiPsiShiftedLaplace_rightHalfPlane
    {ω : ℝ} (h : SuzukiPsiShiftedEventuallyNonnegative ω) :
    AnalyticOnNhd ℂ (complexLaplaceIntegral (suzukiPsiShifted ω))
      {w : ℂ | 0 < w.re} := by
  intro w hw
  change 0 < w.re at hw
  let σ : ℝ := w.re / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσw : σ < w.re := by dsimp [σ]; linarith
  exact (analyticOnNhd_complexLaplaceIntegral_of_convergesAt
    (continuous_suzukiPsiShifted ω)
    (laplaceConvergesAt_suzukiPsiShifted_of_eventual_nonneg h hσ))
      w hσw

/-- Meromorphic uniqueness propagates the initial shifted-transform identity
across the connected right half-plane. -/
theorem meromorphicOrderAt_suzukiPsiShiftedLaplaceContinuation_nonneg
    {ω : ℝ} (h : SuzukiPsiShiftedEventuallyNonnegative ω)
    {w : ℂ} (hw : 0 < w.re) :
    0 ≤ meromorphicOrderAt (suzukiPsiShiftedLaplaceContinuation ω) w := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let L : ℂ → ℂ := complexLaplaceIntegral (suzukiPsiShifted ω)
  let D : ℂ → ℂ := fun z =>
    suzukiPsiShiftedLaplaceContinuation ω z - L z
  have hFOn : MeromorphicOn (suzukiPsiShiftedLaplaceContinuation ω) U :=
    fun z _ => meromorphic_suzukiPsiShiftedLaplaceContinuation ω z
  have hLOn : MeromorphicOn L U :=
    (analyticOnNhd_suzukiPsiShiftedLaplace_rightHalfPlane h).meromorphicOn
  have hDOn : MeromorphicOn D U := hFOn.sub hLOn
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  let b : ℝ := max (1 / 2 - ω) 0 + 1
  have hb0 : 0 < b := by
    dsimp [b]
    linarith [le_max_right (1 / 2 - ω) 0]
  have hbstrip : 1 / 2 - ω < b := by
    dsimp [b]
    linarith [le_max_left (1 / 2 - ω) 0]
  have hbaseU : (b : ℂ) ∈ U := by
    change 0 < (b : ℂ).re
    simpa using hb0
  have heqBase : D =ᶠ[nhdsWithin (b : ℂ) ({(b : ℂ)} : Set ℂ)ᶜ] 0 := by
    have hpos : ∀ᶠ z : ℂ in nhds (b : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
        (by simpa using hb0)
    have hstrip : ∀ᶠ z : ℂ in nhds (b : ℂ), 1 / 2 - ω < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
        (by simpa using hbstrip)
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds,
      hstrip.filter_mono nhdsWithin_le_nhds] with z hz hzs
    dsimp [D, L]
    rw [complexLaplaceIntegral_suzukiPsiShifted_eq_continuation_of_re
      ω hz hzs]
    simp
  have hbaseTop : meromorphicOrderAt D (b : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr heqBase
  have hDTop : meromorphicOrderAt D w = ⊤ := by
    by_contra hne
    have hbaseNe := hDOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (x := w) (y := (b : ℂ)) hU (by simpa [U] using hw)
      hbaseU hne
    exact hbaseNe hbaseTop
  have hDeq := meromorphicOrderAt_eq_top_iff.mp hDTop
  have heqPunct : suzukiPsiShiftedLaplaceContinuation ω =ᶠ[
      nhdsWithin w ({w} : Set ℂ)ᶜ] L := by
    filter_upwards [hDeq] with z hz
    exact sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr heqPunct]
  exact (analyticOnNhd_suzukiPsiShiftedLaplace_rightHalfPlane h
    w (by simpa using hw)).meromorphicOrderAt_nonneg

/-- Away from `w = 0`, multiplication by `w²` recovers xi's logarithmic
derivative from the shifted continuation. -/
theorem logDeriv_riemannXi_shifted_eq_sq_mul_laplaceContinuation
    (ω : ℝ) {w : ℂ} (hw : w ≠ 0) :
    logDeriv riemannXi (((1 / 2 + ω : ℝ) : ℂ) + w) =
      w ^ 2 * suzukiPsiShiftedLaplaceContinuation ω w := by
  rw [suzukiPsiShiftedLaplaceContinuation]
  field_simp [hw]

private theorem not_xi_zero_right_of_of_shifted_eventual_nonneg
    {ω : ℝ} (h : SuzukiPsiShiftedEventuallyNonnegative ω)
    {ρ : ℂ} (hρ : riemannXi ρ = 0)
    (hright : 1 / 2 + ω < ρ.re) : False := by
  let center : ℂ := ((1 / 2 + ω : ℝ) : ℂ)
  let w : ℂ := ρ - center
  have hwre : 0 < w.re := by
    dsimp [w, center]
    simpa using hright
  have hwne : w ≠ 0 := by
    intro hw
    have := congrArg Complex.re hw
    simp only [Complex.zero_re] at this
    linarith
  have horder :=
    meromorphicOrderAt_suzukiPsiShiftedLaplaceContinuation_nonneg h hwre
  obtain ⟨c, hlim⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg
    (meromorphic_suzukiPsiShiftedLaplaceContinuation ω w) horder
  let coord : ℂ → ℂ := fun s => s - center
  have hcoordNhds : Tendsto coord (nhds ρ) (nhds w) := by
    have hc : ContinuousAt coord ρ := by
      dsimp [coord]
      fun_prop
    simpa [coord, w] using hc.tendsto
  have hcoord : Tendsto coord
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ)
      (nhdsWithin w ({w} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordNhds.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    intro heq
    apply hs
    exact sub_left_inj.mp heq
  have hcoordPunct : Tendsto coord
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds w) :=
    hcoordNhds.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto
      (fun s => coord s ^ 2 *
        suzukiPsiShiftedLaplaceContinuation ω (coord s))
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds (w ^ 2 * c)) :=
    (hcoordPunct.pow 2).mul (hlim.comp hcoord)
  have hρcenter : ρ ≠ center := by
    intro heq
    subst ρ
    dsimp [center] at hright
    simp at hright
  have hcoordne : ∀ᶠ s in nhdsWithin ρ ({ρ} : Set ℂ)ᶜ,
      coord s ≠ 0 := by
    filter_upwards [eventually_ne_nhdsWithin hρcenter] with s hs
    exact sub_ne_zero.mpr hs
  have heqLog : (logDeriv riemannXi) =ᶠ[
      nhdsWithin ρ ({ρ} : Set ℂ)ᶜ]
      (fun s => coord s ^ 2 *
        suzukiPsiShiftedLaplaceContinuation ω (coord s)) := by
    filter_upwards [hcoordne] with s hs
    have heq :=
      logDeriv_riemannXi_shifted_eq_sq_mul_laplaceContinuation ω hs
    dsimp [coord, center] at heq ⊢
    rw [show (((1 / 2 + ω : ℝ) : ℂ) +
        (s - ((1 / 2 + ω : ℝ) : ℂ))) = s by ring] at heq
    exact heq
  have hld : Tendsto (logDeriv riemannXi)
      (nhdsWithin ρ ({ρ} : Set ℂ)ᶜ) (nhds (w ^ 2 * c)) :=
    hprod.congr' heqLog.symm
  exact not_tendsto_logDeriv_riemannXi_of_zero hρ _ hld

/-- The Lean-checked reverse implication in Suzuki's shifted Theorem 11.1:
eventual nonnegativity of `Psi_ω` excludes xi zeros strictly to the right of
`Re s = 1/2 + ω`. -/
theorem xiZeroFreeRightOf_of_shifted_eventually_nonnegative
    (ω : ℝ) (h : SuzukiPsiShiftedEventuallyNonnegative ω) :
    XiZeroFreeRightOf ω := by
  intro s hs
  by_contra hnot
  exact not_xi_zero_right_of_of_shifted_eventual_nonneg h hs
    (lt_of_not_ge hnot)

theorem shiftedEventualNonnegative_implies_xiZeroFreeRightOf
    (ω : ℝ) :
    SuzukiPsiShiftedEventuallyNonnegative ω → XiZeroFreeRightOf ω :=
  xiZeroFreeRightOf_of_shifted_eventually_nonnegative ω

/-- Every eventually positive shifted parameter lies in the corresponding
zero-free parameter set. -/
theorem suzukiShiftedEventualPositivitySet_subset_zeroFree :
    SuzukiShiftedEventualPositivitySet ⊆
      {ω : ℝ | XiZeroFreeRightOf ω} := by
  intro ω hω
  exact xiZeroFreeRightOf_of_shifted_eventually_nonnegative ω hω

end RHGarden
