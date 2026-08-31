import RHGarden.LiComposition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section

namespace RHGarden

/-- The principal logarithm of the unnormalized entire xi function, used only
as a local analytic germ at `s = 1`. -/
def standardXiLog (s : ℂ) : ℂ := Complex.log (riemannXi s)

theorem riemannXi_one_ne_zero : riemannXi 1 ≠ 0 := by
  rw [riemannXi_one]
  norm_num

theorem riemannXi_one_mem_slitPlane : riemannXi 1 ∈ Complex.slitPlane := by
  rw [riemannXi_one]
  simp [Complex.slitPlane]

theorem analyticAt_standardXiLog : AnalyticAt ℂ standardXiLog 1 := by
  unfold standardXiLog
  exact (differentiable_riemannXi.analyticAt 1).clog riemannXi_one_mem_slitPlane

theorem analyticAt_log_normalizedXi :
    AnalyticAt ℂ (fun s : ℂ ↦ Complex.log (normalizedXi s)) 1 := by
  have hnorm : AnalyticAt ℂ normalizedXi 1 := by
    unfold normalizedXi
    exact (differentiable_riemannXi.const_mul 2).analyticAt 1
  exact hnorm.clog (by simp [normalizedXi, Complex.slitPlane])

/-- Zero-based form of Li's standard classical definition: index `n`
corresponds to the conventional coefficient `λ_(n+1)`. -/
def classicalLiCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1)
      (fun s : ℂ ↦ s ^ n * Complex.log (riemannXi s)) 1 /
    (n.factorial : ℂ)

/-- The local difference between the normalized and standard xi logarithms. -/
def logNormalizationDifference (s : ℂ) : ℂ :=
  Complex.log (normalizedXi s) - standardXiLog s

theorem analyticAt_logNormalizationDifference :
    AnalyticAt ℂ logNormalizationDifference 1 := by
  unfold logNormalizationDifference standardXiLog
  exact analyticAt_log_normalizedXi.sub analyticAt_standardXiLog

theorem eventually_standardXiLog_conj :
    ∀ᶠ s in nhds (1 : ℂ),
      standardXiLog (starRingEnd ℂ s) =
        starRingEnd ℂ (standardXiLog s) := by
  have hxi : ∀ᶠ s in nhds (1 : ℂ), riemannXi s ∈ Complex.slitPlane :=
    differentiable_riemannXi.continuous.continuousAt
      (Complex.isOpen_slitPlane.mem_nhds riemannXi_one_mem_slitPlane)
  filter_upwards [hxi] with s hs
  rw [standardXiLog, standardXiLog, riemannXi_conj, Complex.log_conj]
  exact (Complex.arg_lt_pi_iff.mpr
    ((Complex.mem_slitPlane_iff.mp hs).elim (fun h ↦ Or.inl h.le) Or.inr)).ne

private theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ iteratedDeriv m f ∘ starRingEnd ℂ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih, deriv_conj_conj]

theorem iteratedDeriv_standardXiLog_conj (m : ℕ) :
    starRingEnd ℂ (iteratedDeriv m standardXiLog 1) =
      iteratedDeriv m standardXiLog 1 := by
  have hreflect :
      (starRingEnd ℂ ∘ standardXiLog ∘ starRingEnd ℂ) =ᶠ[nhds (1 : ℂ)]
        standardXiLog := by
    filter_upwards [eventually_standardXiLog_conj] with s hs
    simpa [Function.comp_def] using congrArg (starRingEnd ℂ) hs
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq m hreflect
  rw [iteratedDeriv_conj_conj] at hderiv
  simpa [Function.comp_def] using hderiv

theorem iteratedDeriv_standardXiLog_im_eq_zero (m : ℕ) :
    (iteratedDeriv m standardXiLog 1).im = 0 :=
  Complex.conj_eq_iff_im.mp (iteratedDeriv_standardXiLog_conj m)

theorem eventually_deriv_log_normalizedXi_eq_standardXiLog :
    ∀ᶠ s in nhds (1 : ℂ),
      deriv (fun z : ℂ ↦ Complex.log (normalizedXi z)) s =
        deriv standardXiLog s := by
  have hxi : ∀ᶠ s in nhds (1 : ℂ), riemannXi s ∈ Complex.slitPlane :=
    differentiable_riemannXi.continuous.continuousAt
      (Complex.isOpen_slitPlane.mem_nhds riemannXi_one_mem_slitPlane)
  have hnorm : ∀ᶠ s in nhds (1 : ℂ), normalizedXi s ∈ Complex.slitPlane :=
    (differentiable_riemannXi.const_mul 2).continuous.continuousAt
      (Complex.isOpen_slitPlane.mem_nhds (by simp [Complex.slitPlane]))
  filter_upwards [hxi, hnorm] with s hsxi hsnorm
  rw [show (fun z : ℂ ↦ Complex.log (normalizedXi z)) =
      Complex.log ∘ normalizedXi by rfl,
    Complex.deriv_log_comp_eq_logDeriv
      (by
        unfold normalizedXi
        exact (differentiable_riemannXi.const_mul 2).differentiableAt) hsnorm]
  rw [show standardXiLog = Complex.log ∘ riemannXi by
      ext z; rfl,
    Complex.deriv_log_comp_eq_logDeriv
      differentiable_riemannXi.differentiableAt hsxi]
  change logDeriv (fun z : ℂ ↦ 2 * riemannXi z) s = logDeriv riemannXi s
  exact logDeriv_const_mul s 2 (by norm_num)

theorem deriv_log_normalizedXi_eq_standardXiLog :
    deriv (fun s : ℂ ↦ Complex.log (normalizedXi s)) 1 =
      deriv standardXiLog 1 :=
  Filter.EventuallyEq.eq_of_nhds
    eventually_deriv_log_normalizedXi_eq_standardXiLog

theorem eventually_log_normalizedXi_eq_standardXiLog_add_const :
    ∃ C : ℂ, ∀ᶠ s in nhds (1 : ℂ),
      Complex.log (normalizedXi s) = standardXiLog s + C := by
  have hderiv := eventually_deriv_log_normalizedXi_eq_standardXiLog
  have hdiffNorm : ∀ᶠ s in nhds (1 : ℂ),
      DifferentiableAt ℂ (fun z : ℂ ↦ Complex.log (normalizedXi z)) s :=
    analyticAt_log_normalizedXi.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt
  have hdiffStd : ∀ᶠ s in nhds (1 : ℂ), DifferentiableAt ℂ standardXiLog s :=
    analyticAt_standardXiLog.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hderiv.and (hdiffNorm.and hdiffStd))
  have hdiffNorm : DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.log (normalizedXi s)) (Metric.ball 1 r) := by
    intro s hs
    exact (hball hs).2.1.differentiableWithinAt
  have hdiffStd : DifferentiableOn ℂ standardXiLog (Metric.ball 1 r) := by
    intro s hs
    exact (hball hs).2.2.differentiableWithinAt
  obtain ⟨C, hC⟩ := Metric.isOpen_ball.exists_eq_add_of_deriv_eq
    (convex_ball (1 : ℂ) r).isPreconnected hdiffNorm hdiffStd
    (fun s hs ↦ (hball hs).1)
  exact ⟨C, Filter.Eventually.mono (Metric.ball_mem_nhds 1 hr) hC⟩

theorem eventuallyEq_logNormalizationDifference_const :
    ∃ C : ℂ, logNormalizationDifference =ᶠ[nhds (1 : ℂ)] fun _ ↦ C := by
  obtain ⟨C, hC⟩ := eventually_log_normalizedXi_eq_standardXiLog_add_const
  refine ⟨C, ?_⟩
  filter_upwards [hC] with s hs
  simp [logNormalizationDifference, hs]

theorem iteratedDeriv_log_normalizedXi_eq_standardXiLog
    (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m (fun s : ℂ ↦ Complex.log (normalizedXi s)) 1 =
      iteratedDeriv m standardXiLog 1 := by
  obtain ⟨C, hC⟩ := eventually_log_normalizedXi_eq_standardXiLog_add_const
  calc
    iteratedDeriv m (fun s : ℂ ↦ Complex.log (normalizedXi s)) 1 =
        iteratedDeriv m (fun s ↦ standardXiLog s + C) 1 :=
      Filter.EventuallyEq.iteratedDeriv_eq m hC
    _ = iteratedDeriv m standardXiLog 1 := by
      simpa [add_comm] using
        (iteratedDeriv_const_add (x := (1 : ℂ)) (f := standardXiLog) (by omega) C)

theorem iteratedDeriv_const_mul_pow_succ_eq_zero (C : ℂ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun s : ℂ ↦ C * s ^ n) 1 = 0 := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  simp

theorem normalizedClassicalLiCoefficient_eq_classical (n : ℕ) :
    normalizedClassicalLiCoefficient n = classicalLiCoefficient n := by
  obtain ⟨C, hC⟩ := eventually_log_normalizedXi_eq_standardXiLog_add_const
  have hprod :
      (fun s : ℂ ↦ s ^ n * Complex.log (normalizedXi s)) =ᶠ[nhds 1]
        (fun s : ℂ ↦ s ^ n * standardXiLog s + C * s ^ n) := by
    filter_upwards [hC] with s hs
    rw [hs]
    ring
  rw [normalizedClassicalLiCoefficient, classicalLiCoefficient]
  rw [Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hprod]
  have hpow : ContDiffAt ℂ (n + 1) (fun s : ℂ ↦ s ^ n) 1 := by
    fun_prop
  have hpolylog : ContDiffAt ℂ (n + 1)
      (fun s : ℂ ↦ s ^ n * standardXiLog s) 1 :=
    hpow.mul analyticAt_standardXiLog.contDiffAt
  have hconstpow : ContDiffAt ℂ (n + 1) (fun s : ℂ ↦ C * s ^ n) 1 := by
    fun_prop
  rw [show (fun s : ℂ ↦ s ^ n * standardXiLog s + C * s ^ n) =
      (fun s : ℂ ↦ s ^ n * standardXiLog s) + (fun s : ℂ ↦ C * s ^ n) by rfl,
    iteratedDeriv_add hpolylog hconstpow,
    iteratedDeriv_const_mul_pow_succ_eq_zero]
  simp [standardXiLog]

theorem liGeneratingCoefficient_eq_classical (n : ℕ) :
    liGeneratingCoefficient n = classicalLiCoefficient n :=
  (liGeneratingCoefficient_eq_normalizedClassical n).trans
    (normalizedClassicalLiCoefficient_eq_classical n)

theorem classicalLiCoefficient_conj (n : ℕ) :
    starRingEnd ℂ (classicalLiCoefficient n) = classicalLiCoefficient n := by
  let f : ℂ → ℂ := fun s ↦ s ^ n * standardXiLog s
  have hreflect : (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) =ᶠ[nhds (1 : ℂ)] f := by
    filter_upwards [eventually_standardXiLog_conj] with s hs
    simp only [f, Function.comp_apply, map_mul, map_pow, starRingEnd_self_apply]
    rw [hs]
    simp
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hreflect
  rw [iteratedDeriv_conj_conj] at hderiv
  rw [classicalLiCoefficient]
  simp only [map_div₀, map_natCast]
  change starRingEnd ℂ (iteratedDeriv (n + 1) f 1) /
      (n.factorial : ℂ) = iteratedDeriv (n + 1) f 1 / (n.factorial : ℂ)
  simpa [Function.comp_def] using congrArg
    (fun z : ℂ ↦ z / (n.factorial : ℂ)) hderiv

theorem classicalLiCoefficient_im_eq_zero (n : ℕ) :
    (classicalLiCoefficient n).im = 0 :=
  Complex.conj_eq_iff_im.mp (classicalLiCoefficient_conj n)

/-- The standard classical Li coefficient as a real number. Index `n`
corresponds to the conventional coefficient `λ_(n+1)`. -/
def classicalLiRealCoefficient (n : ℕ) : ℝ := (classicalLiCoefficient n).re

theorem classicalLiCoefficient_eq_real (n : ℕ) :
    classicalLiCoefficient n = (classicalLiRealCoefficient n : ℂ) := by
  apply Complex.ext
  · simp [classicalLiRealCoefficient]
  · simp [classicalLiCoefficient_im_eq_zero]

/-- The open Li-positivity proposition in zero-based indexing: the term at
index `n` is the conventional classical coefficient `λ_(n+1)`. -/
def LiPositive : Prop := ∀ n : ℕ, 0 ≤ classicalLiRealCoefficient n

end RHGarden
