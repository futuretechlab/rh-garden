import RHGarden.XiNevanlinna
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology ComplexConjugate

namespace RHGarden

/-- The compactly restricted integral quadratic form associated to a kernel. -/
noncomputable def kernelQuadraticIntegral
    (K : ℝ → ℝ → ℂ) (a : ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∫ t in Set.Icc (-a) a,
    ∫ u in Set.Icc (-a) a,
      K t u * φ t * starRingEnd ℂ (φ u)

/-- Positivity of all compact-interval quadratic forms with continuous test
functions. -/
def IntegralKernelPSD (K : ℝ → ℝ → ℂ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ φ : ℝ → ℂ,
    ContinuousOn φ (Set.Icc (-a) a) →
      0 ≤ (kernelQuadraticIntegral K a φ).re

/-- The integrand of the product-space version of the compact kernel form. -/
def kernelQuadraticIntegrand
    (K : ℝ → ℝ → ℂ) (φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  K p.1 p.2 * φ p.1 * starRingEnd ℂ (φ p.2)

theorem continuousOn_kernelQuadraticIntegrand
    {K : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {s : Set ℝ}
    (hK : ContinuousOn (Function.uncurry K) (s ×ˢ s))
    (hφ : ContinuousOn φ s) :
    ContinuousOn (kernelQuadraticIntegrand K φ) (s ×ˢ s) := by
  have hφfst : ContinuousOn (fun p : ℝ × ℝ => φ p.1) (s ×ˢ s) :=
    hφ.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hφsnd : ContinuousOn (fun p : ℝ × ℝ => φ p.2) (s ×ˢ s) :=
    hφ.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  exact (hK.mul hφfst).mul (continuous_star.comp_continuousOn hφsnd)

/-- A continuous kernel/test integrand is Bochner integrable on a compact
rectangle. -/
theorem integrableOn_kernelQuadraticIntegrand
    {K : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {a : ℝ}
    (hK : ContinuousOn (Function.uncurry K)
      (Set.Icc (-a) a ×ˢ Set.Icc (-a) a))
    (hφ : ContinuousOn φ (Set.Icc (-a) a)) :
    MeasureTheory.IntegrableOn (kernelQuadraticIntegrand K φ)
      (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) := by
  exact (continuousOn_kernelQuadraticIntegrand hK hφ).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- Positive sampled kernels remain positive after inserting nonnegative real
quadrature weights. -/
theorem KernelPSD.weighted_sum_nonneg
    {K : ℝ → ℝ → ℂ} (hK : KernelPSD K)
    {N : ℕ} (x : Fin N → ℝ) (w : Fin N → ℝ)
    (_hw : ∀ i, 0 ≤ w i) (φ : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j,
      (w i : ℂ) * (w j : ℂ) * K (x i) (x j) *
        φ i * starRingEnd ℂ (φ j)).re := by
  have h := hK N x (fun i => (w i : ℂ) * φ i)
  convert h using 1
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, conj_ofReal]
  ring

theorem KernelPSD.weighted_fintype_sum_nonneg
    {K : ℝ → ℝ → ℂ} (hK : KernelPSD K)
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (φ : ι → ℂ) :
    0 ≤ (∑ i, ∑ j,
      (w i : ℂ) * (w j : ℂ) * K (x i) (x j) *
        φ i * starRingEnd ℂ (φ j)).re := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := hK.weighted_sum_nonneg
    (fun i => x (e.symm i)) (fun i => w (e.symm i))
    (fun i => hw (e.symm i)) (fun i => φ (e.symm i))
  let A : ι → ι → ℂ := fun i j =>
    (w i : ℂ) * (w j : ℂ) * K (x i) (x j) *
      φ i * starRingEnd ℂ (φ j)
  have heq : (∑ i : Fin (Fintype.card ι),
      ∑ j : Fin (Fintype.card ι), A (e.symm i) (e.symm j)) =
      ∑ i : ι, ∑ j : ι, A i j := by
    calc
      (∑ i : Fin (Fintype.card ι),
          ∑ j : Fin (Fintype.card ι), A (e.symm i) (e.symm j)) =
        ∑ i : Fin (Fintype.card ι), ∑ j : ι, A (e.symm i) j := by
          apply Finset.sum_congr rfl
          intro i hi
          exact e.symm.sum_comp (fun j : ι => A (e.symm i) j)
      _ = ∑ i : ι, ∑ j : ι, A i j :=
        e.symm.sum_comp (fun i : ι => ∑ j : ι, A i j)
  change 0 ≤ (∑ i : Fin (Fintype.card ι),
    ∑ j : Fin (Fintype.card ι), A (e.symm i) (e.symm j)).re at h
  rw [heq] at h
  exact h

private theorem integral_comp_simpleFunc_eq_sum
    {α β E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (q : MeasureTheory.SimpleFunc α β) (F : β → E) :
    ∫ x, F (q x) ∂μ =
      ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • F y := by
  classical
  have hpoint : (fun x => F (q x)) =
      fun x => ∑ y ∈ q.range,
        (q ⁻¹' {y}).indicator (fun _ => F y) x := by
    funext x
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro y hy hyx
      rw [Set.indicator_of_notMem]
      exact fun hmem => hyx hmem.symm
    · exact fun h => (h (q.mem_range_self x)).elim
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [MeasureTheory.integral_indicator_const _ (q.measurableSet_preimage {y})]
  · intro y hy
    exact (MeasureTheory.integrable_const (F y)).indicator
      (q.measurableSet_preimage {y})

private theorem simpleFunc_kernelQuadraticIntegral_nonneg
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    {K : ℝ → ℝ → ℂ} (hK : KernelPSD K)
    (q : MeasureTheory.SimpleFunc α ℝ) (φ : ℝ → ℂ) :
    0 ≤ (∫ t, ∫ u,
      K (q t) (q u) * φ (q t) * starRingEnd ℂ (φ (q u)) ∂μ ∂μ).re := by
  classical
  let H : ℝ → ℝ → ℂ := fun x y =>
    K x y * φ x * starRingEnd ℂ (φ y)
  have hinner (x : ℝ) :
      (∫ u, H x (q u) ∂μ) =
        ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • H x y :=
    integral_comp_simpleFunc_eq_sum μ q (H x)
  have houter :
      (∫ t, ∫ u, H (q t) (q u) ∂μ ∂μ) =
        ∑ x ∈ q.range, μ.real (q ⁻¹' {x}) •
          ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • H x y := by
    calc
      (∫ t, ∫ u, H (q t) (q u) ∂μ ∂μ) =
          ∑ x ∈ q.range, μ.real (q ⁻¹' {x}) •
            (∫ u, H x (q u) ∂μ) :=
        integral_comp_simpleFunc_eq_sum μ q
          (fun x => ∫ u, H x (q u) ∂μ)
      _ = ∑ x ∈ q.range, μ.real (q ⁻¹' {x}) •
          ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • H x y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hinner]
  let w : {x // x ∈ q.range} → ℝ := fun x => μ.real (q ⁻¹' {(x : ℝ)})
  have hfinite := hK.weighted_fintype_sum_nonneg
    (fun x : {x // x ∈ q.range} => (x : ℝ)) w
    (fun _ => MeasureTheory.measureReal_nonneg) (fun x => φ (x : ℝ))
  change 0 ≤ (∫ t, ∫ u, H (q t) (q u) ∂μ ∂μ).re
  rw [houter]
  convert hfinite using 1
  apply congrArg Complex.re
  rw [← q.range.sum_attach]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.smul_sum, ← q.range.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro y hy
  dsimp [w, H]
  ring

/-- For a continuous kernel, positivity on all finite sampled configurations
extends to the Lebesgue integral quadratic form on every compact interval. -/
theorem integralKernelPSD_of_kernelPSD
    {K : ℝ → ℝ → ℂ}
    (hcont : Continuous (Function.uncurry K))
    (hPSD : KernelPSD K) :
    IntegralKernelPSD K := by
  intro a ha φ hφ
  let s : Set ℝ := Set.Icc (-a) a
  let μ : MeasureTheory.Measure ℝ := (volume : MeasureTheory.Measure ℝ).restrict s
  haveI : MeasureTheory.IsFiniteMeasure μ := by
    dsimp [μ, s]
    infer_instance
  have hzero : (0 : ℝ) ∈ s := by
    change -a ≤ 0 ∧ 0 ≤ a
    constructor <;> linarith
  let q : ℕ → MeasureTheory.SimpleFunc ℝ ℝ := fun n =>
    MeasureTheory.SimpleFunc.approxOn id measurable_id s 0 hzero n
  let F : ℕ → (ℝ × ℝ) → ℂ := fun n p =>
    kernelQuadraticIntegrand K φ (q n p.1, q n p.2)
  let f : (ℝ × ℝ) → ℂ := kernelQuadraticIntegrand K φ
  have hqmem (n : ℕ) (x : ℝ) : q n x ∈ s := by
    exact MeasureTheory.SimpleFunc.approxOn_mem measurable_id hzero n x
  have hFcont : ContinuousOn f (s ×ˢ s) := by
    exact continuousOn_kernelQuadraticIntegrand hcont.continuousOn hφ
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image hFcont.norm
  have hFmeas (n : ℕ) :
      MeasureTheory.AEStronglyMeasurable (F n) (μ.prod μ) := by
    let qp : MeasureTheory.SimpleFunc (ℝ × ℝ) (ℝ × ℝ) :=
      ((q n).comp Prod.fst measurable_fst).pair
        ((q n).comp Prod.snd measurable_snd)
    have hmeas : Measurable (fun p : ℝ × ℝ => f (qp p)) :=
      (qp.map f).measurable
    exact hmeas.aestronglyMeasurable
  have hFbound (n : ℕ) :
      ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, ‖F n p‖ ≤ M := by
    filter_upwards with p
    exact hM (Set.mem_image_of_mem (fun x => ‖f x‖)
      ⟨hqmem n p.1, hqmem n p.2⟩)
  have hM_integrable : MeasureTheory.Integrable (fun _ : ℝ × ℝ => M) (μ.prod μ) :=
    MeasureTheory.integrable_const M
  have hlim : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ,
      Tendsto (fun n => F n p) atTop (𝓝 (f p)) := by
    have hmem : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p ∈ s ×ˢ s := by
      dsimp [μ]
      rw [MeasureTheory.Measure.prod_restrict]
      exact MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [hmem] with p hp
    have hqfst : Tendsto (fun n => q n p.1) atTop (𝓝 p.1) :=
      MeasureTheory.SimpleFunc.tendsto_approxOn measurable_id hzero
        (subset_closure hp.1)
    have hqsnd : Tendsto (fun n => q n p.2) atTop (𝓝 p.2) :=
      MeasureTheory.SimpleFunc.tendsto_approxOn measurable_id hzero
        (subset_closure hp.2)
    apply Filter.Tendsto.comp (hFcont p hp)
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hqfst.prodMk_nhds hqsnd,
      Filter.Eventually.of_forall (fun n => ⟨hqmem n p.1, hqmem n p.2⟩)⟩
  have htendsto : Tendsto
      (fun n => ∫ p, F n p ∂μ.prod μ) atTop
      (𝓝 (∫ p, f p ∂μ.prod μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ × ℝ => M) hFmeas hM_integrable hFbound hlim
  have hFnint (n : ℕ) : MeasureTheory.Integrable (F n) (μ.prod μ) :=
    hM_integrable.mono' (hFmeas n) (hFbound n)
  have hFnnonneg (n : ℕ) : 0 ≤ (∫ p, F n p ∂μ.prod μ).re := by
    rw [MeasureTheory.integral_prod _ (hFnint n)]
    exact simpleFunc_kernelQuadraticIntegral_nonneg μ hPSD (q n) φ
  have hlimit_nonneg : 0 ≤ (∫ p, f p ∂μ.prod μ).re := by
    exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp htendsto)
      (Filter.Eventually.of_forall hFnnonneg)
  have hfint : MeasureTheory.Integrable f (μ.prod μ) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.prod_restrict]
    exact integrableOn_kernelQuadraticIntegrand hcont.continuousOn hφ
  rw [MeasureTheory.integral_prod _ hfint] at hlimit_nonneg
  simpa [kernelQuadraticIntegral, μ, s, f, kernelQuadraticIntegrand] using
    hlimit_nonneg

/-- The Riemann screw kernel is jointly continuous. -/
theorem continuous_riemannScrewKernel :
    Continuous (Function.uncurry riemannScrewKernel) := by
  have hg : Continuous (fun t : ℝ => (riemannScrew t : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_riemannScrew
  unfold Function.uncurry riemannScrewKernel
  exact (((hg.comp (continuous_fst.sub continuous_snd)).sub
    (hg.comp continuous_fst)).sub
      (hg.comp continuous_snd.neg)).add continuous_const

/-- Sampled positivity of the Riemann screw kernel therefore implies
positivity of every compact-interval integral quadratic form. -/
theorem integralRiemannScrewKernelPSD_of_kernelPSD
    (hPSD : KernelPSD riemannScrewKernel) :
    IntegralKernelPSD riemannScrewKernel :=
  integralKernelPSD_of_kernelPSD continuous_riemannScrewKernel hPSD

/-- The whole-line Hermitian form attached to the Riemann screw kernel.  It
is used below only for continuous functions with explicitly bounded support. -/
noncomputable def screwHermitianForm (φ : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, ∫ u : ℝ,
    riemannScrewKernel t u * φ t * starRingEnd ℂ (φ u)

/-- If the test function is supported in `[-a,a]`, the whole-line form is
exactly its compact-interval restriction. -/
theorem screwHermitianForm_eq_kernelQuadraticIntegral
    {a : ℝ} {φ : ℝ → ℂ}
    (hsupp : Function.support φ ⊆ Set.Icc (-a) a) :
    screwHermitianForm φ =
      kernelQuadraticIntegral riemannScrewKernel a φ := by
  have hzero (x : ℝ) (hx : x ∉ Set.Icc (-a) a) : φ x = 0 := by
    by_contra hne
    exact hx (hsupp (Function.mem_support.mpr hne))
  unfold screwHermitianForm kernelQuadraticIntegral
  calc
    (∫ t : ℝ, ∫ u : ℝ,
        riemannScrewKernel t u * φ t * starRingEnd ℂ (φ u)) =
        ∫ t : ℝ, ∫ u : ℝ in Set.Icc (-a) a,
          riemannScrewKernel t u * φ t * starRingEnd ℂ (φ u) := by
      congr 1 with t
      apply (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => ?_)).symm
      simp [hzero u hu]
    _ = ∫ t : ℝ in Set.Icc (-a) a,
        ∫ u : ℝ in Set.Icc (-a) a,
          riemannScrewKernel t u * φ t * starRingEnd ℂ (φ u) := by
      apply (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => ?_)).symm
      simp [hzero t ht]

/-- Every continuous compactly supported test with an explicit symmetric
support bound has nonnegative Riemann screw Hermitian form. -/
theorem screwHermitianForm_nonneg_of_kernelPSD
    (hPSD : KernelPSD riemannScrewKernel)
    {a : ℝ} (ha : 0 < a) {φ : ℝ → ℂ}
    (hφ_cont : Continuous φ)
    (hsupp : Function.support φ ⊆ Set.Icc (-a) a) :
    0 ≤ (screwHermitianForm φ).re := by
  rw [screwHermitianForm_eq_kernelQuadraticIntegral hsupp]
  exact integralRiemannScrewKernelPSD_of_kernelPSD hPSD a ha φ
    hφ_cont.continuousOn

/-- The compact convolution term remaining after the zero-mean affine
pieces of the screw kernel are removed. -/
noncomputable def screwConvolutionIntegral
    (a : ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ in Set.Icc (-a) a,
    ∫ u : ℝ in Set.Icc (-a) a,
      (riemannScrew (t - u) : ℂ) * φ t * starRingEnd ℂ (φ u)

private theorem kernelQuadraticIntegral_eq_setIntegral_prod
    {K : ℝ → ℝ → ℂ} {a : ℝ} {φ : ℝ → ℂ}
    (hK : ContinuousOn (Function.uncurry K)
      (Set.Icc (-a) a ×ˢ Set.Icc (-a) a))
    (hφ : ContinuousOn φ (Set.Icc (-a) a)) :
    kernelQuadraticIntegral K a φ =
      ∫ p : ℝ × ℝ in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
        kernelQuadraticIntegrand K φ p := by
  have hint := integrableOn_kernelQuadraticIntegrand hK hφ
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
    ← MeasureTheory.Measure.prod_restrict] at hint
  rw [kernelQuadraticIntegral, MeasureTheory.Measure.volume_eq_prod,
    ← MeasureTheory.Measure.prod_restrict,
    MeasureTheory.integral_prod _ hint]
  rfl

/-- On zero-mean tests, all three affine terms in the screw kernel vanish,
leaving only the translation-convolution term. -/
theorem kernelQuadraticIntegral_eq_convolution_of_integral_zero
    {a : ℝ} {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc (-a) a))
    (hzero : ∫ t : ℝ in Set.Icc (-a) a, φ t = 0) :
    kernelQuadraticIntegral riemannScrewKernel a φ =
      screwConvolutionIntegral a φ := by
  let s : Set ℝ := Set.Icc (-a) a
  let KA : ℝ → ℝ → ℂ := fun t u => (riemannScrew (t - u) : ℂ)
  let KB : ℝ → ℝ → ℂ := fun t _ => (riemannScrew t : ℂ)
  let KC : ℝ → ℝ → ℂ := fun _ u => (riemannScrew (-u) : ℂ)
  let KD : ℝ → ℝ → ℂ := fun _ _ => (riemannScrew 0 : ℂ)
  change ContinuousOn φ s at hφ
  change (∫ t : ℝ in s, φ t) = 0 at hzero
  have hKA : Continuous (Function.uncurry KA) := by
    dsimp [KA, Function.uncurry]
    exact (Complex.continuous_ofReal.comp continuous_riemannScrew).comp
      (continuous_fst.sub continuous_snd)
  have hKB : Continuous (Function.uncurry KB) := by
    dsimp [KB, Function.uncurry]
    exact (Complex.continuous_ofReal.comp continuous_riemannScrew).comp continuous_fst
  have hKC : Continuous (Function.uncurry KC) := by
    dsimp [KC, Function.uncurry]
    exact (Complex.continuous_ofReal.comp continuous_riemannScrew).comp continuous_snd.neg
  have hKD : Continuous (Function.uncurry KD) := continuous_const
  have hA : MeasureTheory.IntegrableOn (kernelQuadraticIntegrand KA φ) (s ×ˢ s) :=
    integrableOn_kernelQuadraticIntegrand hKA.continuousOn hφ
  have hB : MeasureTheory.IntegrableOn (kernelQuadraticIntegrand KB φ) (s ×ˢ s) :=
    integrableOn_kernelQuadraticIntegrand hKB.continuousOn hφ
  have hC : MeasureTheory.IntegrableOn (kernelQuadraticIntegrand KC φ) (s ×ˢ s) :=
    integrableOn_kernelQuadraticIntegrand hKC.continuousOn hφ
  have hD : MeasureTheory.IntegrableOn (kernelQuadraticIntegrand KD φ) (s ×ˢ s) :=
    integrableOn_kernelQuadraticIntegrand hKD.continuousOn hφ
  have hBzero :
      (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KB φ p) = 0 := by
    rw [show (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KB φ p) =
        (∫ t : ℝ in s, (riemannScrew t : ℂ) * φ t) *
          ∫ u : ℝ in s, starRingEnd ℂ (φ u) by
      exact MeasureTheory.setIntegral_prod_mul
        (fun t => (riemannScrew t : ℂ) * φ t)
        (fun u => starRingEnd ℂ (φ u)) s s]
    rw [integral_conj, hzero]
    simp
  have hCzero :
      (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KC φ p) = 0 := by
    calc
      (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KC φ p) =
          ∫ p : ℝ × ℝ in s ×ˢ s,
            φ p.1 * ((riemannScrew (-p.2) : ℂ) * starRingEnd ℂ (φ p.2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        dsimp [kernelQuadraticIntegrand, KC]
        ring
      _ = (∫ t : ℝ in s, φ t) *
          ∫ u : ℝ in s,
            (riemannScrew (-u) : ℂ) * starRingEnd ℂ (φ u) :=
        MeasureTheory.setIntegral_prod_mul φ
          (fun u => (riemannScrew (-u) : ℂ) * starRingEnd ℂ (φ u)) s s
      _ = 0 := by rw [hzero, zero_mul]
  have hDzero :
      (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KD φ p) = 0 := by
    rw [show (∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KD φ p) =
        (∫ t : ℝ in s, (riemannScrew 0 : ℂ) * φ t) *
          ∫ u : ℝ in s, starRingEnd ℂ (φ u) by
      exact MeasureTheory.setIntegral_prod_mul
        (fun t => (riemannScrew 0 : ℂ) * φ t)
        (fun u => starRingEnd ℂ (φ u)) s s]
    rw [integral_conj, hzero]
    simp
  rw [kernelQuadraticIntegral_eq_setIntegral_prod
    continuous_riemannScrewKernel.continuousOn hφ]
  change (∫ p : ℝ × ℝ in s ×ˢ s,
      kernelQuadraticIntegrand riemannScrewKernel φ p) = _
  have hconv : screwConvolutionIntegral a φ =
      ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KA φ p := by
    calc
      screwConvolutionIntegral a φ = kernelQuadraticIntegral KA a φ := by
        rfl
      _ = ∫ p : ℝ × ℝ in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          kernelQuadraticIntegrand KA φ p :=
        kernelQuadraticIntegral_eq_setIntegral_prod hKA.continuousOn hφ
      _ = ∫ p : ℝ × ℝ in s ×ˢ s,
          kernelQuadraticIntegrand KA φ p := by rfl
  rw [hconv]
  have hpoint (p : ℝ × ℝ) :
      kernelQuadraticIntegrand riemannScrewKernel φ p =
        kernelQuadraticIntegrand KA φ p -
          kernelQuadraticIntegrand KB φ p -
          kernelQuadraticIntegrand KC φ p +
          kernelQuadraticIntegrand KD φ p := by
    dsimp [kernelQuadraticIntegrand, riemannScrewKernel, KA, KB, KC, KD]
    ring
  simp_rw [hpoint]
  calc
    (∫ p : ℝ × ℝ in s ×ˢ s,
        kernelQuadraticIntegrand KA φ p - kernelQuadraticIntegrand KB φ p -
          kernelQuadraticIntegrand KC φ p + kernelQuadraticIntegrand KD φ p) =
        (∫ p : ℝ × ℝ in s ×ˢ s,
          kernelQuadraticIntegrand KA φ p - kernelQuadraticIntegrand KB φ p -
            kernelQuadraticIntegrand KC φ p) +
        ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KD φ p :=
      MeasureTheory.integral_add (hA.sub hB |>.sub hC) hD
    _ = (((∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KA φ p) -
          ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KB φ p) -
          ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KC φ p) +
          ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KD φ p := by
      congr 1
      calc
        (∫ p : ℝ × ℝ in s ×ˢ s,
            kernelQuadraticIntegrand KA φ p - kernelQuadraticIntegrand KB φ p -
              kernelQuadraticIntegrand KC φ p) =
            (∫ p : ℝ × ℝ in s ×ˢ s,
              kernelQuadraticIntegrand KA φ p - kernelQuadraticIntegrand KB φ p) -
              ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KC φ p :=
          MeasureTheory.integral_sub (hA.sub hB) hC
        _ = ((∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KA φ p) -
            ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KB φ p) -
              ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KC φ p := by
          rw [MeasureTheory.integral_sub hA hB]
    _ = ∫ p : ℝ × ℝ in s ×ˢ s, kernelQuadraticIntegrand KA φ p := by
      rw [hBzero, hCzero, hDzero]
      ring

/-- Whole-line version of the zero-mean convolution simplification for an
explicitly compactly supported test. -/
theorem screwHermitianForm_eq_convolution_of_integral_zero
    {a : ℝ} {φ : ℝ → ℂ}
    (hφ : Continuous φ)
    (hsupp : Function.support φ ⊆ Set.Icc (-a) a)
    (hzero : ∫ t : ℝ, φ t = 0) :
    screwHermitianForm φ = screwConvolutionIntegral a φ := by
  rw [screwHermitianForm_eq_kernelQuadraticIntegral hsupp]
  apply kernelQuadraticIntegral_eq_convolution_of_integral_zero hφ.continuousOn
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hzero
  · intro t ht
    by_contra hne
    exact ht (hsupp (Function.mem_support.mpr hne))

/-- A continuous one-sided cutoff which is supported between `-1` and
`R+1` and is identically one on `[0,R]` when `R ≥ 0`. -/
def screwExponentialCutoff (R t : ℝ) : ℝ :=
  max 0 (min 1 (t + 1)) * max 0 (min 1 (R + 1 - t))

theorem continuous_screwExponentialCutoff (R : ℝ) :
    Continuous (screwExponentialCutoff R) := by
  unfold screwExponentialCutoff
  fun_prop

theorem screwExponentialCutoff_eq_one
    {R t : ℝ} (ht0 : 0 ≤ t) (htR : t ≤ R) :
    screwExponentialCutoff R t = 1 := by
  rw [screwExponentialCutoff,
    min_eq_left (by linarith), max_eq_right (by linarith),
    min_eq_left (by linarith), max_eq_right (by linarith)]
  norm_num

/-- Compactly supported truncated exponential used to approximate the
Fourier--Laplace test without introducing a noncompact test prematurely. -/
noncomputable def exponentialTest (z : ℂ) (R t : ℝ) : ℂ :=
  (screwExponentialCutoff R t : ℂ) *
    Complex.exp (Complex.I * z * (t : ℂ))

theorem continuous_exponentialTest (z : ℂ) (R : ℝ) :
    Continuous (exponentialTest z R) := by
  unfold exponentialTest
  exact (Complex.continuous_ofReal.comp
    (continuous_screwExponentialCutoff R)).mul
      (Complex.continuous_exp.comp (by fun_prop))

theorem support_exponentialTest_subset
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    Function.support (exponentialTest z R) ⊆
      Set.Icc (-(R + 1)) (R + 1) := by
  intro t ht
  have htne : exponentialTest z R t ≠ 0 := Function.mem_support.mp ht
  constructor
  · by_contra hnot
    have hlt : t < -(R + 1) := lt_of_not_ge hnot
    have hmin : min 1 (t + 1) = t + 1 := min_eq_right (by linarith)
    have hmax : max 0 (t + 1) = 0 := max_eq_left (by linarith)
    apply htne
    simp [exponentialTest, screwExponentialCutoff, hmin, hmax]
  · by_contra hnot
    have hlt : R + 1 < t := lt_of_not_ge hnot
    have hmin : min 1 (R + 1 - t) = R + 1 - t :=
      min_eq_right (by linarith)
    have hmax : max 0 (R + 1 - t) = 0 := max_eq_left (by linarith)
    apply htne
    simp [exponentialTest, screwExponentialCutoff, hmin, hmax]

theorem integrable_exponentialTest
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    MeasureTheory.Integrable (exponentialTest z R) := by
  let s : Set ℝ := Set.Icc (-(R + 1)) (R + 1)
  have hsupp : Function.support (exponentialTest z R) ⊆ s :=
    support_exponentialTest_subset z hR
  have hint : MeasureTheory.IntegrableOn (exponentialTest z R) s :=
    (continuous_exponentialTest z R).continuousOn.integrableOn_compact isCompact_Icc
  exact hint.integrable_of_forall_notMem_eq_zero fun t ht => by
    by_contra hne
    exact ht (hsupp (Function.mem_support.mpr hne))

/-- Integral screw-kernel positivity is available for every truncated
exponential test. -/
theorem screwHermitianForm_exponentialTest_nonneg_of_kernelPSD
    (hPSD : KernelPSD riemannScrewKernel)
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ (screwHermitianForm (exponentialTest z R)).re := by
  apply screwHermitianForm_nonneg_of_kernelPSD hPSD
    (a := R + 1) (by linarith) (continuous_exponentialTest z R)
    (support_exponentialTest_subset z hR)

end RHGarden
