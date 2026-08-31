import RHGarden.WeilFinite
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Analytic.Order

noncomputable section

open Filter Set Metric

namespace RHGarden

theorem analyticAt_riemannXi (ρ : ℂ) : AnalyticAt ℂ riemannXi ρ :=
  differentiable_riemannXi.analyticAt ρ

theorem analyticOnNhd_riemannXi : AnalyticOnNhd ℂ riemannXi Set.univ :=
  fun z _ ↦ analyticAt_riemannXi z

theorem meromorphicOn_riemannXi : MeromorphicOn riemannXi Set.univ :=
  analyticOnNhd_riemannXi.meromorphicOn

/-- The global divisor of the entire xi function; positive values are zero
multiplicities and its support is locally finite. -/
noncomputable def xiDivisor : Function.locallyFinsupp ℂ ℤ :=
  MeromorphicOn.divisor riemannXi Set.univ

theorem analyticOrderAt_riemannXi_ne_top (ρ : ℂ) :
    analyticOrderAt riemannXi ρ ≠ ⊤ := by
  intro htop
  have h := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero
    ρ analyticAt_riemannXi).mp htop
  have := congrFun h 1
  simp [riemannXi_one] at this

theorem xiDivisor_apply (ρ : ℂ) :
    xiDivisor ρ = ((analyticOrderAt riemannXi ρ).map (↑)).untop₀ := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi trivial

theorem xiDivisor_nonneg (ρ : ℂ) : 0 ≤ xiDivisor ρ := by
  rw [xiDivisor_apply]
  simp

/-- Analytic multiplicity of an xi zero, and zero away from the zero set. -/
noncomputable def xiMultiplicity (ρ : ℂ) : ℕ := Int.toNat (xiDivisor ρ)

theorem xiMultiplicity_cast (ρ : ℂ) :
    (xiMultiplicity ρ : ℤ) = xiDivisor ρ := by
  exact Int.eq_natCast_toNat.mpr (xiDivisor_nonneg ρ) |>.symm

theorem xiDivisor_ne_zero_iff (ρ : ℂ) :
    xiDivisor ρ ≠ 0 ↔ riemannXi ρ = 0 := by
  rw [xiDivisor_apply]
  have htop := analyticOrderAt_riemannXi_ne_top ρ
  cases horder : analyticOrderAt riemannXi ρ with
  | top => contradiction
  | coe n =>
      simp only [ENat.map_natCast, WithTop.untop₀_coe]
      simpa [horder] using (analyticAt_riemannXi ρ).analyticOrderAt_ne_zero

theorem mem_xiDivisor_support_iff (ρ : ℂ) :
    ρ ∈ xiDivisor.support ↔ riemannXi ρ = 0 := by
  exact Function.mem_support.trans (xiDivisor_ne_zero_iff ρ)

theorem mem_xiDivisor_support_iff_nontrivialZetaZero (ρ : ℂ) :
    ρ ∈ xiDivisor.support ↔ IsNontrivialZetaZero ρ := by
  rw [mem_xiDivisor_support_iff, riemannXi_eq_zero_iff_nontrivialZetaZero]

/-- Divisor support in the closed radial ball. -/
def xiZeroSupportInClosedBall (T : ℝ) : Set ℂ :=
  closedBall (0 : ℂ) T ∩ xiDivisor.support

theorem xiZeroSupportInClosedBall_finite (T : ℝ) :
    (xiZeroSupportInClosedBall T).Finite := by
  exact xiDivisor.locallyFiniteSupport.finite_inter_support_of_isCompact
    (isCompact_closedBall (0 : ℂ) T)

noncomputable def xiZeroSupportFinset (T : ℝ) : Finset ℂ :=
  (xiZeroSupportInClosedBall_finite T).toFinset

theorem mem_xiZeroSupportFinset_iff (T : ℝ) (ρ : ℂ) :
    ρ ∈ xiZeroSupportFinset T ↔ ρ ∈ xiDivisor.support ∧ ‖ρ‖ ≤ T := by
  rw [xiZeroSupportFinset, Set.Finite.mem_toFinset]
  simp [xiZeroSupportInClosedBall, mem_closedBall, and_comm]

/-- The genuine radial xi-zero cutoff, with each zero repeated according to
its analytic multiplicity. -/
noncomputable def xiZeroRadialCutoff (T : ℝ) : Multiset ℂ :=
  (xiZeroSupportFinset T).val.bind
    (fun ρ ↦ Multiset.replicate (xiMultiplicity ρ) ρ)

theorem count_xiZeroRadialCutoff (T : ℝ) (ρ : ℂ) :
    Multiset.count ρ (xiZeroRadialCutoff T) =
      if ‖ρ‖ ≤ T then xiMultiplicity ρ else 0 := by
  classical
  rw [xiZeroRadialCutoff, Multiset.count_bind]
  by_cases hnorm : ‖ρ‖ ≤ T
  · by_cases hzero : riemannXi ρ = 0
    · simp [Multiset.count_replicate, mem_xiZeroSupportFinset_iff,
        Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hnorm, hzero]
    · have hdiv : xiDivisor ρ = 0 := by
        apply not_ne_iff.mp
        exact fun h ↦ hzero ((xiDivisor_ne_zero_iff ρ).mp h)
      simp [Multiset.count_replicate, mem_xiZeroSupportFinset_iff,
        Function.mem_support, xiMultiplicity, hnorm, hdiv]
  · simp [Multiset.count_replicate, mem_xiZeroSupportFinset_iff,
      Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hnorm]

theorem xiZeroRadialCutoff_valid (T : ℝ) :
    ValidWeilZeroCutoff (xiZeroRadialCutoff T) := by
  intro ρ hρ
  have hcount : Multiset.count ρ (xiZeroRadialCutoff T) ≠ 0 :=
    Multiset.count_ne_zero.mpr hρ
  rw [count_xiZeroRadialCutoff] at hcount
  split at hcount
  · have hmult : xiMultiplicity ρ ≠ 0 := hcount
    have hdiv : xiDivisor ρ ≠ 0 := by
      intro h
      apply hmult
      simp [xiMultiplicity, h]
    have hzero := (xiDivisor_ne_zero_iff ρ).mp hdiv
    exact ⟨by intro h; subst ρ; norm_num [riemannXi_zero] at hzero,
      by intro h; subst ρ; norm_num [riemannXi_one] at hzero⟩
  · contradiction

theorem riemannXi_zero_re_mem_Ioo {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  have hzeta : riemannZeta ρ = 0 :=
    (riemannXi_eq_zero_iff_nontrivialZetaZero ρ).mp hρ |>.1
  constructor
  · by_contra h
    have hreflect : riemannXi (1 - ρ) = 0 := by
      rw [riemannXi_one_sub, hρ]
    have hzetaReflect : riemannZeta (1 - ρ) = 0 :=
      (riemannXi_eq_zero_iff_nontrivialZetaZero (1 - ρ)).mp hreflect |>.1
    exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - ρ) (by
      change 1 ≤ 1 - ρ.re
      linarith)) hzetaReflect
  · by_contra h
    exact (riemannZeta_ne_zero_of_one_le_re (s := ρ) (by linarith)) hzeta

/-- Xi-divisor support in Lagarias's height ordering. -/
def xiZeroSupportInHeightStrip (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ xiDivisor.support ∧ |ρ.im| ≤ T}

theorem xiZeroSupportInHeightStrip_finite (T : ℝ) :
    (xiZeroSupportInHeightStrip T).Finite := by
  let R := 1 + max T 0
  have hfinite : (closedBall (0 : ℂ) R ∩ xiDivisor.support).Finite :=
    xiDivisor.locallyFiniteSupport.finite_inter_support_of_isCompact
      (isCompact_closedBall (0 : ℂ) R)
  apply hfinite.subset
  intro ρ hρ
  have hzero := (mem_xiDivisor_support_iff ρ).mp hρ.1
  have hre := riemannXi_zero_re_mem_Ioo hzero
  constructor
  · rw [mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + max T 0 := by
        rw [abs_of_pos hre.1]
        exact add_le_add (le_of_lt hre.2) (hρ.2.trans (le_max_left _ _))
  · exact hρ.1

noncomputable def xiZeroHeightSupportFinset (T : ℝ) : Finset ℂ :=
  (xiZeroSupportInHeightStrip_finite T).toFinset

theorem mem_xiZeroHeightSupportFinset_iff (T : ℝ) (ρ : ℂ) :
    ρ ∈ xiZeroHeightSupportFinset T ↔
      ρ ∈ xiDivisor.support ∧ |ρ.im| ≤ T := by
  rw [xiZeroHeightSupportFinset, Set.Finite.mem_toFinset]
  rfl

/-- Lagarias's genuine height cutoff, retaining analytic multiplicity. -/
noncomputable def xiZeroHeightCutoff (T : ℝ) : Multiset ℂ :=
  (xiZeroHeightSupportFinset T).val.bind
    (fun ρ ↦ Multiset.replicate (xiMultiplicity ρ) ρ)

theorem count_xiZeroHeightCutoff (T : ℝ) (ρ : ℂ) :
    Multiset.count ρ (xiZeroHeightCutoff T) =
      if |ρ.im| ≤ T then xiMultiplicity ρ else 0 := by
  classical
  rw [xiZeroHeightCutoff, Multiset.count_bind]
  by_cases hheight : |ρ.im| ≤ T
  · by_cases hzero : riemannXi ρ = 0
    · simp [Multiset.count_replicate, mem_xiZeroHeightSupportFinset_iff,
        Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hheight, hzero]
    · have hdiv : xiDivisor ρ = 0 := by
        apply not_ne_iff.mp
        exact fun h ↦ hzero ((xiDivisor_ne_zero_iff ρ).mp h)
      simp [Multiset.count_replicate, mem_xiZeroHeightSupportFinset_iff,
        Function.mem_support, xiMultiplicity, hheight, hdiv]
  · simp [Multiset.count_replicate, mem_xiZeroHeightSupportFinset_iff,
      Function.mem_support, xiMultiplicity, xiDivisor_ne_zero_iff, hheight]

theorem xiZeroHeightCutoff_valid (T : ℝ) :
    ValidWeilZeroCutoff (xiZeroHeightCutoff T) := by
  intro ρ hρ
  have hcount : Multiset.count ρ (xiZeroHeightCutoff T) ≠ 0 :=
    Multiset.count_ne_zero.mpr hρ
  rw [count_xiZeroHeightCutoff] at hcount
  split at hcount
  · have hmult : xiMultiplicity ρ ≠ 0 := hcount
    have hdiv : xiDivisor ρ ≠ 0 := by
      intro h
      apply hmult
      simp [xiMultiplicity, h]
    have hzero := (xiDivisor_ne_zero_iff ρ).mp hdiv
    exact ⟨by intro h; subst ρ; norm_num [riemannXi_zero] at hzero,
      by intro h; subst ρ; norm_num [riemannXi_one] at hzero⟩
  · contradiction

@[simp] theorem weilReflect_im (ρ : ℂ) : (weilReflect ρ).im = ρ.im := by
  simp [weilReflect]

@[simp] theorem abs_im_weilReflect (ρ : ℂ) :
    |(weilReflect ρ).im| = |ρ.im| := by simp

private theorem iteratedDeriv_conj_conj' (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ iteratedDeriv m f ∘ starRingEnd ℂ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih, deriv_conj_conj]

theorem iteratedDeriv_riemannXi_conj (m : ℕ) (ρ : ℂ) :
    iteratedDeriv m riemannXi (starRingEnd ℂ ρ) =
      starRingEnd ℂ (iteratedDeriv m riemannXi ρ) := by
  have hfun : starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ = riemannXi := by
    funext z
    simp [Function.comp_def]
  have h := congrFun (iteratedDeriv_conj_conj' riemannXi m)
    (starRingEnd ℂ ρ)
  rw [hfun] at h
  simpa [Function.comp_def] using h

theorem analyticOrderNatAt_riemannXi_conj (ρ : ℂ) :
    analyticOrderNatAt riemannXi (starRingEnd ℂ ρ) =
      analyticOrderNatAt riemannXi ρ := by
  apply Nat.le_antisymm
  · rw [← ENat.natCast_le_natCast,
      Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _),
      Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _),
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top
        (starRingEnd ℂ ρ)),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_riemannXi ρ)]
    intro i hi
    have hself : (analyticOrderNatAt riemannXi (starRingEnd ℂ ρ) : ℕ∞) ≤
        analyticOrderAt riemannXi (starRingEnd ℂ ρ) := by
      rw [Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _)]
    have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannXi (starRingEnd ℂ ρ))).mp hself i hi
    rw [iteratedDeriv_riemannXi_conj] at hzero
    exact (map_eq_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mp hzero
  · rw [← ENat.natCast_le_natCast,
      Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _),
      Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _),
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top ρ),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (analyticAt_riemannXi (starRingEnd ℂ ρ))]
    intro i hi
    rw [iteratedDeriv_riemannXi_conj]
    have hself : (analyticOrderNatAt riemannXi ρ : ℕ∞) ≤
        analyticOrderAt riemannXi ρ := by
      rw [Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top _)]
    exact (map_eq_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (analyticAt_riemannXi ρ)).mp hself i hi)

theorem xiMultiplicity_eq_analyticOrderNatAt (ρ : ℂ) :
    xiMultiplicity ρ = analyticOrderNatAt riemannXi ρ := by
  apply Int.ofNat_injective
  change (xiMultiplicity ρ : ℤ) = (analyticOrderNatAt riemannXi ρ : ℤ)
  rw [xiMultiplicity_cast, xiDivisor_apply]
  rw [show analyticOrderAt riemannXi ρ =
      (analyticOrderNatAt riemannXi ρ : ℕ∞) by
    exact (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_riemannXi_ne_top ρ)).symm]
  simp

theorem xiMultiplicity_conj (ρ : ℂ) :
    xiMultiplicity (starRingEnd ℂ ρ) = xiMultiplicity ρ := by
  simp only [xiMultiplicity_eq_analyticOrderNatAt,
    analyticOrderNatAt_riemannXi_conj]

theorem xiMultiplicity_one_sub (ρ : ℂ) :
    xiMultiplicity (1 - ρ) = xiMultiplicity ρ := by
  rw [xiMultiplicity_eq_analyticOrderNatAt,
    xiMultiplicity_eq_analyticOrderNatAt]
  let g : ℂ → ℂ := fun z ↦ 1 - z
  have hg : AnalyticAt ℂ g ρ := by fun_prop
  have hg' : deriv g ρ ≠ 0 := by simp [g]
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := riemannXi) hg hg'
  have hfun : riemannXi ∘ g = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  rw [hfun] at hcomp
  exact congrArg ENat.toNat (by simpa [g] using hcomp.symm)

theorem xiMultiplicity_weilReflect (ρ : ℂ) :
    xiMultiplicity (weilReflect ρ) = xiMultiplicity ρ := by
  rw [weilReflect, xiMultiplicity_one_sub, xiMultiplicity_conj]

/-- The genuine Lagarias height cutoff is exactly reflection-stable, including
analytic multiplicities. -/
theorem xiZeroHeightCutoff_reflectionStable (T : ℝ) :
    WeilReflectionStable (xiZeroHeightCutoff T) := by
  unfold WeilReflectionStable
  rw [Multiset.ext]
  intro ρ
  have hinj : Function.Injective weilReflect := by
    intro x y h
    have := congrArg weilReflect h
    simpa [weilReflect] using this
  have hmap := Multiset.count_map_eq_count' weilReflect
    (xiZeroHeightCutoff T) hinj (weilReflect ρ)
  have hcountReflect :
      Multiset.count ρ ((xiZeroHeightCutoff T).map weilReflect) =
        Multiset.count (weilReflect ρ) (xiZeroHeightCutoff T) := by
    simpa [weilReflect] using hmap
  rw [hcountReflect, count_xiZeroHeightCutoff, count_xiZeroHeightCutoff]
  simp [xiMultiplicity_weilReflect]

theorem finiteWeilScalar_heightCutoff_self_eq_two_re (T : ℝ) (n : ℤ) :
    finiteWeilScalar (xiZeroHeightCutoff T) (weilLiTest n) (weilLiTest n) =
      (2 * (finiteLiZeroValue (xiZeroHeightCutoff T) n).re : ℂ) :=
  finiteWeilScalar_liTest_self_eq_two_re _ (xiZeroHeightCutoff_valid T)
    (xiZeroHeightCutoff_reflectionStable T) n

/-- Lagarias's finite height-ordered star partial sum, with analytic multiplicity. -/
noncomputable def liStarPartial (T : ℝ) (n : ℤ) : ℂ :=
  finiteLiZeroValue (xiZeroHeightCutoff T) n

/-- The exact height-limit proposition used by Lagarias's star convention. -/
def LiStarConvergesTo (n : ℤ) (L : ℂ) : Prop :=
  Tendsto (fun T : ℝ ↦ liStarPartial T n) atTop (nhds L)

def ClassicalLiEqualsNegativeStar : Prop :=
  ∀ k : ℕ, LiStarConvergesTo (-((k + 1 : ℕ) : ℤ)) (classicalLiCoefficient k)

def StarLiSymmetry : Prop :=
  ∀ (n : ℤ) (L : ℂ), LiStarConvergesTo n L → LiStarConvergesTo (-n) L

theorem norm_weilReflect_le (ρ : ℂ) : ‖weilReflect ρ‖ ≤ ‖ρ‖ + 1 := by
  rw [weilReflect]
  calc
    ‖1 - starRingEnd ℂ ρ‖ ≤ ‖(1 : ℂ)‖ + ‖starRingEnd ℂ ρ‖ := norm_sub_le _ _
    _ = ‖ρ‖ + 1 := by simp [add_comm]

theorem norm_le_norm_weilReflect_add_one (ρ : ℂ) :
    ‖ρ‖ ≤ ‖weilReflect ρ‖ + 1 := by
  have hreflect : weilReflect (weilReflect ρ) = ρ := by
    simp [weilReflect]
  simpa [hreflect] using norm_weilReflect_le (weilReflect ρ)

theorem norm_weilReflect_sub_norm_le_one (ρ : ℂ) :
    |‖weilReflect ρ‖ - ‖ρ‖| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [norm_weilReflect_le ρ,
    norm_le_norm_weilReflect_add_one ρ]

end RHGarden
