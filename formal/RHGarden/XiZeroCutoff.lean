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
noncomputable def xiZeroCutoff (T : ℝ) : Multiset ℂ :=
  (xiZeroSupportFinset T).val.bind
    (fun ρ ↦ Multiset.replicate (xiMultiplicity ρ) ρ)

theorem count_xiZeroCutoff (T : ℝ) (ρ : ℂ) :
    Multiset.count ρ (xiZeroCutoff T) =
      if ‖ρ‖ ≤ T then xiMultiplicity ρ else 0 := by
  classical
  rw [xiZeroCutoff, Multiset.count_bind]
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

theorem xiZeroCutoff_valid (T : ℝ) :
    ValidWeilZeroCutoff (xiZeroCutoff T) := by
  intro ρ hρ
  have hcount : Multiset.count ρ (xiZeroCutoff T) ≠ 0 :=
    Multiset.count_ne_zero.mpr hρ
  rw [count_xiZeroCutoff] at hcount
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

/-- Lagarias's finite radial star partial sum, with analytic multiplicity. -/
noncomputable def liStarPartial (T : ℝ) (n : ℤ) : ℂ :=
  finiteLiZeroValue (xiZeroCutoff T) n

/-- The exact radial-limit proposition used by Lagarias's star convention. -/
def LiStarConvergesTo (n : ℤ) (L : ℂ) : Prop :=
  Tendsto (fun T : ℝ ↦ liStarPartial T n) atTop (nhds L)

/-- Open target: Li's derivative coefficient initially matches Lagarias's
negative-index star coefficient. -/
def ClassicalLiEqualsNegativeStar : Prop :=
  ∀ k : ℕ, LiStarConvergesTo (-((k + 1 : ℕ) : ℤ)) (classicalLiCoefficient k)

/-- Open target separating the positive/negative-index star symmetry step. -/
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
