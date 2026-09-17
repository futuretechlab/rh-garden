import RHGarden.SuzukiSurchargeSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
The absolutely summable higher-prime-power mass and its moving arithmetic tail. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RHGarden

abbrev SuzukiHigherPowerIndex := {p : ℕ // p.Prime} × ℕ

def suzukiHigherPowerValue (i : SuzukiHigherPowerIndex) : ℕ := i.1.val ^ (i.2 + 3)

def suzukiHigherPowerMass (i : SuzukiHigherPowerIndex) : ℝ :=
  suzukiPrimePowerOvercharge (suzukiHigherPowerValue i)

theorem suzukiHigherPowerValue_injective : Function.Injective suzukiHigherPowerValue := by
  intro ⟨p, k⟩ ⟨q, l⟩ h
  have he := p.property.pow_inj' q.property (by omega : k + 3 ≠ 0)
    (by omega : l + 3 ≠ 0) h
  obtain ⟨hp, hk⟩ := he
  have : p = q := Subtype.ext hp
  subst q
  have : k = l := by omega
  subst l
  rfl

theorem summable_higherPowerMass : Summable suzukiHigherPowerMass := by
  apply (summable_prod_of_nonneg (fun i => suzukiPrimePowerOvercharge_nonneg _)).mpr
  refine ⟨fun p => (summable_higher_primePower_overcharge p.property).1, ?_⟩
  have hmajor := (summable_log_div_threeHalves.mul_left 32).subtype Nat.Prime
  apply Summable.of_nonneg_of_le (fun p => tsum_nonneg (fun _ =>
    suzukiPrimePowerOvercharge_nonneg _)) _ hmajor
  intro p
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have he : (Real.sqrt (p.val : ℝ))⁻¹ ^ 3 = 1 / (p.val : ℝ) ^ (3 / 2 : ℝ) := by
    rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hp0.le]
    norm_num
  have hb := (summable_higher_primePower_overcharge p.property).2
  dsimp [suzukiHigherPowerMass, suzukiHigherPowerValue]
  rw [he] at hb
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hb

/-- Total mass of all exponent-at-least-three events strictly after the anchor.
This is an exact convergent sum, not an effective numerical enclosure. -/
def suzukiHigherPowerTail (m : ℕ) : ℝ :=
  ∑' i : SuzukiHigherPowerIndex,
    if m < suzukiHigherPowerValue i then suzukiHigherPowerMass i else 0

theorem suzukiHigherPowerTail_nonneg (m : ℕ) : 0 ≤ suzukiHigherPowerTail m := by
  apply tsum_nonneg
  intro i
  split_ifs <;> first | exact le_refl 0 | exact suzukiPrimePowerOvercharge_nonneg _

theorem summable_higherPowerTail (m : ℕ) : Summable (fun i : SuzukiHigherPowerIndex =>
    if m < suzukiHigherPowerValue i then suzukiHigherPowerMass i else 0) := by
  apply Summable.of_nonneg_of_le _ _ summable_higherPowerMass
  · intro i
    split_ifs <;> first | exact le_refl 0 | exact suzukiPrimePowerOvercharge_nonneg _
  · intro i
    split_ifs <;> first | exact le_refl _ | exact suzukiPrimePowerOvercharge_nonneg _

theorem tendsto_suzukiHigherPowerTail :
    Tendsto suzukiHigherPowerTail atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop (α := ℕ))
    (f := fun m (i : SuzukiHigherPowerIndex) =>
      if m < suzukiHigherPowerValue i then suzukiHigherPowerMass i else 0)
    (g := fun _ => (0 : ℝ)) summable_higherPowerMass
  simp only [tsum_zero] at h
  apply h
  · intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (suzukiHigherPowerValue i)] with m hm
    simp [not_lt.mpr hm]
  · apply Filter.Eventually.of_forall
    intro m i
    rw [Real.norm_eq_abs]
    split_ifs
    · exact le_of_eq (abs_of_nonneg (suzukiPrimePowerOvercharge_nonneg _))
    · simpa [suzukiHigherPowerMass] using suzukiPrimePowerOvercharge_nonneg (suzukiHigherPowerValue i)

/-- Every finite selection of higher powers after m is bounded by the same moving tail. -/
theorem higherPower_window_le_tail (m : ℕ) (t : Finset SuzukiHigherPowerIndex)
    (ht : ∀ i ∈ t, m < suzukiHigherPowerValue i) :
    ∑ i ∈ t, suzukiHigherPowerMass i ≤ suzukiHigherPowerTail m := by
  have he : (∑ i ∈ t, suzukiHigherPowerMass i) =
      ∑ i ∈ t, if m < suzukiHigherPowerValue i then suzukiHigherPowerMass i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (ht i hi)]
  rw [he]
  exact (summable_higherPowerTail m).sum_le_tsum t (fun i _ => by
    split_ifs <;> first | exact le_refl 0 | exact suzukiPrimePowerOvercharge_nonneg _)

end RHGarden
