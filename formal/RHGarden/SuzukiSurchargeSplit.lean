import RHGarden.SuzukiHigherPowerTail
import RHGarden.SuzukiSquareAbel

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Certified finite reindexing of the surcharge into squares and higher powers. -/
noncomputable section
open scoped BigOperators
namespace RHGarden
attribute [local instance] Classical.propDecidable

def IsSuzukiPrimeSquare (q : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ p ^ 2 = q
def IsSuzukiHigherPower (q : ℕ) : Prop := ∃ i : SuzukiHigherPowerIndex, suzukiHigherPowerValue i = q

theorem primeSquare_not_higherPower {q : ℕ} (hq : IsSuzukiPrimeSquare q) :
    ¬ IsSuzukiHigherPower q := by
  rintro ⟨⟨p, n⟩, hn⟩
  obtain ⟨r, hr, he⟩ := hq
  have h := hr.pow_inj' p.property (by norm_num : (2 : ℕ) ≠ 0)
    (by omega : n + 3 ≠ 0) (he.trans hn.symm)
  omega

theorem overcharge_square_higher_split (q : ℕ) :
    suzukiPrimePowerOvercharge q =
      (if IsSuzukiPrimeSquare q then suzukiPrimePowerOvercharge q else 0) +
      (if IsSuzukiHigherPower q then suzukiPrimePowerOvercharge q else 0) := by
  classical
  by_cases hz : suzukiPrimePowerOvercharge q = 0
  · simp [hz]
  have hpositive : 0 < suzukiPrimePowerOvercharge q :=
    lt_of_le_of_ne (suzukiPrimePowerOvercharge_nonneg q) (Ne.symm hz)
  obtain ⟨p, k, hp, hk, rfl⟩ := (suzukiPrimePowerOvercharge_pos_iff q).mp hpositive
  by_cases hk2 : k = 2
  · subst k
    have hs : IsSuzukiPrimeSquare (p ^ 2) := ⟨p, hp, rfl⟩
    simp [hs, primeSquare_not_higherPower hs]
  · have hh : IsSuzukiHigherPower (p ^ k) := by
      refine ⟨(⟨p, hp⟩, k - 3), ?_⟩
      dsimp [suzukiHigherPowerValue]
      rw [Nat.sub_add_cancel (by omega)]
    have hs : ¬ IsSuzukiPrimeSquare (p ^ k) := fun h => primeSquare_not_higherPower h hh
    simp [hs, hh]

theorem prime_square_weight {p : ℕ} (hp : p.Prime) :
    suzukiPrimePowerOvercharge (p ^ 2) = Real.log p / p := by
  rw [suzukiPrimePowerOvercharge_prime_pow hp (by norm_num), Nat.cast_pow,
    Real.sqrt_sq (Nat.cast_nonneg p)]
  norm_num

theorem prime_square_window_mem {m p : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    p ^ 2 ∈ Finset.Ioc m ⌊x⌋₊ ↔
      p ∈ Finset.Ioc ⌊Real.sqrt (m : ℝ)⌋₊ ⌊Real.sqrt x⌋₊ := by
  rw [Finset.mem_Ioc, Finset.mem_Ioc, Nat.floor_lt (Real.sqrt_nonneg _),
    Nat.le_floor_iff hx, Nat.le_floor_iff (Real.sqrt_nonneg _)]
  constructor
  · intro h
    constructor
    · apply (Real.sqrt_lt (Nat.cast_nonneg m) (Nat.cast_nonneg p)).mpr
      exact_mod_cast h.1
    · apply (Real.le_sqrt (Nat.cast_nonneg p) hx).mpr
      exact_mod_cast h.2
  · intro h
    constructor
    · have := (Real.sqrt_lt (Nat.cast_nonneg m) (Nat.cast_nonneg p)).mp h.1
      exact_mod_cast this
    · have := (Real.le_sqrt (Nat.cast_nonneg p) hx).mp h.2
      exact_mod_cast this

/-- Actual reindexing of the square events, not an assumed identification. -/
theorem primeSquareWindow_eq_reciprocal (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ q ∈ (Finset.Ioc m ⌊x⌋₊).filter IsSuzukiPrimeSquare, suzukiPrimePowerOvercharge q) =
      suzukiPrimeReciprocalWindow (Real.sqrt m) (Real.sqrt x) := by
  classical
  unfold suzukiPrimeReciprocalWindow
  symm
  apply Finset.sum_bij (fun p _ => p ^ 2)
  · intro p hp
    obtain ⟨hpm, hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(prime_square_window_mem hx).mpr hpm, ⟨p, hp, rfl⟩⟩
  · intro p hp r hr he
    exact (Nat.pow_left_inj (by norm_num : (2 : ℕ) ≠ 0)).mp he
  · intro q hq
    obtain ⟨hqm, p, hp, rfl⟩ := Finset.mem_filter.mp hq
    exact ⟨p, Finset.mem_filter.mpr ⟨(prime_square_window_mem hx).mp hqm, hp⟩, rfl⟩
  · intro p hp
    exact (prime_square_weight (Finset.mem_filter.mp hp).2).symm

def suzukiHigherPowerWindow (m : ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ q ∈ (Finset.Ioc m ⌊x⌋₊).filter IsSuzukiHigherPower, suzukiPrimePowerOvercharge q

theorem primePowerDelta_eq_square_add_higher (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    suzukiPrimePowerDelta m x =
      suzukiPrimeReciprocalWindow (Real.sqrt m) (Real.sqrt x) + suzukiHigherPowerWindow m x := by
  classical
  rw [← primeSquareWindow_eq_reciprocal m hx]
  unfold suzukiPrimePowerDelta suzukiHigherPowerWindow
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => overcharge_square_higher_split q)

theorem higherPowerWindow_nonneg (m : ℕ) (x : ℝ) : 0 ≤ suzukiHigherPowerWindow m x := by
  classical
  exact Finset.sum_nonneg (fun q _ => suzukiPrimePowerOvercharge_nonneg q)

theorem higherPowerWindow_le_tail (m : ℕ) (x : ℝ) :
    suzukiHigherPowerWindow m x ≤ suzukiHigherPowerTail m := by
  classical
  let t := (Finset.Ioc m ⌊x⌋₊).preimage suzukiHigherPowerValue
    suzukiHigherPowerValue_injective.injOn
  have he : suzukiHigherPowerWindow m x = ∑ i ∈ t, suzukiHigherPowerMass i := by
    symm
    apply Finset.sum_bij (fun i _ => suzukiHigherPowerValue i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_preimage.mp hi, ⟨i, rfl⟩⟩
    · intro i _ j _ hij
      exact suzukiHigherPowerValue_injective hij
    · intro q hq
      obtain ⟨hqm, i, rfl⟩ := Finset.mem_filter.mp hq
      exact ⟨i, Finset.mem_preimage.mpr hqm, rfl⟩
    · intro i _
      rfl
  rw [he]
  apply higherPower_window_le_tail
  intro i hi
  exact (Finset.mem_Ioc.mp (Finset.mem_preimage.mp hi)).1

end RHGarden
