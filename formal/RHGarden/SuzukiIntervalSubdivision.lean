import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Copyright (c) 2026 Future Technologies Laboratory LLC.
Finite subdivision only: no short-interval arithmetic theorem is assumed proved. -/
namespace RHGarden
open Set

theorem increment_le_of_equal_subdivision {f : ℝ → ℝ} {a h c : ℝ} {k : ℕ}
    (hk : 0 < k)
    (hb : ∀ i : ℕ, i < k →
      f (a + (i + 1) * (h / k)) - f (a + i * (h / k)) ≤ c * (h / k)) :
    f (a + h) - f a ≤ c * h := by
  have hpartial : ∀ j : ℕ, j ≤ k →
      f (a + j * (h / k)) - f a ≤ c * (j * (h / k)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hs := hb j (by omega)
      have hi := ih (by omega)
      push_cast
      nlinarith
  have he : (k : ℝ) * (h / k) = h := by field_simp
  simpa [he] using hpartial k le_rfl

/-- Bounds on all blocks of lengths [H,2H] extend to every length at least H.
The premise includes the translated block anchors, not just the original anchor. -/
theorem increment_le_of_block_range {f : ℝ → ℝ} {a H h c : ℝ}
    (hH : 0 < H) (hHh : H ≤ h)
    (hb : ∀ y ∈ Icc a (a + h), ∀ t ∈ Icc H (2 * H),
      y + t ≤ a + h → f (y + t) - f y ≤ c * t) :
    f (a + h) - f a ≤ c * h := by
  let k := ⌊h / H⌋₊
  have hh : 0 < h := hH.trans_le hHh
  have hratio : 1 ≤ h / H := (le_div_iff₀ hH).mpr (by simpa)
  have hk : 0 < k := Nat.floor_pos.mpr hratio
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkle : (k : ℝ) ≤ h / H := Nat.floor_le (by positivity)
  have hkgt : h / H < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdlo : H ≤ h / k := by
    apply (le_div_iff₀ hkR).mpr
    have := (le_div_iff₀ hH).mp hkle
    nlinarith
  have hdhi : h / k ≤ 2 * H := by
    apply (div_le_iff₀ hkR).mpr
    have := (div_lt_iff₀ hH).mp hkgt
    nlinarith
  apply increment_le_of_equal_subdivision hk
  intro i hi
  have hiR : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  have hd0 : 0 ≤ h / k := by positivity
  have his : ((i : ℝ) + 1) * (h / k) ≤ h := by
    calc
      _ ≤ (k : ℝ) * (h / k) := mul_le_mul_of_nonneg_right hiR hd0
      _ = h := by field_simp
  have hi0 : 0 ≤ (i : ℝ) * (h / k) := by positivity
  have hb' := hb (a + i * (h / k)) ⟨by linarith, by nlinarith⟩
    (h / k) ⟨hdlo, hdhi⟩ (by nlinarith)
  have he : a + (i + 1) * (h / (k : ℝ)) = a + i * (h / k) + h / k := by ring
  simpa only [he] using hb'

/-- A purely geometric overlap threshold, unrelated to the arithmetic cutoff. -/
theorem threeFifths_blocks_fit_point99 {a h : ℝ}
    (ha : 64 ≤ a) (hh0 : 0 ≤ h) (hh : h ≤ a / 8) :
    2 * (a + h) ^ (3 / 5 : ℝ) ≤ a ^ (99 / 100 : ℝ) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hfour : (4 : ℝ) ≤ a ^ (1 / 3 : ℝ) := by
    have hb := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4 ^ 3)
      (by norm_num; exact ha : (4 : ℝ) ^ 3 ≤ a) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have he : ((4 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 4 := by
      rw [← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rwa [he] at hb
  have hgap : (9 / 4 : ℝ) ≤ a ^ (39 / 100 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num : (1 / 3 : ℝ) ≤ 39 / 100)
    linarith
  calc
    _ ≤ 2 * ((9 / 8 : ℝ) * a) ^ (3 / 5 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ = 2 * (9 / 8 : ℝ) ^ (3 / 5 : ℝ) * a ^ (3 / 5 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) ha0.le]; ring
    _ ≤ (9 / 4 : ℝ) * a ^ (3 / 5 : ℝ) := by
      have hb := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 9 / 8)
        (by norm_num : (3 / 5 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ha0.le (3 / 5 : ℝ))]
    _ ≤ a ^ (39 / 100 : ℝ) * a ^ (3 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg ha0.le _)
    _ = _ := by rw [← Real.rpow_add ha0]; norm_num

/-- Conditional adapter of the source's .99 upper restriction by proved subdivision.
It requires all translated real anchors, and asserts no arithmetic premise. -/
theorem increment_le_from_threeFifths_to_point99 {f : ℝ → ℝ} {a h c : ℝ}
    (ha : 64 ≤ a) (hlo : a ^ (3 / 5 : ℝ) ≤ h) (hhi : h ≤ a / 8)
    (hb : ∀ y ∈ Icc a (a + h), ∀ t ∈ Icc (y ^ (3 / 5 : ℝ)) (y ^ (99 / 100 : ℝ)),
      f (y + t) - f y ≤ c * t) :
    f (a + h) - f a ≤ c * h := by
  have ha0 : 0 < a := by linarith
  have hh : 0 < h := (Real.rpow_pos_of_pos ha0 _).trans_le hlo
  by_cases hsmall : h ≤ a ^ (99 / 100 : ℝ)
  · exact hb a ⟨le_rfl, by linarith⟩ h ⟨hlo, hsmall⟩
  let H := (a + h) ^ (3 / 5 : ℝ)
  have hH : 0 < H := Real.rpow_pos_of_pos (by linarith) _
  have hgeom := threeFifths_blocks_fit_point99 ha hh.le hhi
  have hHh : H ≤ h := by dsimp [H] at *; linarith
  apply increment_le_of_block_range hH hHh
  intro y hy t ht _
  apply hb y hy t
  constructor
  · exact (Real.rpow_le_rpow (by linarith [hy.1]) hy.2 (by norm_num)).trans ht.1
  · exact (ht.2.trans hgeom).trans (Real.rpow_le_rpow ha0.le hy.1 (by norm_num))

end RHGarden
