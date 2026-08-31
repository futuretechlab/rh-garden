import RHGarden.LiCombinatorics
import Mathlib.Data.Fintype.Powerset

noncomputable section
namespace RHGarden

theorem compositionAsSetEquiv_card_add_one (n : ℕ) (c : CompositionAsSet (n + 1)) :
    (compositionAsSetEquiv (n + 1) c).card + 1 = c.length := by
  let e := compositionAsSetEquiv (n + 1)
  obtain ⟨s, rfl⟩ := e.symm.surjective c
  let emb : Fin n ↪ Fin (n + 2) :=
    ⟨fun j => ⟨j + 1, by omega⟩, by intro a b h; ext; simpa using congrArg Fin.val h⟩
  have hbound :
      ({i : Fin (n + 2) |
          i = 0 ∨ i = Fin.last (n + 1) ∨
            ∃ (j : Fin n) (_hj : j ∈ s), (i : ℕ) = j + 1}.toFinset) =
        insert 0 (insert (Fin.last (n + 1)) (s.map emb)) := by
    ext i
    simp only [Set.toFinset_ofPred, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro (h | h | ⟨j, hj, hval⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j, hj, by
          ext
          change (j : ℕ) + 1 = (i : ℕ)
          exact hval.symm⟩)
    · rintro (h | h | ⟨j, hj, hji⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j, hj, by
          change (i : ℕ) = (j : ℕ) + 1
          exact congrArg Fin.val hji.symm⟩)
  simp only [e, Equiv.apply_symm_apply]
  change s.card + 1 =
    ({i : Fin (n + 2) |
        i = 0 ∨ i = Fin.last (n + 1) ∨
          ∃ (j : Fin n) (_hj : j ∈ s), (i : ℕ) = j + 1}.toFinset).card - 1
  rw [hbound]
  have hzero : (0 : Fin (n + 2)) ∉ s.map emb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro j _
    intro h
    have hv := congrArg Fin.val h
    change (j : ℕ) + 1 = 0 at hv
    omega
  have hlast : Fin.last (n + 1) ∉ s.map emb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro j _
    intro h
    have hv := congrArg Fin.val h
    change (j : ℕ) + 1 = n + 1 at hv
    have hj := j.isLt
    omega
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem hlast, Finset.card_map]
    omega
  · simp [hzero, hlast, Fin.ext_iff]

theorem card_composition_succ_length_succ (n k : ℕ) :
    Fintype.card {c : Composition (n + 1) // c.length = k + 1} =
      Nat.choose n k := by
  let e : Composition (n + 1) ≃ Finset (Fin n) :=
    (compositionEquiv (n + 1)).trans (compositionAsSetEquiv (n + 1))
  let er : {c : Composition (n + 1) // c.length = k + 1} ≃
      {s : Finset (Fin n) // s.card = k} :=
    e.subtypeEquiv (fun c => by
      have h := compositionAsSetEquiv_card_add_one n c.toCompositionAsSet
      simp only [Composition.toCompositionAsSet_length] at h
      change ((compositionAsSetEquiv (n + 1))
        ((compositionEquiv (n + 1)) c)).card + 1 = c.length at h
      have he : (e c).card + 1 = c.length := by simpa [e] using h
      change c.length = k + 1 ↔ (e c).card = k
      omega)
  rw [Fintype.card_congr er, Fintype.card_finset_len, Fintype.card_fin]

theorem sum_composition_by_length (q : ℕ → ℂ) (n : ℕ) :
    ∑ c : Composition (n + 1), q c.length =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) * q (k + 1) := by
  let e : Composition (n + 1) ≃ Finset (Fin n) :=
    (compositionEquiv (n + 1)).trans (compositionAsSetEquiv (n + 1))
  have helen (c : Composition (n + 1)) : (e c).card + 1 = c.length := by
    have h := compositionAsSetEquiv_card_add_one n c.toCompositionAsSet
    simp only [Composition.toCompositionAsSet_length] at h
    change ((compositionAsSetEquiv (n + 1))
      ((compositionEquiv (n + 1)) c)).card + 1 = c.length at h
    simpa [e] using h
  rw [Fintype.sum_equiv e (fun c => q c.length) (fun s => q (s.card + 1))
    (fun c => by rw [helen])]
  let g : Finset (Fin n) → Fin (n + 1) := fun s =>
    ⟨s.card, Nat.lt_succ_iff.mpr (s.card_le_univ.trans_eq (Finset.card_fin n))⟩
  rw [← Finset.sum_fiberwise Finset.univ g (fun s => q (s.card + 1))]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n + 1 := Finset.mem_range.mp hk
  simp only [dif_pos hklt]
  rw [Finset.sum_congr rfl (fun s hs => by
    have hcard : s.card = k := by simpa [g] using hs
    rw [hcard])]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  change ((Finset.univ.filter fun s : Finset (Fin n) => g s = ⟨k, hklt⟩).card : ℂ) *
      q (k + 1) = _
  congr 1
  norm_cast
  simpa [g, Fin.ext_iff, Fintype.card_subtype, Fintype.card_fin] using
    (Fintype.card_finset_len (α := Fin n) k)

open PowerSeries

theorem coeff_comp_liMobiusFMS (q : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ q).comp
      liMobiusFPowerSeries).coeff (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) * q (k + 1) := by
  rw [show ((FormalMultilinearSeries.ofScalars ℂ q).comp
      liMobiusFPowerSeries).coeff (n + 1) =
      ∑ c : Composition (n + 1), q c.length by
    simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.comp]
    simp only [ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro c _
    simp [FormalMultilinearSeries.applyComposition,
      liMobiusFPowerSeries,
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun _))]]
  exact sum_composition_by_length q n

theorem coeff_subst_liMobius_binomial (H : PowerSeries ℂ) (n : ℕ) :
    coeff (n + 1) (H.subst liMobiusSeries) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * coeff (k + 1) H := by
  rw [PowerSeries.coeff_subst' liMobiusSeries_hasSubst]
  simp_rw [coeff_liMobiusSeries_pow]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 2)) (by
    intro k hk
    simp only [Function.mem_support] at hk
    by_contra hkrange
    have hklarge : n + 2 ≤ k := by simpa using hkrange
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero,
      smul_zero] at hk
    exact hk rfl)]
  rw [Finset.sum_range_succ']
  simp only [if_pos, smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  simp [smul_eq_mul, mul_comm]

theorem coeff_comp_liMobiusFMS_eq_subst
    (q : ℕ → ℂ) (H : PowerSeries ℂ)
    (hcoeff : ∀ k, q k = coeff k H) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ q).comp
      liMobiusFPowerSeries).coeff n =
      coeff n (H.subst liMobiusSeries) := by
  cases n with
  | zero =>
      have hleft : ((FormalMultilinearSeries.ofScalars ℂ q).comp
          liMobiusFPowerSeries).coeff 0 = q 0 := by
        rw [FormalMultilinearSeries.coeff]
        rw [FormalMultilinearSeries.comp_coeff_zero']
        simp [FormalMultilinearSeries.ofScalars]
      rw [hleft, hcoeff]
      rw [PowerSeries.coeff_subst' liMobiusSeries_hasSubst]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_pow, liMobiusSeries_constantCoeff, smul_eq_mul]
      have hf : (∑ᶠ d : ℕ, coeff d H * 0 ^ d) = coeff 0 H := by
        rw [finsum_eq_single (fun d : ℕ => coeff d H * 0 ^ d) 0]
        · simp
        · intro b hb
          simp [zero_pow hb]
      rw [hf, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
      rw [coeff_comp_liMobiusFMS q n, coeff_subst_liMobius_binomial H n]
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoeff]

theorem liGeneratingLogFPowerSeries_coeff_eq_subst (k : ℕ) :
    liGeneratingLogFPowerSeries.coeff k =
      coeff k (liLocalLogTaylor.subst liMobiusSeries) := by
  apply coeff_comp_liMobiusFMS_eq_subst
  intro j
  simp [liLocalLogTaylor]

theorem liXiSeries_eq_certifiedLiXiSeries :
    liXiSeries = certifiedLiXiSeries := by
  apply PowerSeries.ext
  intro k
  rw [liXiSeries, certifiedLiXiSeries, analyticLiXiPowerSeries_coeff]
  symm
  apply coeff_comp_liMobiusFMS_eq_subst
  intro j
  simp [normalizedXiTaylor]

theorem coeff_one_add_pow_mul_liLocalLogTaylor (n : ℕ) :
    coeff (n + 1) ((1 + X) ^ n * liLocalLogTaylor) =
      iteratedDeriv (n + 1) (fun u : ℂ => (1 + u) ^ n * liLocalLog u) 0 /
        ((n + 1).factorial : ℂ) := by
  rw [PowerSeries.coeff_mul]
  change (∑ p ∈ Finset.antidiagonal (n + 1),
      coeff p.1 ((1 + X) ^ n : PowerSeries ℂ) * coeff p.2 liLocalLogTaylor) = _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_one_add_X_pow]
  simp_rw [show ∀ j, coeff j liLocalLogTaylor =
      iteratedDeriv j liLocalLog 0 / (j.factorial : ℂ) by
    intro j; simp [liLocalLogTaylor]]
  change _ = iteratedDeriv (n + 1)
      ((fun u : ℂ => (1 + u) ^ n) * liLocalLog) 0 / ((n + 1).factorial : ℂ)
  rw [iteratedDeriv_mul]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show iteratedDeriv i (fun u : ℂ => (1 + u) ^ n) 0 =
        (n.descFactorial i : ℂ) by
      simpa [Function.comp_def] using
        congrFun (iteratedDeriv_comp_const_add i (fun u : ℂ => u ^ n) 1) 0]
    by_cases hin : i ≤ n
    · have hi' : i ≤ n + 1 := by omega
      have hid : n.choose i * (n + 1).factorial =
          (n + 1).choose i * n.descFactorial i * (n + 1 - i).factorial := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        calc
          n.choose i * (n + 1).factorial =
              n.choose i * ((n + 1).choose i * i.factorial *
                (n + 1 - i).factorial) := by
                  rw [Nat.choose_mul_factorial_mul_factorial hi']
          _ = (n + 1).choose i * (i.factorial * n.choose i) *
                (n + 1 - i).factorial := by ring
      have hfac : ((n + 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero (n + 1))
      have hsubfac : ((n + 1 - i).factorial : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero (n + 1 - i))
      have hidc : (n.choose i : ℂ) * ((n + 1).factorial : ℂ) =
          ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
            ((n + 1 - i).factorial : ℂ) := by
        exact_mod_cast hid
      field_simp
      calc
        (n.choose i : ℂ) * iteratedDeriv (n + 1 - i) liLocalLog 0 *
            ((n + 1).factorial : ℂ) =
          iteratedDeriv (n + 1 - i) liLocalLog 0 *
            ((n.choose i : ℂ) * ((n + 1).factorial : ℂ)) := by ring
        _ = iteratedDeriv (n + 1 - i) liLocalLog 0 *
            (((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
              ((n + 1 - i).factorial : ℂ)) := by rw [hidc]
        _ = iteratedDeriv (n + 1 - i) liLocalLog 0 *
            ((n + 1 - i).factorial : ℂ) * ((n + 1).choose i : ℂ) *
              (n.descFactorial i : ℂ) := by ring
    · have hieq : i = n + 1 := by
        have := Finset.mem_range.mp hi
        omega
      subst i
      simp [Nat.descFactorial_eq_zero_iff_lt]
  · fun_prop
  · exact analyticAt_liLocalLog.contDiffAt

theorem liOriginalFunctional_liLocalLogTaylor_eq_shiftedClassical (n : ℕ) :
    liOriginalFunctional liLocalLogTaylor n = shiftedClassicalLiCoefficient n := by
  rw [liOriginalFunctional, shiftedClassicalLiCoefficient,
    coeff_one_add_pow_mul_liLocalLogTaylor]
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp

theorem liGeneratingCoefficient_eq_shiftedClassical (n : ℕ) :
    liGeneratingCoefficient n = shiftedClassicalLiCoefficient n := by
  calc
    liGeneratingCoefficient n =
        (n + 1 : ℂ) * liGeneratingLogFPowerSeries.coeff (n + 1) :=
      liGeneratingCoefficient_eq_succ_mul_fms_coeff n
    _ = (n + 1 : ℂ) *
        coeff (n + 1) (liLocalLogTaylor.subst liMobiusSeries) := by
      rw [liGeneratingLogFPowerSeries_coeff_eq_subst]
    _ = liGeneratingFunctional liLocalLogTaylor n := by
      rw [liGeneratingFunctional, PowerSeries.coeff_derivative]
      ring
    _ = liOriginalFunctional liLocalLogTaylor n :=
      liGeneratingFunctional_eq_liOriginalFunctional liLocalLogTaylor
        liLocalLogTaylor_constantCoeff n
    _ = shiftedClassicalLiCoefficient n :=
      liOriginalFunctional_liLocalLogTaylor_eq_shiftedClassical n

theorem liGeneratingCoefficient_eq_normalizedClassical (n : ℕ) :
    liGeneratingCoefficient n = normalizedClassicalLiCoefficient n :=
  (liGeneratingCoefficient_eq_shiftedClassical n).trans
    (normalizedClassicalLiCoefficient_eq_shifted n).symm

end RHGarden
