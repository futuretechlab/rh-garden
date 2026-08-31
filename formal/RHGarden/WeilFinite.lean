import RHGarden.LiNormalization

noncomputable section

open scoped ComplexConjugate

namespace RHGarden

/-- Lagarias's integer-indexed Li test function, equation (3.2). Division and
integer powers are totalized by Lean; identities across its poles state their
exclusions explicitly. -/
def weilLiTest (n : ℤ) (s : ℂ) : ℂ := 1 - (1 - 1 / s) ^ n

@[simp] theorem weilLiTest_zero_index (s : ℂ) : weilLiTest 0 s = 0 := by
  simp [weilLiTest]

@[simp] theorem weilLiTest_one_index (s : ℂ) : weilLiTest 1 s = 1 / s := by
  simp [weilLiTest]

private theorem weilLiBase_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    1 - 1 / (1 - s) = (1 - 1 / s)⁻¹ := by
  field_simp
  ring

/-- Lagarias (3.5), pointwise away from the two poles. -/
theorem weilLiTest_neg (m : ℤ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    weilLiTest (-m) s = weilLiTest m (1 - s) := by
  rw [weilLiTest, weilLiTest, weilLiBase_one_sub hs0 hs1]
  simp [zpow_neg]

/-- Lagarias (3.6), the finite algebraic product identity. -/
theorem weilLiTest_mul_neg (n m : ℤ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    weilLiTest n s * weilLiTest (-m) s =
      weilLiTest n s + weilLiTest (-m) s - weilLiTest (n - m) s := by
  have hb : 1 - 1 / s ≠ 0 := by
    rw [show 1 - 1 / s = (s - 1) / s by field_simp]
    exact div_ne_zero (sub_ne_zero.mpr hs1) hs0
  rw [weilLiTest, weilLiTest, weilLiTest, zpow_sub₀ hb, zpow_neg]
  ring

/-- Reflection appearing in the Weil scalar product. -/
def weilReflect (s : ℂ) : ℂ := 1 - starRingEnd ℂ s

theorem conj_weilLiTest_weilReflect (m : ℤ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    starRingEnd ℂ (weilLiTest m (weilReflect s)) = weilLiTest (-m) s := by
  rw [weilLiTest_neg m hs0 hs1]
  simp [weilLiTest, weilReflect, map_zpow₀]

/-- A finite zero sum retaining multiplicity. It is deliberately not the
conditionally star-convergent infinite Li coefficient. -/
def finiteLiZeroValue (Z : Multiset ℂ) (n : ℤ) : ℂ :=
  (Z.map (weilLiTest n)).sum

/-- Every member of a finite cutoff avoids the poles of the Li tests. -/
def ValidWeilZeroCutoff (Z : Multiset ℂ) : Prop :=
  ∀ s ∈ Z, s ≠ 0 ∧ s ≠ 1

/-- The finite version of Lagarias's equation (3.1), defined independently of
all Li coefficients and convergence claims. -/
def finiteWeilScalar (Z : Multiset ℂ) (F G : ℂ → ℂ) : ℂ :=
  (Z.map fun ρ ↦ F ρ * starRingEnd ℂ (G (weilReflect ρ))).sum

/-- Finite exact skeleton of Lagarias (3.3). -/
theorem finiteWeilScalar_liTest (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (n m : ℤ) :
    finiteWeilScalar Z (weilLiTest n) (weilLiTest m) =
      finiteLiZeroValue Z n + finiteLiZeroValue Z (-m) -
        finiteLiZeroValue Z (n - m) := by
  induction Z using Multiset.induction_on with
  | empty => simp [finiteWeilScalar, finiteLiZeroValue]
  | @cons s Z ih =>
      have hs := hZ s (by simp)
      have hZ' : ValidWeilZeroCutoff Z := fun z hz ↦ hZ z (by simp [hz])
      simp only [finiteWeilScalar, finiteLiZeroValue, Multiset.map_cons,
        Multiset.sum_cons]
      rw [conj_weilLiTest_weilReflect m hs.1 hs.2,
        weilLiTest_mul_neg n m hs.1 hs.2]
      have hi := ih hZ'
      simp only [finiteWeilScalar, finiteLiZeroValue] at hi
      rw [hi]
      ring

/-- The finite diagonal form, before imposing any symmetry on the cutoff. -/
theorem finiteWeilScalar_liTest_self (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (n : ℤ) :
    finiteWeilScalar Z (weilLiTest n) (weilLiTest n) =
      finiteLiZeroValue Z n + finiteLiZeroValue Z (-n) := by
  rw [finiteWeilScalar_liTest Z hZ n n]
  simp [finiteLiZeroValue]

/-- A finite cutoff is stable under Weil reflection, with multiplicity. -/
def WeilReflectionStable (Z : Multiset ℂ) : Prop := Z.map weilReflect = Z

theorem finiteLiZeroValue_neg_eq_conj (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (hstable : WeilReflectionStable Z) (n : ℤ) :
    finiteLiZeroValue Z (-n) = starRingEnd ℂ (finiteLiZeroValue Z n) := by
  have hpoint : Z.map (weilLiTest (-n)) =
      Z.map (fun s ↦ starRingEnd ℂ (weilLiTest n (weilReflect s))) := by
    apply Multiset.map_congr rfl
    intro s hs
    have hp := hZ s hs
    exact (conj_weilLiTest_weilReflect n hp.1 hp.2).symm
  have hstar (W : Multiset ℂ) :
      (W.map (fun t ↦ starRingEnd ℂ (weilLiTest n t))).sum =
        starRingEnd ℂ ((W.map (weilLiTest n)).sum) := by
    induction W using Multiset.induction_on with
    | empty => simp
    | cons s W ih => simp [ih, map_add]
  rw [finiteLiZeroValue, hpoint]
  calc
    _ = ((Z.map weilReflect).map
          (fun t ↦ starRingEnd ℂ (weilLiTest n t))).sum := by
        rw [Multiset.map_map]
        simp
    _ = (Z.map (fun t ↦ starRingEnd ℂ (weilLiTest n t))).sum := by
        rw [hstable]
    _ = starRingEnd ℂ (finiteLiZeroValue Z n) := by
        simpa only [finiteLiZeroValue] using hstar Z

theorem finiteWeilScalar_liTest_self_eq_two_re (Z : Multiset ℂ)
    (hZ : ValidWeilZeroCutoff Z) (hstable : WeilReflectionStable Z) (n : ℤ) :
    finiteWeilScalar Z (weilLiTest n) (weilLiTest n) =
      (2 * (finiteLiZeroValue Z n).re : ℂ) := by
  rw [finiteWeilScalar_liTest_self Z hZ n,
    finiteLiZeroValue_neg_eq_conj Z hZ hstable n]
  apply Complex.ext
  · simp; ring
  · simp

end RHGarden
