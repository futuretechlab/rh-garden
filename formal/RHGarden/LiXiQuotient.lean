import RHGarden.LiExpAffine
import Mathlib.Analysis.Meromorphic.NormalForm

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace RHGarden

set_option maxHeartbeats 200000

/-- The occurrence product vanishes at every xi zero. -/
theorem xiCanonicalProductOccurrences_eq_zero_of_riemannXi_eq_zero
    {s : ℂ} (hs : riemannXi s = 0) :
    xiCanonicalProductOccurrences s = 0 := by
  let ρ : XiZero := ⟨s, (mem_xiDivisor_support_iff s).mpr hs⟩
  have hm : 0 < xiMultiplicity s := by
    apply Nat.pos_of_ne_zero
    intro h
    have hcast := xiMultiplicity_cast s
    rw [h, Nat.cast_zero] at hcast
    exact (xiDivisor_ne_zero_iff s).mpr hs hcast.symm
  let a : XiZeroOccurrence := ⟨ρ, ⟨0, hm⟩⟩
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num [riemannXi_zero] at hs
  apply tprod_of_exists_eq_zero
  refine ⟨a, ?_⟩
  simp [xiOccurrencePrimaryFactor, XiZeroOccurrence.value, a, ρ,
    primaryFactorOne, div_self hs0]

theorem xiCanonicalProductOccurrences_eq_zero_iff (s : ℂ) :
    xiCanonicalProductOccurrences s = 0 ↔ riemannXi s = 0 := by
  constructor
  · contrapose!
    exact xiCanonicalProductOccurrences_ne_zero
  · exact xiCanonicalProductOccurrences_eq_zero_of_riemannXi_eq_zero

/-- An opaque wrapper around the dependent occurrence sigma, used to keep
infinite-product partition elaboration small in Lean 4.33.0-rc2. -/
structure XiProductOccurrence where
  occurrence : XiZeroOccurrence

namespace XiProductOccurrence

def zero (a : XiProductOccurrence) : XiZero := a.occurrence.zero

end XiProductOccurrence

def xiProductOccurrenceEquiv : XiProductOccurrence ≃ XiZeroOccurrence where
  toFun := XiProductOccurrence.occurrence
  invFun := XiProductOccurrence.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

def xiProductOccurrenceFactor (a : XiProductOccurrence) (s : ℂ) : ℂ :=
  xiOccurrencePrimaryFactor a.occurrence s

/-- The predicate selecting the occurrence fiber belonging to one fixed xi zero. -/
def xiOccurrencesAtSet (ρ : XiZero) : Set XiProductOccurrence :=
  {a | a.occurrence.value = (ρ : ℂ)}

/-- The finite occurrence fiber belonging to one fixed xi zero. -/
abbrev XiOccurrencesAt (ρ : XiZero) := xiOccurrencesAtSet ρ

/-- The complementary occurrence fiber away from one fixed xi zero. -/
abbrev XiOccurrencesAwayFrom (ρ : XiZero) :=
  {a : XiProductOccurrence // a ∈ (xiOccurrencesAtSet ρ)ᶜ}

/-- The fixed-zero occurrence fiber is exactly its finite multiplicity index. -/
def xiOccurrencesAtEquiv (ρ : XiZero) :
    XiOccurrencesAt ρ ≃ Fin (xiMultiplicity (ρ : ℂ)) where
  toFun a := by
    rcases a with ⟨⟨⟨ρ', j⟩⟩, h⟩
    have hz : ρ' = ρ := Subtype.ext h
    subst ρ'
    exact j
  invFun j := ⟨⟨⟨ρ, j⟩⟩, rfl⟩
  left_inv a := by
    rcases a with ⟨⟨⟨ρ', j⟩⟩, hρ⟩
    have hz : ρ' = ρ := Subtype.ext hρ
    subst ρ'
    rfl
  right_inv j := rfl

/-- The canonical product with the occurrence fiber at `ρ` omitted. -/
noncomputable def xiCanonicalProductAwayFrom (ρ : XiZero) (s : ℂ) : ℂ :=
  ∏' a : XiOccurrencesAwayFrom ρ, xiProductOccurrenceFactor a.1 s

private theorem tprod_equiv
    {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M]
    (e : ι ≃ κ) (f : κ → M) :
    (∏' i, f (e i)) = ∏' k, f k :=
  e.tprod_eq f

private theorem multipliable_equiv
    {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M]
    (e : ι ≃ κ) (f : κ → M) (hf : Multipliable f) :
    Multipliable (fun i => f (e i)) :=
  e.multipliable_iff.mpr hf

private theorem tprod_partition_of_subproducts
    {ι M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M] [ContinuousMul M]
    (S : Set ι) (f : ι → M)
    (hs : Multipliable (fun i : S => f i.1))
    (hsc : Multipliable (fun i : {j // j ∈ Sᶜ} => f i.1)) :
    (∏' i : S, f i.1) * (∏' i : {j // j ∈ Sᶜ}, f i.1) = ∏' i, f i :=
  Multipliable.tprod_mul_tprod_compl hs hsc

private theorem xiProductOccurrence_multipliable (s : ℂ) :
    Multipliable (fun a : XiProductOccurrence => xiProductOccurrenceFactor a s) :=
  multipliable_equiv xiProductOccurrenceEquiv
    (fun a : XiZeroOccurrence => xiOccurrencePrimaryFactor a s)
    (xiOccurrencePrimaryFactors_multipliableLocallyUniformly.multipliable
      (Set.mem_univ s))

private theorem xiProductOccurrence_tprod_eq (s : ℂ) :
    (∏' a : XiProductOccurrence, xiProductOccurrenceFactor a s) =
      xiCanonicalProductOccurrences s := by
  calc
    _ = ∏' a : XiZeroOccurrence, xiOccurrencePrimaryFactor a s :=
      tprod_equiv xiProductOccurrenceEquiv
        (fun a : XiZeroOccurrence => xiOccurrencePrimaryFactor a s)
    _ = xiCanonicalProductOccurrences s := rfl

private theorem xiOccurrencesAt_multipliable (ρ : XiZero) (s : ℂ) :
    Multipliable (fun a : XiOccurrencesAt ρ => xiProductOccurrenceFactor a.1 s) := by
  letI : Fintype (XiOccurrencesAt ρ) :=
    Fintype.ofEquiv (Fin (xiMultiplicity (ρ : ℂ))) (xiOccurrencesAtEquiv ρ).symm
  exact Multipliable.of_finite

private theorem xiOccurrencesAwayFrom_multipliable (ρ : XiZero) (s : ℂ) :
    Multipliable (fun a : XiOccurrencesAwayFrom ρ =>
      xiProductOccurrenceFactor a.1 s) := by
  have hinc : Function.Injective
      (fun a : XiOccurrencesAwayFrom ρ => a.1.occurrence) := by
    intro a b h
    apply Subtype.ext
    exact xiProductOccurrenceEquiv.injective h
  have hsumm : Summable (fun a : XiOccurrencesAwayFrom ρ =>
      xiOccurrencePrimaryDelta a.1.occurrence s) :=
    (xiOccurrencePrimaryDelta_summableLocallyUniformly.summable
      (Set.mem_univ s)).comp_injective hinc
  simpa [xiProductOccurrenceFactor, xiOccurrencePrimaryDelta, add_comm] using
    multipliable_one_add_of_summable hsumm.norm

private theorem xiProductOccurrence_partition (ρ : XiZero) (s : ℂ) :
    (∏' a : {x // x ∈ xiOccurrencesAtSet ρ}, xiProductOccurrenceFactor a.1 s) *
      (∏' a : {x // x ∈ (xiOccurrencesAtSet ρ)ᶜ},
        xiProductOccurrenceFactor a.1 s) =
        ∏' a : XiProductOccurrence, xiProductOccurrenceFactor a s :=
  tprod_partition_of_subproducts (xiOccurrencesAtSet ρ)
    (fun a : XiProductOccurrence => xiProductOccurrenceFactor a s)
    (xiOccurrencesAt_multipliable ρ s) (xiOccurrencesAwayFrom_multipliable ρ s)

theorem xiCanonicalProductOccurrences_split (ρ : XiZero) (s : ℂ) :
    (∏' a : {x // x ∈ xiOccurrencesAtSet ρ}, xiProductOccurrenceFactor a.1 s) *
      (∏' a : {x // x ∈ (xiOccurrencesAtSet ρ)ᶜ},
        xiProductOccurrenceFactor a.1 s) =
        xiCanonicalProductOccurrences s := by
  exact (xiProductOccurrence_partition ρ s).trans (xiProductOccurrence_tprod_eq s)

theorem xiOccurrencesAt_product (ρ : XiZero) (s : ℂ) :
    (∏' a : XiOccurrencesAt ρ, xiProductOccurrenceFactor a.1 s) =
      primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ) := by
  letI : Fintype (XiOccurrencesAt ρ) :=
    Fintype.ofEquiv (Fin (xiMultiplicity (ρ : ℂ))) (xiOccurrencesAtEquiv ρ).symm
  rw [tprod_fintype]
  calc
    (∏ a : XiOccurrencesAt ρ, xiProductOccurrenceFactor a.1 s) =
        ∏ _j : Fin (xiMultiplicity (ρ : ℂ)),
          primaryFactorOne (s / (ρ : ℂ)) := by
      apply Fintype.prod_equiv (xiOccurrencesAtEquiv ρ)
      intro a
      rcases a with ⟨⟨⟨ρ', j⟩⟩, hρ⟩
      have hz : ρ' = ρ := Subtype.ext hρ
      subst ρ'
      rfl
    _ = primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ) :=
      Fin.prod_const _ _

theorem xiCanonicalProductOccurrences_eq_primaryFactor_mul_away
    (ρ : XiZero) (s : ℂ) :
    xiCanonicalProductOccurrences s =
      primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ) *
        xiCanonicalProductAwayFrom ρ s := by
  rw [← xiCanonicalProductOccurrences_split ρ s, xiOccurrencesAt_product]
  rfl

private theorem xiAwayPrimaryFactors_multipliableLocallyUniformly (ρ : XiZero) :
    MultipliableLocallyUniformlyOn
      (fun a : XiOccurrencesAwayFrom ρ =>
        xiProductOccurrenceFactor a.1) Set.univ := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨u, hu, hbound⟩ := xiOccurrencePrimaryDelta_compact_majorant K hK
  let v : XiOccurrencesAwayFrom ρ → ℝ := fun a => u a.1.occurrence
  have hinc : Function.Injective (fun a : XiOccurrencesAwayFrom ρ => a.1.occurrence) := by
    intro a b h
    apply Subtype.ext
    exact xiProductOccurrenceEquiv.injective h
  have hv : Summable v := hu.comp_injective hinc
  have hbound' : ∀ᶠ a : XiOccurrencesAwayFrom ρ in cofinite,
      ∀ s ∈ K, ‖xiOccurrencePrimaryDelta a.1.occurrence s‖ ≤ v a := by
    exact hinc.tendsto_cofinite.eventually hbound
  have hprod := Summable.hasProdUniformlyOn_one_add hK hv hbound'
    (fun a => ((differentiable_xiOccurrencePrimaryFactor a.1.occurrence).continuous.sub
      continuous_const).continuousOn)
  change HasProdUniformlyOn
    (fun a : XiOccurrencesAwayFrom ρ =>
      xiOccurrencePrimaryFactor a.1.occurrence)
    (fun s => ∏' a : XiOccurrencesAwayFrom ρ,
      xiOccurrencePrimaryFactor a.1.occurrence s) K
  simpa [xiOccurrencePrimaryDelta, v] using hprod

theorem differentiable_xiCanonicalProductAwayFrom (ρ : XiZero) :
    Differentiable ℂ (xiCanonicalProductAwayFrom ρ) := by
  unfold xiCanonicalProductAwayFrom
  change Differentiable ℂ (fun s : ℂ =>
    ∏' a : XiOccurrencesAwayFrom ρ,
      xiProductOccurrenceFactor a.1 s)
  have hd := (xiAwayPrimaryFactors_multipliableLocallyUniformly ρ)
    |>.hasProdLocallyUniformlyOn.differentiableOn
      (.of_forall <| by
        intro u
        simp only [xiProductOccurrenceFactor, xiOccurrencePrimaryFactor, primaryFactorOne]
        fun_prop)
      isOpen_univ
  exact fun s => (hd s (Set.mem_univ s)).differentiableAt Filter.univ_mem

theorem xiCanonicalProductAwayFrom_ne_zero (ρ : XiZero) :
    xiCanonicalProductAwayFrom ρ (ρ : ℂ) ≠ 0 := by
  have hsumm := xiOccurrencePrimaryDelta_summableLocallyUniformly.summable
    (x := (ρ : ℂ)) (Set.mem_univ _)
  have hsumm' : Summable (fun a : XiOccurrencesAwayFrom ρ =>
      xiOccurrencePrimaryDelta a.1.occurrence (ρ : ℂ)) := by
    apply hsumm.comp_injective
    intro a b h
    apply Subtype.ext
    exact xiProductOccurrenceEquiv.injective h
  have hne := tprod_one_add_ne_zero_of_summable
    (f := fun a : XiOccurrencesAwayFrom ρ =>
      xiOccurrencePrimaryDelta a.1.occurrence (ρ : ℂ))
    (fun a => by
      simpa [xiOccurrencePrimaryDelta] using
        xiOccurrencePrimaryFactor_ne_zero (a := a.1.occurrence) (by
          intro h
          apply a.2
          exact h.symm))
    hsumm'.norm
  simpa [xiCanonicalProductAwayFrom, xiProductOccurrenceFactor,
    xiOccurrencePrimaryDelta] using hne

theorem analyticOrderAt_primaryFactorOne_div_self (ρ : XiZero) :
    analyticOrderAt (fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) (ρ : ℂ) = 1 := by
  let u : ℂ → ℂ := fun s => -(1 / (ρ : ℂ)) * Complex.exp (s / (ρ : ℂ))
  have hu : AnalyticAt ℂ u (ρ : ℂ) := by
    dsimp [u]
    fun_prop
  have hu0 : u (ρ : ℂ) ≠ 0 := by
    dsimp [u]
    exact mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero ρ.ne_zero)) (Complex.exp_ne_zero _)
  have hfun : (fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) =
      (fun s => s - (ρ : ℂ)) * u := by
    funext s
    dsimp [u, primaryFactorOne]
    field_simp [ρ.ne_zero]
    ring
  have hcenter : analyticOrderAt (fun s : ℂ => s - (ρ : ℂ)) (ρ : ℂ) = 1 := by
    convert (analyticOrderAt_centeredMonomial
      (𝕜 := ℂ) (z₀ := (ρ : ℂ)) (n := 1)) using 1 <;> simp
  rw [hfun, analyticOrderAt_mul (by fun_prop) hu, hcenter,
    hu.analyticOrderAt_eq_zero.mpr hu0]
  simp

theorem analyticOrderNatAt_primaryFactorMultiplicity (ρ : XiZero) :
    analyticOrderNatAt
      (fun s : ℂ => primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ))
      (ρ : ℂ) = xiMultiplicity (ρ : ℂ) := by
  change analyticOrderNatAt
      ((fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) ^ xiMultiplicity (ρ : ℂ))
      (ρ : ℂ) = _
  rw [analyticOrderNatAt_pow
    ((differentiable_primaryFactorOne_div (ρ : ℂ)).analyticAt _),
    show analyticOrderNatAt (fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) (ρ : ℂ) = 1 by
      simp [analyticOrderNatAt, analyticOrderAt_primaryFactorOne_div_self]]
  simp

theorem analyticAt_primaryFactorOne_div (ρ : XiZero) (s : ℂ) :
    AnalyticAt ℂ (fun z => primaryFactorOne (z / (ρ : ℂ))) s :=
  (differentiable_primaryFactorOne_div (ρ : ℂ)).analyticAt s

theorem analyticOrderNatAt_xiCanonicalProductOccurrences_at_zero (ρ : XiZero) :
    analyticOrderNatAt xiCanonicalProductOccurrences (ρ : ℂ) =
      xiMultiplicity (ρ : ℂ) := by
  have hfun : xiCanonicalProductOccurrences =
      (fun s : ℂ => primaryFactorOne (s / (ρ : ℂ)) ^ xiMultiplicity (ρ : ℂ)) *
        xiCanonicalProductAwayFrom ρ := by
    funext s
    exact xiCanonicalProductOccurrences_eq_primaryFactor_mul_away ρ s
  rw [hfun]
  change analyticOrderNatAt
      ((fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) ^ xiMultiplicity (ρ : ℂ) *
        xiCanonicalProductAwayFrom ρ) (ρ : ℂ) = _
  rw [analyticOrderNatAt_mul
    ((analyticAt_primaryFactorOne_div ρ _).pow _)
    ((differentiable_xiCanonicalProductAwayFrom ρ).analyticAt _)
    (by
      rw [analyticOrderAt_pow (analyticAt_primaryFactorOne_div ρ _)]
      simp [analyticOrderAt_primaryFactorOne_div_self])
    (by
      exact ne_of_eq_of_ne
        (((differentiable_xiCanonicalProductAwayFrom ρ).analyticAt _).analyticOrderAt_eq_zero.mpr
          (xiCanonicalProductAwayFrom_ne_zero ρ))
        ENat.zero_ne_top),
    show analyticOrderNatAt
        ((fun s : ℂ => primaryFactorOne (s / (ρ : ℂ))) ^ xiMultiplicity (ρ : ℂ))
        (ρ : ℂ) = xiMultiplicity (ρ : ℂ) by
      exact analyticOrderNatAt_primaryFactorMultiplicity ρ]
  rw [show analyticOrderNatAt (xiCanonicalProductAwayFrom ρ) (ρ : ℂ) = 0 by
    simp [analyticOrderNatAt,
      ((differentiable_xiCanonicalProductAwayFrom ρ).analyticAt _).analyticOrderAt_eq_zero,
      xiCanonicalProductAwayFrom_ne_zero]]
  simp

theorem analyticOrderNatAt_xiCanonicalProductOccurrences (s : ℂ) :
    analyticOrderNatAt xiCanonicalProductOccurrences s = xiMultiplicity s := by
  by_cases hs : riemannXi s = 0
  · let ρ : XiZero := ⟨s, (mem_xiDivisor_support_iff s).mpr hs⟩
    exact analyticOrderNatAt_xiCanonicalProductOccurrences_at_zero ρ
  · have hcp : xiCanonicalProductOccurrences s ≠ 0 :=
      xiCanonicalProductOccurrences_ne_zero hs
    have hcpOrder : analyticOrderNatAt xiCanonicalProductOccurrences s = 0 := by
      simp [analyticOrderNatAt,
        (differentiable_xiCanonicalProductOccurrences.analyticAt s).analyticOrderAt_eq_zero,
        hcp]
    have hxiOrder : analyticOrderNatAt riemannXi s = 0 := by
      simp [analyticOrderNatAt, (analyticAt_riemannXi s).analyticOrderAt_eq_zero, hs]
    rw [hcpOrder, xiMultiplicity_eq_analyticOrderNatAt, hxiOrder]

theorem analyticOrderAt_xiCanonicalProductOccurrences_ne_top (s : ℂ) :
    analyticOrderAt xiCanonicalProductOccurrences s ≠ ⊤ := by
  intro htop
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z => differentiable_xiCanonicalProductOccurrences.analyticAt z)).mp htop
  have := congrFun hzero 0
  simpa [xiCanonicalProductOccurrences_zero] using this

theorem analyticOrderAt_xiCanonicalProduct_eq_riemannXi (s : ℂ) :
    analyticOrderAt xiCanonicalProductOccurrences s = analyticOrderAt riemannXi s := by
  rw [← Nat.cast_analyticOrderNatAt
      (analyticOrderAt_xiCanonicalProductOccurrences_ne_top s),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top s)]
  congr 1
  rw [analyticOrderNatAt_xiCanonicalProductOccurrences,
    xiMultiplicity_eq_analyticOrderNatAt]

/-- The totalized pointwise quotient, before repairing its common-zero values. -/
def xiRawQuotient (s : ℂ) : ℂ :=
  riemannXi s / xiCanonicalProductOccurrences s

theorem meromorphicOn_xiRawQuotient : MeromorphicOn xiRawQuotient Set.univ := by
  intro s _
  exact (analyticAt_riemannXi s).meromorphicAt.div
    (differentiable_xiCanonicalProductOccurrences.analyticAt s).meromorphicAt

theorem meromorphicOrderAt_xiRawQuotient (s : ℂ) :
    meromorphicOrderAt xiRawQuotient s = 0 := by
  unfold xiRawQuotient
  change meromorphicOrderAt (riemannXi / xiCanonicalProductOccurrences) s = 0
  rw [meromorphicOrderAt_div
    (analyticAt_riemannXi s).meromorphicAt
    (differentiable_xiCanonicalProductOccurrences.analyticAt s).meromorphicAt,
    (analyticAt_riemannXi s).meromorphicOrderAt_eq,
    (differentiable_xiCanonicalProductOccurrences.analyticAt s).meromorphicOrderAt_eq,
    analyticOrderAt_xiCanonicalProduct_eq_riemannXi]
  simp [analyticOrderAt_riemannXi_ne_top s]

/-- The canonical normal-form extension of the xi/canonical-product quotient. -/
noncomputable def xiZeroFreeQuotient : ℂ → ℂ :=
  toMeromorphicNFOn xiRawQuotient Set.univ

theorem analyticOnNhd_xiZeroFreeQuotient :
    AnalyticOnNhd ℂ xiZeroFreeQuotient Set.univ := by
  have hnf := meromorphicNFOn_toMeromorphicNFOn xiRawQuotient Set.univ
  change AnalyticOnNhd ℂ (toMeromorphicNFOn xiRawQuotient Set.univ) Set.univ
  rw [← hnf.divisor_nonneg_iff_analyticOnNhd]
  intro s
  rw [hnf.meromorphicOn.divisor_apply (Set.mem_univ s)]
  rw [meromorphicOrderAt_toMeromorphicNFOn meromorphicOn_xiRawQuotient
    (Set.mem_univ s), meromorphicOrderAt_xiRawQuotient]
  exact le_rfl

theorem differentiable_xiZeroFreeQuotient :
    Differentiable ℂ xiZeroFreeQuotient := fun s =>
  (analyticOnNhd_xiZeroFreeQuotient s (Set.mem_univ s)).differentiableAt

theorem xiZeroFreeQuotient_ne_zero (s : ℂ) : xiZeroFreeQuotient s ≠ 0 := by
  rw [xiZeroFreeQuotient,
    toMeromorphicNFOn_eq_toMeromorphicNFAt meromorphicOn_xiRawQuotient (Set.mem_univ s)]
  exact (meromorphicOn_xiRawQuotient s (Set.mem_univ s)
    |>.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).mp
      (meromorphicOrderAt_xiRawQuotient s)

theorem xiZeroFreeQuotient_eq_div {s : ℂ} (hs : riemannXi s ≠ 0) :
    xiZeroFreeQuotient s = riemannXi s / xiCanonicalProductOccurrences s := by
  have hcp := xiCanonicalProductOccurrences_ne_zero hs
  have hraw : AnalyticAt ℂ xiRawQuotient s :=
    (analyticAt_riemannXi s).div
      (differentiable_xiCanonicalProductOccurrences.analyticAt s) hcp
  rw [xiZeroFreeQuotient,
    toMeromorphicNFOn_eq_toMeromorphicNFAt meromorphicOn_xiRawQuotient (Set.mem_univ s),
    toMeromorphicNFAt_eq_self.mpr hraw.meromorphicNFAt]
  rfl

theorem riemannXi_eq_zeroFreeQuotient_mul_canonicalProduct (s : ℂ) :
    riemannXi s = xiZeroFreeQuotient s * xiCanonicalProductOccurrences s := by
  by_cases hs : riemannXi s = 0
  · rw [hs, xiCanonicalProductOccurrences_eq_zero_of_riemannXi_eq_zero hs, mul_zero]
  · rw [xiZeroFreeQuotient_eq_div hs, div_mul_cancel₀ _
      (xiCanonicalProductOccurrences_ne_zero hs)]

theorem xiZeroFreeQuotient_divisor_zero :
    MeromorphicOn.divisor xiZeroFreeQuotient Set.univ = 0 := by
  change MeromorphicOn.divisor (toMeromorphicNFOn xiRawQuotient Set.univ) Set.univ = 0
  rw [meromorphicOn_xiRawQuotient.divisor_of_toMeromorphicNFOn]
  ext s
  rw [meromorphicOn_xiRawQuotient.divisor_apply (Set.mem_univ s)]
  simp [meromorphicOrderAt_xiRawQuotient]

/-- The sole remaining xi-specific growth gate for the affine factorization. -/
def XiQuotientSubquadraticGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖xiZeroFreeQuotient z‖ ≤
        Real.exp (C * (1 + ‖z‖) ^ (xiGrowthOrder + ε))

theorem riemannXi_eq_exp_affine_mul_canonicalProduct_of_quotient_growth
    (hgrowth : XiQuotientSubquadraticGrowth) :
    ∃ A B : ℂ, ∀ s : ℂ,
      riemannXi s = Complex.exp (A + B * s) * xiCanonicalProductOccurrences s := by
  obtain ⟨A, B, hAB⟩ := subquadratic_zeroFree_entire_is_exp_affine
    differentiable_xiZeroFreeQuotient xiZeroFreeQuotient_ne_zero hgrowth
  exact ⟨A, B, fun s => by
    rw [riemannXi_eq_zeroFreeQuotient_mul_canonicalProduct, hAB]⟩

end RHGarden
