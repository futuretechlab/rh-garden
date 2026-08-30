import RHGarden.CriticalLine
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

namespace RHGarden

open PowerSeries

/-- The formal series `z / (1-z) = z + z² + ⋯`. -/
def liMobiusSeries : PowerSeries ℂ :=
  X * mk 1

@[simp] theorem liMobiusSeries_constantCoeff :
    constantCoeff liMobiusSeries = 0 := by
  simp [liMobiusSeries]

theorem liMobiusSeries_coeff_zero : coeff 0 liMobiusSeries = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, liMobiusSeries_constantCoeff]

@[simp] theorem liMobiusSeries_coeff_succ (n : ℕ) :
    coeff (n + 1) liMobiusSeries = 1 := by
  simp [liMobiusSeries]

theorem liMobiusSeries_coeff (n : ℕ) :
    coeff n liMobiusSeries = if n = 0 then 0 else 1 := by
  cases n with
  | zero => simp [liMobiusSeries_coeff_zero]
  | succ n => simp

theorem one_add_liMobiusSeries :
    1 + liMobiusSeries = (mk 1 : PowerSeries ℂ) := by
  ext (_ | n) <;> simp [liMobiusSeries]

theorem geometricSeries_eq_inv_one_sub_X :
    (mk 1 : PowerSeries ℂ) = (1 - X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · exact PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  · simp

theorem one_add_liMobiusSeries_eq_inv_one_sub_X :
    1 + liMobiusSeries = (1 - X : PowerSeries ℂ)⁻¹ :=
  one_add_liMobiusSeries.trans geometricSeries_eq_inv_one_sub_X

theorem liMobiusSeries_hasSubst : PowerSeries.HasSubst liMobiusSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero' liMobiusSeries_constantCoeff

/-- The normalized entire function whose Taylor data at zero is the Taylor data
of `2 * xi` at `s = 1`. -/
def normalizedXiAtOne (u : ℂ) : ℂ :=
  2 * riemannXi (1 + u)

theorem differentiable_normalizedXiAtOne :
    Differentiable ℂ normalizedXiAtOne := by
  unfold normalizedXiAtOne
  have hinner : Differentiable ℂ (fun u : ℂ ↦ 1 + u) := by fun_prop
  have hcomp : Differentiable ℂ (fun u : ℂ ↦ riemannXi (1 + u)) := by
    change Differentiable ℂ (riemannXi ∘ fun u : ℂ ↦ 1 + u)
    exact differentiable_riemannXi.comp hinner
  exact (differentiable_const (c := (2 : ℂ))).mul hcomp

theorem analyticAt_normalizedXiAtOne :
    AnalyticAt ℂ normalizedXiAtOne 0 :=
  differentiable_normalizedXiAtOne.analyticAt 0

/-- Formal Taylor coefficient data of `u ↦ 2 * xi(1+u)`.  This definition
does not assert convergence or equality of a power-series evaluation with xi. -/
def normalizedXiTaylor : PowerSeries ℂ :=
  mk fun n ↦ iteratedDeriv n normalizedXiAtOne 0 / (n.factorial : ℂ)

/-- The analytic formal-multilinear-series certificate for the same scalar
Taylor coefficients stored algebraically in `normalizedXiTaylor`. -/
def normalizedXiFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n ↦
    iteratedDeriv n normalizedXiAtOne 0 / (n.factorial : ℂ)

theorem normalizedXiAtOne_hasFPowerSeriesAt :
    HasFPowerSeriesAt normalizedXiAtOne normalizedXiFPowerSeries 0 := by
  exact analyticAt_normalizedXiAtOne.hasFPowerSeriesAt

theorem normalizedXiFPowerSeries_coeff (n : ℕ) :
    normalizedXiFPowerSeries.coeff n = coeff n normalizedXiTaylor := by
  simp [normalizedXiFPowerSeries, normalizedXiTaylor]

/-- Locally at zero, the algebraic coefficients in `normalizedXiTaylor`
actually sum to the normalized xi function.  No global radius is asserted. -/
theorem normalizedXiTaylor_hasSum :
    ∀ᶠ z : ℂ in nhds 0,
      HasSum (fun n ↦ coeff n normalizedXiTaylor * z ^ n)
        (normalizedXiAtOne z) := by
  have h := hasFPowerSeriesAt_iff.mp normalizedXiAtOne_hasFPowerSeriesAt
  filter_upwards [h] with z hz
  simpa [normalizedXiFPowerSeries_coeff, mul_comm] using hz

/-- The analytic Mobius coordinate used by the Li generating function. -/
def analyticLiMobius (z : ℂ) : ℂ := z / (1 - z)

/-- The explicit analytic FMS for `z / (1-z)`, with coefficients
`0, 1, 1, ...`. -/
def liMobiusFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n ↦ if n = 0 then 0 else 1

@[simp] theorem liMobiusFPowerSeries_coeff_zero :
    liMobiusFPowerSeries.coeff 0 = 0 := by
  simp [liMobiusFPowerSeries]

@[simp] theorem liMobiusFPowerSeries_coeff_succ (n : ℕ) :
    liMobiusFPowerSeries.coeff (n + 1) = 1 := by
  simp [liMobiusFPowerSeries]

theorem liMobiusFPowerSeries_coeff_eq_powerSeries (n : ℕ) :
    liMobiusFPowerSeries.coeff n = coeff n liMobiusSeries := by
  simp [liMobiusFPowerSeries, liMobiusSeries_coeff]

theorem liMobius_hasFPowerSeriesAt :
    HasFPowerSeriesAt analyticLiMobius liMobiusFPowerSeries 0 := by
  have hgeom : HasFPowerSeriesAt (fun z : ℂ ↦ 1 / (1 - z))
      (FormalMultilinearSeries.ofScalars ℂ fun _ : ℕ ↦ (1 : ℂ)) 0 :=
    Complex.one_div_one_sub_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
  have hconst : HasFPowerSeriesAt (fun _ : ℂ ↦ (1 : ℂ))
      (constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) 0 :=
    hasFPowerSeriesAt_const
  have hsub := hgeom.sub hconst
  have hseries :
      (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ ↦ (1 : ℂ)) -
        constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) = liMobiusFPowerSeries := by
    ext n
    cases n with
    | zero =>
        simp [liMobiusFPowerSeries]
    | succ n =>
        simp [liMobiusFPowerSeries]
  rw [hseries] at hsub
  apply hsub.congr
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with z hz
  simp only [Pi.sub_apply]
  rw [show 1 / (1 - z) - 1 = analyticLiMobius z by
    unfold analyticLiMobius
    field_simp
    ring]

theorem analyticAt_liMobius : AnalyticAt ℂ analyticLiMobius 0 := by
  unfold analyticLiMobius
  exact analyticAt_id.div (analyticAt_const.sub analyticAt_id) (by norm_num)

/-- The actual analytic composite, deliberately kept distinct from the
algebraic `PowerSeries.subst` object `liXiSeries`. -/
def analyticLiXi (z : ℂ) : ℂ := normalizedXiAtOne (analyticLiMobius z)

theorem analyticAt_analyticLiXi : AnalyticAt ℂ analyticLiXi 0 := by
  unfold analyticLiXi
  have houter : AnalyticAt ℂ normalizedXiAtOne (analyticLiMobius 0) := by
    simpa [analyticLiMobius] using analyticAt_normalizedXiAtOne
  change AnalyticAt ℂ (normalizedXiAtOne ∘ analyticLiMobius) 0
  exact houter.comp analyticAt_liMobius

/-- Authoritative analytic composition of the normalized-xi germ with the
explicit Mobius germ. -/
def liXiFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  normalizedXiFPowerSeries.comp liMobiusFPowerSeries

theorem analyticLiXi_hasFPowerSeriesAt_comp :
    HasFPowerSeriesAt analyticLiXi liXiFPowerSeries 0 := by
  have houter : HasFPowerSeriesAt normalizedXiAtOne normalizedXiFPowerSeries
      (analyticLiMobius 0) := by
    simpa [analyticLiMobius] using normalizedXiAtOne_hasFPowerSeriesAt
  have hcomp := houter.comp liMobius_hasFPowerSeriesAt
  change HasFPowerSeriesAt (normalizedXiAtOne ∘ analyticLiMobius)
    liXiFPowerSeries 0
  exact hcomp

def analyticLiXiTaylorFMS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n ↦
    iteratedDeriv n analyticLiXi 0 / (n.factorial : ℂ)

theorem analyticLiXiFMS_eq_derivativeTaylor :
    liXiFPowerSeries = analyticLiXiTaylorFMS := by
  apply analyticLiXi_hasFPowerSeriesAt_comp.eq_formalMultilinearSeries
  exact analyticAt_analyticLiXi.hasFPowerSeriesAt

/-- Coefficient adapter from the analytically certified FMS into the algebraic
`PowerSeries` layer. -/
def analyticLiXiPowerSeries : PowerSeries ℂ :=
  mk fun n ↦ liXiFPowerSeries.coeff n

@[simp] theorem analyticLiXiPowerSeries_coeff (n : ℕ) :
    coeff n analyticLiXiPowerSeries = liXiFPowerSeries.coeff n := by
  simp [analyticLiXiPowerSeries]

@[simp] theorem analyticLiXiPowerSeries_constantCoeff :
    constantCoeff analyticLiXiPowerSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, analyticLiXiPowerSeries_coeff,
    analyticLiXiFMS_eq_derivativeTaylor]
  simp [analyticLiXiTaylorFMS, analyticLiXi, analyticLiMobius,
    normalizedXiAtOne, iteratedDeriv_zero, riemannXi_one]

theorem analyticLiXiPowerSeries_isUnit : IsUnit analyticLiXiPowerSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    analyticLiXiPowerSeries_constantCoeff]
  exact isUnit_one

theorem analyticLiXiPowerSeries_mul_inv :
    analyticLiXiPowerSeries * analyticLiXiPowerSeries⁻¹ = 1 := by
  exact PowerSeries.mul_inv_cancel analyticLiXiPowerSeries (by simp)

/-- The authoritative coefficient series backed by the local analytic FMS
certificate. -/
def certifiedLiXiSeries : PowerSeries ℂ := analyticLiXiPowerSeries

def certifiedLiFormalLogDerivative : PowerSeries ℂ :=
  PowerSeries.derivative ℂ certifiedLiXiSeries * certifiedLiXiSeries⁻¹

def certifiedLiFormalCoefficient (n : ℕ) : ℂ :=
  coeff n certifiedLiFormalLogDerivative

theorem certifiedLiXiSeries_hasSum :
    ∀ᶠ z : ℂ in nhds 0,
      HasSum (fun n ↦ coeff n certifiedLiXiSeries * z ^ n)
        (analyticLiXi z) := by
  have h := hasFPowerSeriesAt_iff.mp analyticLiXi_hasFPowerSeriesAt_comp
  filter_upwards [h] with z hz
  simpa [certifiedLiXiSeries, mul_comm] using hz

@[simp] theorem normalizedXiTaylor_constantCoeff :
    constantCoeff normalizedXiTaylor = 1 := by
  simp [normalizedXiTaylor, normalizedXiAtOne, iteratedDeriv_zero, riemannXi_one]

/-- Formal substitution of the Mobius series into the xi Taylor data. -/
def liXiSeries : PowerSeries ℂ :=
  normalizedXiTaylor.subst liMobiusSeries

@[simp] theorem liXiSeries_constantCoeff :
    constantCoeff liXiSeries = 1 := by
  have htail : constantCoeff (normalizedXiTaylor - 1) = 0 := by simp
  have hzero := PowerSeries.constantCoeff_subst_eq_zero
    liMobiusSeries_constantCoeff (normalizedXiTaylor - 1) htail
  have hsplit : normalizedXiTaylor = 1 + (normalizedXiTaylor - 1) := by ring
  rw [liXiSeries, hsplit,
    PowerSeries.subst_add liMobiusSeries_hasSubst]
  change MvPowerSeries.constantCoeff
    ((1 : PowerSeries ℂ).subst liMobiusSeries +
      (normalizedXiTaylor - 1).subst liMobiusSeries) = 1
  rw [map_add, hzero]
  change MvPowerSeries.constantCoeff ((C (1 : ℂ)).subst liMobiusSeries) + 0 = 1
  rw [PowerSeries.subst_C]
  simp

theorem liXiSeries_isUnit : IsUnit liXiSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, liXiSeries_constantCoeff]
  exact isUnit_one

theorem liXiSeries_mul_inv : liXiSeries * liXiSeries⁻¹ = 1 := by
  exact PowerSeries.mul_inv_cancel liXiSeries (by simp)

/-- Purely formal logarithmic derivative; no complex logarithm is used. -/
def liFormalLogDerivative : PowerSeries ℂ :=
  PowerSeries.derivative ℂ liXiSeries * liXiSeries⁻¹

/-- Zero-based indexing: `liFormalCoefficient n` is intended to correspond to
classical `λ_(n+1)` only after an independent analytic identification theorem. -/
def liFormalCoefficient (n : ℕ) : ℂ :=
  coeff n liFormalLogDerivative

section CubicCheck

variable (a₁ a₂ a₃ : ℂ)

/-- A generic cubic Taylor jet `1 + a₁X + a₂X² + a₃X³`. -/
def cubicXiTaylor : PowerSeries ℂ :=
  1 + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3

def cubicXiAfterFormalMobius : PowerSeries ℂ :=
  (cubicXiTaylor a₁ a₂ a₃).subst liMobiusSeries

def cubicLiFormalLogDerivative : PowerSeries ℂ :=
  PowerSeries.derivative ℂ (cubicXiAfterFormalMobius a₁ a₂ a₃) *
    (cubicXiAfterFormalMobius a₁ a₂ a₃)⁻¹

theorem cubicXiAfterFormalMobius_eq :
    cubicXiAfterFormalMobius a₁ a₂ a₃ =
      1 + C a₁ * liMobiusSeries + C a₂ * liMobiusSeries ^ 2 +
        C a₃ * liMobiusSeries ^ 3 := by
  have hone : (1 : PowerSeries ℂ).subst liMobiusSeries = 1 := by
    change (C (1 : ℂ)).subst liMobiusSeries = 1
    simpa [PowerSeries.C_apply] using PowerSeries.subst_C (a := liMobiusSeries) (1 : ℂ)
  have hC (a : ℂ) : (C a : PowerSeries ℂ).subst liMobiusSeries = C a := by
    rw [PowerSeries.subst_C]
    rfl
  simp [cubicXiAfterFormalMobius, cubicXiTaylor, hone, hC,
    PowerSeries.subst_add liMobiusSeries_hasSubst,
    PowerSeries.subst_mul liMobiusSeries_hasSubst,
    PowerSeries.subst_pow liMobiusSeries_hasSubst,
    PowerSeries.subst_X liMobiusSeries_hasSubst]

@[simp] theorem cubicXiAfterFormalMobius_coeff_zero :
    coeff 0 (cubicXiAfterFormalMobius a₁ a₂ a₃) = 1 := by
  rw [cubicXiAfterFormalMobius_eq]
  simp

@[simp] theorem cubicXiAfterFormalMobius_coeff_one :
    coeff 1 (cubicXiAfterFormalMobius a₁ a₂ a₃) = a₁ := by
  rw [cubicXiAfterFormalMobius_eq]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, liMobiusSeries_coeff,
    pow_succ]

@[simp] theorem cubicXiAfterFormalMobius_coeff_two :
    coeff 2 (cubicXiAfterFormalMobius a₁ a₂ a₃) = a₁ + a₂ := by
  rw [cubicXiAfterFormalMobius_eq]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, liMobiusSeries_coeff,
    pow_succ]

@[simp] theorem cubicXiAfterFormalMobius_coeff_three :
    coeff 3 (cubicXiAfterFormalMobius a₁ a₂ a₃) = a₁ + 2 * a₂ + a₃ := by
  rw [cubicXiAfterFormalMobius_eq]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, liMobiusSeries_coeff,
    pow_succ]
  ring

@[simp] theorem cubicXiAfterFormalMobius_inv_coeff_zero :
    coeff 0 (cubicXiAfterFormalMobius a₁ a₂ a₃)⁻¹ = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
    ← coeff_zero_eq_constantCoeff_apply, cubicXiAfterFormalMobius_coeff_zero]
  simp

theorem cubicXiAfterFormalMobius_inv_coeff_one :
    coeff 1 (cubicXiAfterFormalMobius a₁ a₂ a₃)⁻¹ = -a₁ := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, ← coeff_zero_eq_constantCoeff_apply]

theorem cubicXiAfterFormalMobius_inv_coeff_two :
    coeff 2 (cubicXiAfterFormalMobius a₁ a₂ a₃)⁻¹ =
      a₁ ^ 2 - a₁ - a₂ := by
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.antidiagonal, ← coeff_zero_eq_constantCoeff_apply,
    cubicXiAfterFormalMobius_inv_coeff_one]
  ring

theorem cubicLiFormalCoefficient_zero :
    coeff 0 (cubicLiFormalLogDerivative a₁ a₂ a₃) = a₁ := by
  rw [cubicLiFormalLogDerivative]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, PowerSeries.coeff_derivative]

theorem cubicLiFormalCoefficient_one :
    coeff 1 (cubicLiFormalLogDerivative a₁ a₂ a₃) =
      2 * a₁ + 2 * a₂ - a₁ ^ 2 := by
  rw [cubicLiFormalLogDerivative]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    cubicXiAfterFormalMobius_inv_coeff_one]
  ring

theorem cubicLiFormalCoefficient_two :
    coeff 2 (cubicLiFormalLogDerivative a₁ a₂ a₃) =
      3 * a₁ + 6 * a₂ + 3 * a₃ - 3 * a₁ ^ 2 - 3 * a₁ * a₂ + a₁ ^ 3 := by
  rw [cubicLiFormalLogDerivative]
  norm_num [Finset.antidiagonal, PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    cubicXiAfterFormalMobius_inv_coeff_one,
    cubicXiAfterFormalMobius_inv_coeff_two]
  ring

end CubicCheck

end RHGarden
