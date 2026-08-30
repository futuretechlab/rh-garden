import RHGarden.LiFormal
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Binomial

noncomputable section

namespace RHGarden

open PowerSeries

/-- Xi normalized to take the value one at `s = 1`. -/
def normalizedXi (s : ℂ) : ℂ := 2 * riemannXi s

@[simp] theorem normalizedXi_one : normalizedXi 1 = 1 := by
  simp [normalizedXi, riemannXi_one]

@[simp] theorem normalizedXiAtOne_zero : normalizedXiAtOne 0 = 1 := by
  simp [normalizedXiAtOne, riemannXi_one]

@[simp] theorem analyticLiXi_zero : analyticLiXi 0 = 1 := by
  simp [analyticLiXi, analyticLiMobius]

/-- The principal logarithm is used only as a germ at `u = 0`, where its
argument is one. -/
def liLocalLog (u : ℂ) : ℂ := Complex.log (normalizedXiAtOne u)

/-- The principal logarithm of the analytically composed Li xi germ. -/
def liGeneratingLog (z : ℂ) : ℂ := Complex.log (analyticLiXi z)

theorem analyticAt_liLocalLog : AnalyticAt ℂ liLocalLog 0 := by
  unfold liLocalLog
  apply analyticAt_normalizedXiAtOne.clog
  simp [Complex.slitPlane]

theorem analyticAt_liGeneratingLog : AnalyticAt ℂ liGeneratingLog 0 := by
  unfold liGeneratingLog
  apply analyticAt_analyticLiXi.clog
  simp [Complex.slitPlane]

@[simp] theorem liLocalLog_zero : liLocalLog 0 = 0 := by
  simp [liLocalLog]

@[simp] theorem liGeneratingLog_zero : liGeneratingLog 0 = 0 := by
  simp [liGeneratingLog]

theorem deriv_liGeneratingLog_zero :
    deriv liGeneratingLog 0 = logDeriv analyticLiXi 0 := by
  change deriv (Complex.log ∘ analyticLiXi) 0 = logDeriv analyticLiXi 0
  exact Complex.deriv_log_comp_eq_logDeriv
    analyticAt_analyticLiXi.differentiableAt (by simp [Complex.slitPlane])

/-- Zero-based analytic generating coefficients; index `n` is intended to be
the classical `λ_(n+1)`, but no equality to another sequence is definitional. -/
def liGeneratingCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1) liGeneratingLog 0 / (n.factorial : ℂ)

/-- Li's original derivative expression with the independently normalized
entire xi function. -/
def normalizedClassicalLiCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1)
      (fun s : ℂ ↦ s ^ n * Complex.log (normalizedXi s)) 1 /
    (n.factorial : ℂ)

/-- The same original derivative expression in the local coordinate
`u = s - 1`. -/
def shiftedClassicalLiCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1)
      (fun u : ℂ ↦ (1 + u) ^ n * liLocalLog u) 0 /
    (n.factorial : ℂ)

theorem normalizedClassicalLiCoefficient_eq_shifted (n : ℕ) :
    normalizedClassicalLiCoefficient n = shiftedClassicalLiCoefficient n := by
  let f : ℂ → ℂ := fun s ↦ s ^ n * Complex.log (normalizedXi s)
  have hshift : iteratedDeriv (n + 1) f 1 =
      iteratedDeriv (n + 1) (fun u : ℂ ↦ f (1 + u)) 0 := by
    simpa using (congrFun (iteratedDeriv_comp_const_add (n + 1) f 1) 0).symm
  simpa [normalizedClassicalLiCoefficient, shiftedClassicalLiCoefficient,
    f, liLocalLog, normalizedXiAtOne, normalizedXi] using congrArg
      (fun z : ℂ ↦ z / (n.factorial : ℂ)) hshift

/-- Algebraic Taylor coefficients of the local logarithm. -/
def liLocalLogTaylor : PowerSeries ℂ :=
  mk fun k ↦ iteratedDeriv k liLocalLog 0 / (k.factorial : ℂ)

@[simp] theorem liLocalLogTaylor_constantCoeff :
    constantCoeff liLocalLogTaylor = 0 := by
  simp [liLocalLogTaylor, iteratedDeriv_zero]

def liLocalLogFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun k ↦
    iteratedDeriv k liLocalLog 0 / (k.factorial : ℂ)

theorem liLocalLog_hasFPowerSeriesAt :
    HasFPowerSeriesAt liLocalLog liLocalLogFPowerSeries 0 := by
  exact analyticAt_liLocalLog.hasFPowerSeriesAt

theorem liLocalLogFPowerSeries_coeff (n : ℕ) :
    liLocalLogFPowerSeries.coeff n = coeff n liLocalLogTaylor := by
  simp [liLocalLogFPowerSeries, liLocalLogTaylor]

/-- The analytically certified composition of the local logarithm with the Li
Mobius germ. -/
def liGeneratingLogFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  liLocalLogFPowerSeries.comp liMobiusFPowerSeries

theorem liGeneratingLog_hasFPowerSeriesAt_comp :
    HasFPowerSeriesAt liGeneratingLog liGeneratingLogFPowerSeries 0 := by
  have houter : HasFPowerSeriesAt liLocalLog liLocalLogFPowerSeries
      (analyticLiMobius 0) := by
    simpa [analyticLiMobius] using liLocalLog_hasFPowerSeriesAt
  have hcomp := houter.comp liMobius_hasFPowerSeriesAt
  change HasFPowerSeriesAt (liLocalLog ∘ analyticLiMobius)
    (liLocalLogFPowerSeries.comp liMobiusFPowerSeries) 0
  exact hcomp

def liGeneratingLogTaylorFMS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun k ↦
    iteratedDeriv k liGeneratingLog 0 / (k.factorial : ℂ)

theorem liGeneratingLogFMS_eq_derivativeTaylor :
    liGeneratingLogFPowerSeries = liGeneratingLogTaylorFMS := by
  apply liGeneratingLog_hasFPowerSeriesAt_comp.eq_formalMultilinearSeries
  exact analyticAt_liGeneratingLog.hasFPowerSeriesAt

theorem liGeneratingCoefficient_eq_succ_mul_fms_coeff (n : ℕ) :
    liGeneratingCoefficient n =
      (n + 1 : ℂ) * liGeneratingLogFPowerSeries.coeff (n + 1) := by
  rw [liGeneratingLogFMS_eq_derivativeTaylor]
  simp only [liGeneratingCoefficient, liGeneratingLogTaylorFMS,
    FormalMultilinearSeries.coeff_ofScalars]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

end RHGarden
