import RHGarden.Xi

noncomputable section

namespace RHGarden

def liMobius (z : ℂ) : ℂ := -z / (1 - z)

def liStandard (z : ℂ) : ℂ := 1 / (1 - z)

theorem liMobius_eq_one_sub_liStandard {z : ℂ} (hz : z ≠ 1) :
    liMobius z = 1 - liStandard z := by
  unfold liMobius liStandard
  field_simp
  ring

theorem riemannXi_liMobius_eq_liStandard {z : ℂ} (hz : z ≠ 1) :
    riemannXi (liMobius z) = riemannXi (liStandard z) := by
  rw [liMobius_eq_one_sub_liStandard hz, riemannXi_one_sub]

end RHGarden
