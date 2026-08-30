import RHGarden.LiCombinatorics

noncomputable section
namespace RHGarden
open PowerSeries


example (q : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ q).comp liMobiusFPowerSeries).coeff n =
      ∑ c : Composition n, q c.length := by
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.comp,
    FormalMultilinearSeries.compAlongComposition_apply]
  simp only [← Finset.sum_univ, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  simp [FormalMultilinearSeries.applyComposition,
    liMobiusFPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq]

end RHGarden
