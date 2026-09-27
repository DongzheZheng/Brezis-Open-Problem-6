import BrezisOP6.WeakBallEnergy
import BrezisOP6.EnergyAnnulusIntegral

/-! A positive annulus strictly inside the ball has the ordinary Lebesgue measure. -/

namespace BrezisOP6

open MeasureTheory Set Metric

theorem weakBallMeasure_restrict_annulus_eq_volume
    (n : ℕ) (R δ ρ : ℝ) (hρR : ρ < R) :
    (weakBallMeasure n R).restrict (energyPositiveAnnulus n δ ρ) =
      volume.restrict (energyPositiveAnnulus n δ ρ) := by
  have hsub : energyPositiveAnnulus n δ ρ ⊆
      Metric.ball (0 : GLEuclidean n) R := by
    intro x hx
    change ‖x‖ ∈ Ioc δ ρ at hx
    simpa only [Metric.mem_ball, dist_zero_right] using
      (lt_of_le_of_lt hx.2 hρR)
  exact Measure.restrict_restrict_of_subset hsub

end BrezisOP6
