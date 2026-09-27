import BrezisOP6.EnergyBridgeNonnegative
import BrezisOP6.EnergyPublishedBallInterface
import BrezisOP6.EnergyQuadraticIntegrability

/-!
# The smooth finite-ball minimization step

This theorem joins the proved two-profile energy identity, the published
entire-vortex minimum, and the geometric quadratic-bridge estimate.  The
published minimum is applied to a smooth representative `v` of the
transformed field: literal division defines the latter to be zero at the
origin, whereas its removable value need not be zero.  The representative
has the same actual ball energy by the proved null-point modification lemma.
The quadratic hypothesis concerns the actual Euclidean density, so that
the spherical/Picone theorem can discharge it without a change of model.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- The radial finite-ball vortex minimizes among smooth competitors once
the separately proved sphere/Picone estimate is supplied for that competitor.
The published input remains the entire-vortex same-boundary theorem. -/
theorem smoothBallEnergy_minimality_of_quadraticBridge
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hf : SmoothProfileBallInteriorData m f z R ρf Bf)
    (hF : SmoothProfileBallInteriorData m F z R ρF BF)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hvOff : ∀ x : GLEuclidean (m + 3), x ≠ 0 →
      v x = F ‖x‖ • z x)
    (hvC1 : ContDiffOn ℝ 1 v
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hvTrace : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      v x = radialVortex (m + 3) F x)
    (hquarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hquad : 0 ≤
      ∫ x, euclideanQuadraticBridgeDensity m f F z x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R
        (fun x => f ‖x‖ • z x) := by
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hf.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hF.reduced_density_integrable
  have hbridgeInt := bridgeEnergyDensity_integrable_of_single
    m R f F z hfInt hFInt
  have hquadInt := euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    m R f F z hbridgeInt hquarticInt
  have hbridgeNonneg := bridgeEnergyIntegral_nonneg_of_quadratic
    m R f F z hbridgeInt hquadInt hquad hFnonneg hFle
  have hbridgeLe := euclideanBall_energy_gap_ge_bridge_of_C1_representative
    m R hR f F z v ρf Bf ρF BF hf hF hunit
    hPublished hvOff hvC1 hvTrace
  linarith

end

end BrezisOP6
