import BrezisOP6.EnergySingleProfileTheorem
import BrezisOP6.EnergyWholeBallInterior

/-!
# Single-profile GL identity with the finite-ball endpoint convention

The radial equation and second derivative are needed only at radii strictly
inside the ball.  A continuous boundary-flux trace replaces any equation or
two-sided second derivative at the outer endpoint.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem smooth_positiveBall_singleProfile_identity_interior (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ B : ℕ → ℝ)
    (hρpos : ∀ k, 0 < ρ k)
    (hρR : ∀ k, ρ k ≤ R)
    (hρanti : Antitone ρ)
    (hρzero : Tendsto ρ atTop (𝓝 0))
    (hBzero : Tendsto B atTop (𝓝 0))
    (hp : ∀ r, 0 < r → r < R → DifferentiableAt ℝ p r)
    (hp' : ∀ r, 0 < r → r < R → DifferentiableAt ℝ (deriv p) r)
    (hz : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ∀ r, 0 < r → r < R →
        DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hode : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        ContinuousOn
          (radialBoundaryFlux m p (energyRaySq (m + 3) z ω))
          (Set.uIcc (ρ k) R))
    (hfluxInt : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        IntervalIntegrable
          (deriv (radialBoundaryFlux m p
            (energyRaySq (m + 3) z ω))) volume (ρ k) R)
    (hPolarInt : ∀ k, Integrable
      (fun q : Metric.sphere (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
          ((energyPositiveAnnulus (m + 3) (ρ k) R).indicator
            (energySpatialGapDensity m p z))
          (unitSpherePolarPoint (m + 3) q))
      ((unitSphereMeasure (m + 3)).prod
        (unitSphereRadiusMeasure (m + 3))))
    (hDensityInt : IntegrableOn (energySpatialGapDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume)
    (hOuterInt : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R)
      (unitSphereMeasure (m + 3)))
    (hInnerInt : ∀ k, Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) (ρ k))
      (unitSphereMeasure (m + 3)))
    (hInnerBound : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        |radialBoundaryFlux m p (energyRaySq (m + 3) z ω) (ρ k)| ≤ B k)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1)
    (huInt : IntegrableOn
      (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hvInt : IntegrableOn
      (euclideanGLDensity (m + 3) (radialVortex (m + 3) p))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hredInt : IntegrableOn (energyReducedSpatialDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume) :
    glEnergy (volume.restrict (energyPositiveClosedBall (m + 3) R))
        (euclideanGradientSq (m + 3))
        (fun y => p ‖y‖ • z y) -
      glEnergy (volume.restrict (energyPositiveClosedBall (m + 3) R))
        (euclideanGradientSq (m + 3))
        (radialVortex (m + 3) p) =
      ∫ x in energyPositiveClosedBall (m + 3) R,
        singleProfileDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => p ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x := by
  have hwhole := euclidean_positiveBall_energy_identity_interior m p z R ρ B
    hρpos hρR hρanti hρzero hBzero hp hp' hz hode
    hfluxCont hfluxInt hPolarInt hDensityInt hOuterInt hInnerInt hInnerBound
  have hsplit := energySpatialGapDensity_integral_split m R p z
    huInt hvInt hredInt
  have houter := energyOuterFlux_integral_zero m p z R hunit
  rw [hsplit, houter] at hwhole
  rw [glEnergy_euclidean_eq_density, glEnergy_euclidean_eq_density]
  linarith


end

end BrezisOP6
