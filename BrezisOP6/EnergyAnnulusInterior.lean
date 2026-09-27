import BrezisOP6.EnergyAnnulusIntegral
import BrezisOP6.EnergyRayInterior

/-!
# Euclidean annulus energy identity with interior ODE

Only the open annulus carries the radial differential equation; the outer
endpoint enters through continuity of the explicit flux.
-/

namespace BrezisOP6

open MeasureTheory Set Metric

noncomputable section

theorem euclidean_annulus_energy_identity_interior (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hp : ∀ r ∈ Set.uIoo ρ R, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ Set.uIoo ρ R, DifferentiableAt ℝ (deriv p) r)
    (hz : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ∀ r ∈ Set.uIoo ρ R,
        DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hode : ∀ r ∈ Set.uIoo ρ R,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ContinuousOn
        (radialBoundaryFlux m p (energyRaySq (m + 3) z ω))
        (Set.uIcc ρ R))
    (hfluxInt : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      IntervalIntegrable
        (deriv (radialBoundaryFlux m p
          (energyRaySq (m + 3) z ω))) volume ρ R)
    (hPolarInt : Integrable
      (fun q : Metric.sphere (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
          ((energyPositiveAnnulus (m + 3) ρ R).indicator
            (fun x => 2 *
              (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
                euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x -
                energyReducedSpatialDensity m p z x)))
          (unitSpherePolarPoint (m + 3) q))
      ((unitSphereMeasure (m + 3)).prod
        (unitSphereRadiusMeasure (m + 3)))) :
    (∫ x in energyPositiveAnnulus (m + 3) ρ R,
      2 * (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
        euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x -
        energyReducedSpatialDensity m p z x)) =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        (radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R -
          radialBoundaryFlux m p (energyRaySq (m + 3) z ω) ρ)
        ∂(unitSphereMeasure (m + 3)) := by
  let density : GLEuclidean (m + 3) → ℝ := fun x => 2 *
    (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
      euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x -
      energyReducedSpatialDensity m p z x)
  have hpolar := annulus_integral_eq_sphere_interval (m + 3)
    (by omega) ρ R hρ hρR density hPolarInt
  change (∫ x in energyPositiveAnnulus (m + 3) ρ R, density x) = _
  rw [hpolar]
  apply integral_congr_ae
  filter_upwards [] with ω
  calc
    (∫ r in ρ..R, r ^ ((m + 3) - 1) *
        density (energySphereRay (m + 3) ω r)) =
      ∫ r in ρ..R,
        2 * (r ^ (m + 2) *
          (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y)
              (energySphereRay (m + 3) ω r) -
            euclideanGLDensity (m + 3) (radialVortex (m + 3) p)
              (energySphereRay (m + 3) ω r)) -
          radialReducedWeightedDensity m r (p r)
            (energyRaySq (m + 3) z ω r)
            (energyRayGradientSq (m + 3) z ω r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc ρ R := by
        simpa [Set.uIcc_of_le hρR] using hr
      have hrpos : 0 < r := lt_of_lt_of_le hρ hr'.1
      have hrnz : r ^ (m + 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hrpos)
      have hnorm := energySphereRay_norm (m + 3) ω r hrpos.le
      simp only [show (m + 3) - 1 = m + 2 by omega,
        density, energyReducedSpatialDensity, energyRaySq,
        energyRayGradientSq, hnorm]
      field_simp [hrnz]
    _ = _ := energyRay_annulus_ibp_interior m p z ω ρ R hρ hρR hp hp'
      (hz ω) hode (hfluxCont ω) (hfluxInt ω)


end

end BrezisOP6
