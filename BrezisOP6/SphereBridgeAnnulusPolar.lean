import BrezisOP6.SphereBridgePolarSpatial
import BrezisOP6.EnergyAnnulusIntegral

/-!
# Polar integration of the actual quadratic bridge

The previous pointwise identity is pushed through mathlib's genuine
Euclidean polar-coordinate change of variables.  The result is an equality
between a spatial annulus integral and a sphere-outer/radius-inner
integral of the already identified vector bridge integrand.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem euclideanQuadraticBridge_annulus_eq_sphere_interval
    (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hz : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
      ∀ r ∈ Set.Ioo ρ R,
        DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hPolarInt : Integrable
      (fun q : Metric.sphere
          (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
          ((energyPositiveAnnulus (m + 3) ρ R).indicator
            (euclideanQuadraticBridgeDensity m f F z))
          (unitSpherePolarPoint (m + 3) q))
      ((unitSphereMeasure (m + 3)).prod
        (unitSphereRadiusMeasure (m + 3)))) :
    (∫ x in energyPositiveAnnulus (m + 3) ρ R,
      euclideanQuadraticBridgeDensity m f F z x) =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        (∫ r in ρ..R,
          vectorSphereBridgePointwise m f F z r ω ∂volume)
        ∂(unitSphereMeasure (m + 3)) := by
  rw [annulus_integral_eq_sphere_interval (m + 3) (by omega)
    ρ R hρ hρR _ hPolarInt]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [intervalIntegral.integral_of_le hρR]
  rw [intervalIntegral.integral_of_le hρR]
  apply integral_congr_ae
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using (measure_singleton R : volume {R} = 0)
  have hInterior : ∀ᵐ r : ℝ ∂volume.restrict (Set.Ioc ρ R),
      r ∈ Set.Ioo ρ R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  filter_upwards [hInterior] with r hr'
  have hrpos : 0 < r := lt_trans hρ hr'.1
  have hpt := vectorSphereBridgePointwise_eq_jacobian_spatial
    m f F z r hrpos ω (hz ω r hr')
  simpa only [show (m + 3) - 1 = m + 2 by omega,
    energySphereRay] using hpt.symm

end

end BrezisOP6
