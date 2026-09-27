import BrezisOP6.EnergyOpenBall
import BrezisOP6.EnergyConcreteBridge

/-!
# Two smooth single-profile identities on the actual Euclidean ball

This file applies the proved punctured-ball single-profile identity twice,
once to the finite-ball profile and once to the entire profile, with the
*same* quotient field.  Nullity of the origin and outer sphere converts both
identities to ordinary open-ball energy identities.  The remaining inputs
are the explicit analytic conditions of the single-profile theorem, the
published entire-vortex minimum, and membership of the transformed
perturbation in its energy-closure class.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Analytic conditions for applying the proved smooth single-profile
identity to one radial profile.  The unit boundary trace of the common
quotient field is kept outside this package, since it is shared by the two
profiles.  No energy identity or bridge conclusion is a field. -/
structure SmoothProfileBallData (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ B : ℕ → ℝ) : Prop where
  rho_pos : ∀ k, 0 < ρ k
  rho_le_radius : ∀ k, ρ k ≤ R
  rho_antitone : Antitone ρ
  rho_tendsto_zero : Tendsto ρ atTop (𝓝 0)
  flux_bound_tendsto_zero : Tendsto B atTop (𝓝 0)
  profile_diff : ∀ r, 0 < r → r ≤ R → DifferentiableAt ℝ p r
  profile_deriv_diff : ∀ r, 0 < r → r ≤ R →
    DifferentiableAt ℝ (deriv p) r
  quotient_diff_on_rays : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
    ∀ r, 0 < r → r ≤ R →
      DifferentiableAt ℝ z (energySphereRay (m + 3) ω r)
  profile_ode : ∀ r, 0 < r → r ≤ R →
    radialODEAt ((m : ℝ) + 3) r
      (p r) (deriv p r) (deriv (deriv p) r)
  flux_interval_integrable : ∀ k,
    ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      IntervalIntegrable
        (deriv (radialBoundaryFlux m p
          (energyRaySq (m + 3) z ω))) volume (ρ k) R
  polar_integrable : ∀ k, Integrable
    (fun q : Metric.sphere (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
      (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
        ((energyPositiveAnnulus (m + 3) (ρ k) R).indicator
          (energySpatialGapDensity m p z))
        (unitSpherePolarPoint (m + 3) q))
    ((unitSphereMeasure (m + 3)).prod
      (unitSphereRadiusMeasure (m + 3)))
  spatial_gap_integrable : IntegrableOn (energySpatialGapDensity m p z)
    (energyPositiveClosedBall (m + 3) R) volume
  outer_flux_integrable : Integrable
    (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
      radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R)
    (unitSphereMeasure (m + 3))
  inner_flux_integrable : ∀ k, Integrable
    (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
      radialBoundaryFlux m p (energyRaySq (m + 3) z ω) (ρ k))
    (unitSphereMeasure (m + 3))
  inner_flux_bound : ∀ k,
    ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      |radialBoundaryFlux m p
        (energyRaySq (m + 3) z ω) (ρ k)| ≤ B k
  product_energy_integrable : IntegrableOn
    (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y))
    (energyPositiveClosedBall (m + 3) R) volume
  vortex_energy_integrable : IntegrableOn
    (euclideanGLDensity (m + 3) (radialVortex (m + 3) p))
    (energyPositiveClosedBall (m + 3) R) volume
  reduced_density_integrable : IntegrableOn
    (energyReducedSpatialDensity m p z)
    (energyPositiveClosedBall (m + 3) R) volume
  single_density_integrable : Integrable
    (singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => p ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2))
    (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R))

/-- The proved punctured-ball identity, written as an identity of concrete
Ginzburg--Landau energies on the ordinary open Euclidean ball. -/
theorem smooth_openBall_singleProfile_identity (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ B : ℕ → ℝ)
    (h : SmoothProfileBallData m p z R ρ B)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1) :
    euclideanBallEnergy (m + 3) R (fun y => p ‖y‖ • z y) -
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) p) =
    ∫ x, singleProfileDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => p ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)) := by
  have hpositive := smooth_positiveBall_singleProfile_identity
    m p z R ρ B h.rho_pos h.rho_le_radius h.rho_antitone
    h.rho_tendsto_zero h.flux_bound_tendsto_zero h.profile_diff
    h.profile_deriv_diff h.quotient_diff_on_rays h.profile_ode
    h.flux_interval_integrable h.polar_integrable
    h.spatial_gap_integrable h.outer_flux_integrable
    h.inner_flux_integrable h.inner_flux_bound hunit
    h.product_energy_integrable h.vortex_energy_integrable
    h.reduced_density_integrable
  simp only [energyPositiveClosedBall_restrict_eq_ball] at hpositive
  simpa only [glEnergy_eq_euclideanBallEnergy] using hpositive

/-- The actual finite-ball bridge comparison assembled from two proved
single-profile identities.  The numerator of the bridge is the energy of
the finite-ball profile times the common quotient field. -/
theorem euclideanBall_energy_gap_ge_bridge_of_smooth_profiles
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hf : SmoothProfileBallData m f z R ρf Bf)
    (hF : SmoothProfileBallData m F z R ρF BF)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1)
    (hPublished : PublishedC1VortexMinimality (m + 3)
      (radialVortex (m + 3) F))
    (hclosure : BallEnergyClosure (m + 3) R
      (radialVortex (m + 3) F)
      (fun x => F ‖x‖ • z x - radialVortex (m + 3) F x)) :
    (∫ x, bridgeEnergyDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) ≤
      euclideanBallEnergy (m + 3) R (fun x => f ‖x‖ • z x) -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f) := by
  have hv : (fun x : GLEuclidean (m + 3) => F ‖x‖ • z x) =
      fun x => radialVortex (m + 3) F x +
        (F ‖x‖ • z x - radialVortex (m + 3) F x) := by
    funext x
    abel
  exact euclideanBall_energy_gap_ge_bridge_of_publishedC1
    (m + 3) R (by omega) hR
    (fun x => f ‖x‖ • z x) (radialVortex (m + 3) f)
    (fun x => F ‖x‖ • z x) (radialVortex (m + 3) F)
    (fun x => F ‖x‖ • z x - radialVortex (m + 3) F x)
    (fun y => f ‖y‖) (fun y => F ‖y‖)
    (euclideanGradientSq (m + 3) z)
    (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
    hf.single_density_integrable hF.single_density_integrable
    (smooth_openBall_singleProfile_identity m f z R ρf Bf hf hunit)
    (smooth_openBall_singleProfile_identity m F z R ρF BF hF hunit)
    hPublished hv hclosure

end

end BrezisOP6
