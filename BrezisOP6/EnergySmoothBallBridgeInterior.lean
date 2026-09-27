import BrezisOP6.EnergySingleProfileInterior
import BrezisOP6.EnergyOpenBall
import BrezisOP6.EnergyConcreteBridge
import BrezisOP6.EnergyRedundantIntegrability

/-!
# Two-profile comparison using interior radial equations

The principal finite-ball energy bridge only needs the radial profile ODE
and its second derivative on `0 < r < R`.  Continuity of the explicit
endpoint flux supplies the boundary data in the one-sided fundamental theorem
of calculus.  The published entire-vortex minimum and transformed competitor
energy-closure membership are kept as explicit external inputs.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

structure SmoothProfileBallInteriorData (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ B : ℕ → ℝ) : Prop where
  rho_pos : ∀ k, 0 < ρ k
  rho_le_radius : ∀ k, ρ k ≤ R
  rho_antitone : Antitone ρ
  rho_tendsto_zero : Tendsto ρ atTop (𝓝 0)
  flux_bound_tendsto_zero : Tendsto B atTop (𝓝 0)
  profile_diff : ∀ r, 0 < r → r < R → DifferentiableAt ℝ p r
  profile_deriv_diff : ∀ r, 0 < r → r < R →
    DifferentiableAt ℝ (deriv p) r
  quotient_diff_on_rays : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
    ∀ r, 0 < r → r < R →
      DifferentiableAt ℝ z (energySphereRay (m + 3) ω r)
  profile_ode : ∀ r, 0 < r → r < R →
    radialODEAt ((m : ℝ) + 3) r
      (p r) (deriv p r) (deriv (deriv p) r)
  flux_interval_continuous : ∀ k,
    ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ContinuousOn
        (radialBoundaryFlux m p (energyRaySq (m + 3) z ω))
        (Set.uIcc (ρ k) R)
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

/-- The proved punctured-ball identity, written as an identity of concrete
Ginzburg--Landau energies on the ordinary open Euclidean ball. -/
theorem smooth_openBall_singleProfile_identity_interior (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ B : ℕ → ℝ)
    (h : SmoothProfileBallInteriorData m p z R ρ B)
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
  have hpositive := smooth_positiveBall_singleProfile_identity_interior
    m p z R ρ B h.rho_pos h.rho_le_radius h.rho_antitone
    h.rho_tendsto_zero h.flux_bound_tendsto_zero h.profile_diff
    h.profile_deriv_diff h.quotient_diff_on_rays h.profile_ode
    h.flux_interval_continuous h.flux_interval_integrable h.polar_integrable
    (energySpatialGapDensity_integrableOn_of_components m R p z
      h.product_energy_integrable h.vortex_energy_integrable
      h.reduced_density_integrable) h.outer_flux_integrable
    h.inner_flux_integrable h.inner_flux_bound hunit
    h.product_energy_integrable h.vortex_energy_integrable
    h.reduced_density_integrable
  simp only [energyPositiveClosedBall_restrict_eq_ball] at hpositive
  simpa only [glEnergy_eq_euclideanBallEnergy] using hpositive

/-- The actual finite-ball bridge comparison assembled from two proved
single-profile identities.  The numerator of the bridge is the energy of
the finite-ball profile times the common quotient field. -/
theorem euclideanBall_energy_gap_ge_bridge_of_smooth_profiles_interior
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hf : SmoothProfileBallInteriorData m f z R ρf Bf)
    (hF : SmoothProfileBallInteriorData m F z R ρF BF)
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
    (singleProfileDensity_integrableOn_ball_of_reduced m R f z
      hf.reduced_density_integrable)
    (singleProfileDensity_integrableOn_ball_of_reduced m R F z
      hF.reduced_density_integrable)
    (smooth_openBall_singleProfile_identity_interior m f z R ρf Bf hf hunit)
    (smooth_openBall_singleProfile_identity_interior m F z R ρF BF hF hunit)
    hPublished hv hclosure


end

end BrezisOP6
