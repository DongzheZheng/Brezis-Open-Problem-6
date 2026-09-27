import BrezisOP6.EnergyFluxSphereIntegrability
import BrezisOP6.SpherePolarAnnulusIntegrability
import BrezisOP6.EnergySmoothBallBridgeInterior
import BrezisOP6.EnergyConcreteReducedDensity

/-!
# Concrete integrability fields for the smooth profile identity

The energy and spherical-integrability fields of the interior bridge data
follow from the actual smooth numerator, the regular radial factor, and
one reduced-density estimate.  The latter can be proved by the
inverse-square quotient estimate; the remaining inputs here are precisely
the radial ODE, differentiation, and endpoint fundamental-theorem data.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

/-- Assemble the interior identity with all five integrability fields
deduced from the concrete smooth competitor.  In particular, polar
integrability is obtained by the measure-preserving polar map from the
spatial density rather than assumed independently. -/
theorem smoothProfileBallInteriorData_of_C1_quotient
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (p H : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ B : ℕ → ℝ)
    (hρpos : ∀ k, 0 < ρ k)
    (hρle : ∀ k, ρ k ≤ R)
    (hρanti : Antitone ρ)
    (hρzero : Tendsto ρ atTop (𝓝 0))
    (hBzero : Tendsto B atTop (𝓝 0))
    (hpdiff : ∀ r, 0 < r → r < R → DifferentiableAt ℝ p r)
    (hpderivdiff : ∀ r, 0 < r → r < R →
      DifferentiableAt ℝ (deriv p) r)
    (hzdiff : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
      ∀ r, 0 < r → r < R →
        DifferentiableAt ℝ
          (fun y : GLEuclidean (m + 3) =>
            (p ‖y‖)⁻¹ • u y)
          (energySphereRay (m + 3) ω r))
    (hode : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        ContinuousOn
          (radialBoundaryFlux m p
            (energyRaySq (m + 3)
              (fun y => (p ‖y‖)⁻¹ • u y) ω))
          (Set.uIcc (ρ k) R))
    (hfluxFTC : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        IntervalIntegrable
          (deriv (radialBoundaryFlux m p
            (energyRaySq (m + 3)
              (fun y => (p ‖y‖)⁻¹ • u y) ω)))
          volume (ρ k) R)
    (hfluxBound : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        |radialBoundaryFlux m p
          (energyRaySq (m + 3)
            (fun y => (p ‖y‖)⁻¹ • u y) ω) (ρ k)| ≤ B k)
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hpPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < p r)
    (hH : ContDiff ℝ 1 H)
    (hpFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      p r = r * H (r ^ 2))
    (hred : IntegrableOn
      (energyReducedSpatialDensity m p
        (fun y : GLEuclidean (m + 3) =>
          (p ‖y‖)⁻¹ • u y))
      (energyPositiveClosedBall (m + 3) R) volume) :
    SmoothProfileBallInteriorData m p
      (fun y : GLEuclidean (m + 3) =>
        (p ‖y‖)⁻¹ • u y) R ρ B := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (p ‖y‖)⁻¹ • u y
  have hprod := quotient_product_GL_integrableOn_positiveBall_of_C1
    m R p u hu hdu hpPos
  have hvortex := radialVortex_GL_integrableOn_positiveBall_of_factor
    m R p H hH hpFactor
  have hgap : IntegrableOn (energySpatialGapDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume :=
    energySpatialGapDensity_integrableOn_of_components
      m R p z hprod hvortex hred
  refine {
    rho_pos := hρpos
    rho_le_radius := hρle
    rho_antitone := hρanti
    rho_tendsto_zero := hρzero
    flux_bound_tendsto_zero := hBzero
    profile_diff := hpdiff
    profile_deriv_diff := hpderivdiff
    quotient_diff_on_rays := hzdiff
    profile_ode := hode
    flux_interval_continuous := hfluxCont
    flux_interval_integrable := hfluxFTC
    polar_integrable := ?_
    outer_flux_integrable := ?_
    inner_flux_integrable := ?_
    inner_flux_bound := hfluxBound
    product_energy_integrable := hprod
    vortex_energy_integrable := hvortex
    reduced_density_integrable := hred }
  · intro k
    have hAnn : IntegrableOn (energySpatialGapDensity m p z)
        (energyPositiveAnnulus (m + 3) (ρ k) R) volume := by
      apply hgap.mono_set
      intro x hx
      change ρ k < ‖x‖ ∧ ‖x‖ ≤ R at hx
      exact ⟨lt_trans (hρpos k) hx.1, hx.2⟩
    exact annulus_polar_indicator_integrable_of_integrableOn
      (m + 3) (by omega) (ρ k) R (hρle k)
      (energySpatialGapDensity m p z) hAnn
  · exact quotient_radialBoundaryFlux_integrable_of_C0
      m R R p u hR.le le_rfl hu
  · intro k
    exact quotient_radialBoundaryFlux_integrable_of_C0
      m R (ρ k) p u (hρpos k).le (hρle k) hu

/-- For a smooth competitor and a positive regular-origin profile, all
spatial, polar, and fixed-radius integrability requirements of the
interior energy identity follow.  The hypotheses retained here are the
radial differential equation, pointwise annular differentiation, and
the endpoint flux estimate. -/
theorem smoothProfileBallInteriorData_of_taylor_C1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (p H : ℝ → ℝ) (α A C : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ B : ℕ → ℝ)
    (hρpos : ∀ k, 0 < ρ k)
    (hρle : ∀ k, ρ k ≤ R)
    (hρanti : Antitone ρ)
    (hρzero : Tendsto ρ atTop (𝓝 0))
    (hBzero : Tendsto B atTop (𝓝 0))
    (hpderivdiff : ∀ r, 0 < r → r < R →
      DifferentiableAt ℝ (deriv p) r)
    (hzdiff : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
      ∀ r, 0 < r → r < R →
        DifferentiableAt ℝ
          (fun y : GLEuclidean (m + 3) =>
            (p ‖y‖)⁻¹ • u y)
          (energySphereRay (m + 3) ω r))
    (hode : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        ContinuousOn
          (radialBoundaryFlux m p
            (energyRaySq (m + 3)
              (fun y => (p ‖y‖)⁻¹ • u y) ω))
          (Set.uIcc (ρ k) R))
    (hfluxFTC : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        IntervalIntegrable
          (deriv (radialBoundaryFlux m p
            (energyRaySq (m + 3)
              (fun y => (p ‖y‖)⁻¹ • u y) ω)))
          volume (ρ k) R)
    (hfluxBound : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        |radialBoundaryFlux m p
          (energyRaySq (m + 3)
            (fun y => (p ‖y‖)⁻¹ • u y) ω) (ρ k)| ≤ B k)
    (hp0 : p 0 = 0) (hα : 0 < α)
    (hTaylor : RadialOriginTaylorOn p α A C R)
    (hpC1 : ContDiff ℝ 1 p) (huC1 : ContDiff ℝ 1 u)
    (hpPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < p r)
    (hH : ContDiff ℝ 1 H)
    (hpFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      p r = r * H (r ^ 2)) :
    SmoothProfileBallInteriorData m p
      (fun y : GLEuclidean (m + 3) =>
        (p ‖y‖)⁻¹ • u y) R ρ B := by
  exact smoothProfileBallInteriorData_of_C1_quotient
    m R hR p H u ρ B hρpos hρle hρanti hρzero hBzero
    (fun r _ _ => hpC1.differentiable_one r)
    hpderivdiff hzdiff hode hfluxCont hfluxFTC hfluxBound
    huC1.continuous.continuousOn
    (huC1.continuous_fderiv (by norm_num)).continuousOn
    hpPos hH hpFactor
    (energyReducedSpatialDensity_quotient_integrableOn_of_taylor_globalC1
      m R hR p α A C u hp0 hα hTaylor hpC1 huC1 hpPos)

end

end BrezisOP6
