import BrezisOP6.EnergySharedProductIntegrable
import BrezisOP6.EnergyConcreteInteriorData
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# Concrete second-profile data for the shared quotient

In the paired energy identity, both profiles act on the same quotient
`z=u/f`.  This constructor derives all spatial, polar, and fixed-sphere
integrability requirements for the `F` identity from ordinary `C¹`
regularity and the regular-origin factors.  Its remaining inputs are
annular ODE/FTC data and the explicit small-sphere flux estimate.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

theorem smoothProfileBallInteriorData_second_shared_quotient_of_taylor_C1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (β A C : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ B : ℕ → ℝ)
    (hρpos : ∀ k, 0 < ρ k)
    (hρle : ∀ k, ρ k ≤ R)
    (hρanti : Antitone ρ)
    (hρzero : Tendsto ρ atTop (𝓝 0))
    (hBzero : Tendsto B atTop (𝓝 0))
    (hFderivdiff : ∀ r, 0 < r → r < R →
      DifferentiableAt ℝ (deriv F) r)
    (hFode : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r))
    (hfluxCont : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        ContinuousOn
          (radialBoundaryFlux m F
            (energyRaySq (m + 3)
              (fun y => (f ‖y‖)⁻¹ • u y) ω))
          (Set.uIcc (ρ k) R))
    (hfluxFTC : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        IntervalIntegrable
          (deriv (radialBoundaryFlux m F
            (energyRaySq (m + 3)
              (fun y => (f ‖y‖)⁻¹ • u y) ω)))
          volume (ρ k) R)
    (hfluxBound : ∀ k,
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        |radialBoundaryFlux m F
          (energyRaySq (m + 3)
            (fun y => (f ‖y‖)⁻¹ • u y) ω) (ρ k)| ≤ B k)
    (hF0 : F 0 = 0) (hβ : 0 < β)
    (hHf0 : Hf 0 = β)
    (hTaylor : RadialOriginTaylorOn f β A C R)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (huC1 : ContDiff ℝ 1 u)
    (hfPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hFle : ∀ r : ℝ, 0 < r → r ≤ R →
      0 ≤ F r ∧ F r ≤ f r)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2)) :
    SmoothProfileBallInteriorData m F
      (fun y : GLEuclidean (m + 3) =>
        (f ‖y‖)⁻¹ • u y) R ρ B := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun y => (f ‖y‖)⁻¹ • u y
  have hprod : IntegrableOn (euclideanGLDensity (m + 3)
      (fun y => F ‖y‖ • z y))
      (energyPositiveClosedBall (m + 3) R) volume :=
    shared_quotient_second_product_GL_integrableOn_positiveBall
      m R f F Hf HF β u hHf hHF hHf0 hβ hfFactor hFFactor
      hfPos huC1
  have hvortex : IntegrableOn
      (euclideanGLDensity (m + 3) (radialVortex (m + 3) F))
      (energyPositiveClosedBall (m + 3) R) volume :=
    radialVortex_GL_integrableOn_positiveBall_of_factor
      m R F HF hHF hFFactor
  have hred : IntegrableOn (energyReducedSpatialDensity m F z)
      (energyPositiveClosedBall (m + 3) R) volume :=
    energyReducedSpatialDensity_shared_quotient_integrableOn_of_taylor_globalC1
      m R hR f F β A C u hF0 hβ hTaylor hfC1 hFC1 huC1
      hfPos hFle
  have hgap : IntegrableOn (energySpatialGapDensity m F z)
      (energyPositiveClosedBall (m + 3) R) volume :=
    energySpatialGapDensity_integrableOn_of_components
      m R F z hprod hvortex hred
  have hz : ContDiffOn ℝ 1 z
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall (m + 3) R f u
      hfC1 hfPos huC1.contDiffOn
  have hopen : IsOpen {x : GLEuclidean (m + 3) |
      0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  refine {
    rho_pos := hρpos
    rho_le_radius := hρle
    rho_antitone := hρanti
    rho_tendsto_zero := hρzero
    flux_bound_tendsto_zero := hBzero
    profile_diff := fun r _ _ => hFC1.differentiable_one r
    profile_deriv_diff := hFderivdiff
    quotient_diff_on_rays := ?_
    profile_ode := hFode
    flux_interval_continuous := hfluxCont
    flux_interval_integrable := hfluxFTC
    polar_integrable := ?_
    outer_flux_integrable := ?_
    inner_flux_integrable := ?_
    inner_flux_bound := hfluxBound
    product_energy_integrable := hprod
    vortex_energy_integrable := hvortex
    reduced_density_integrable := hred }
  · intro ω r hr hrR
    have hx : energySphereRay (m + 3) ω r ∈
        {x : GLEuclidean (m + 3) |
          0 < ‖x‖ ∧ ‖x‖ < R} := by
      simpa only [Set.mem_setOf_eq,
        energySphereRay_norm (m + 3) ω r hr.le] using
        (show 0 < r ∧ r < R from ⟨hr, hrR⟩)
    exact (hz.differentiableOn_one).differentiableAt
      (hopen.mem_nhds hx)
  · intro k
    have hAnn : IntegrableOn (energySpatialGapDensity m F z)
        (energyPositiveAnnulus (m + 3) (ρ k) R) volume := by
      apply hgap.mono_set
      intro x hx
      change ρ k < ‖x‖ ∧ ‖x‖ ≤ R at hx
      exact ⟨lt_trans (hρpos k) hx.1, hx.2⟩
    exact annulus_polar_indicator_integrable_of_integrableOn
      (m + 3) (by omega) (ρ k) R (hρle k)
      (energySpatialGapDensity m F z) hAnn
  · exact radialBoundaryFlux_integrable_of_shared_quotient_C0
      m R R F f u hR.le le_rfl
      huC1.continuous.continuousOn
  · intro k
    exact radialBoundaryFlux_integrable_of_shared_quotient_C0
      m R (ρ k) F f u (hρpos k).le (hρle k)
      huC1.continuous.continuousOn

end

end BrezisOP6
