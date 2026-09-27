import BrezisOP6.EnergyWholeBallIdentity
import BrezisOP6.EnergyAnnulusInterior

/-!
# Whole punctured ball identity from an interior radial ODE

The finite-ball radial profile is required to solve its ODE only for
`0 < r < R`; at `R` the boundary flux needs a continuous trace.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem euclidean_positiveBall_energy_identity_interior (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ) (ρ : ℕ → ℝ) (B : ℕ → ℝ)
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
        |radialBoundaryFlux m p (energyRaySq (m + 3) z ω) (ρ k)| ≤ B k) :
    (∫ x in energyPositiveClosedBall (m + 3) R,
      energySpatialGapDensity m p z x) =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R
        ∂(unitSphereMeasure (m + 3)) := by
  let density := energySpatialGapDensity m p z
  let outer : Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
    fun ω => radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R
  let inner : ℕ → Metric.sphere (0 : GLEuclidean (m + 3)) 1 → ℝ :=
    fun k ω => radialBoundaryFlux m p (energyRaySq (m + 3) z ω) (ρ k)
  have hlocal (k : ℕ) (r : ℝ) (hr : r ∈ Set.uIoo (ρ k) R) :
      0 < r ∧ r < R := by
    have hr' : r ∈ Ioo (ρ k) R := by
      simpa [Set.uIoo_of_le (hρR k)] using hr
    exact ⟨lt_trans (hρpos k) hr'.1, hr'.2⟩
  have hAnnulus (k : ℕ) :
      (∫ x in energyPositiveAnnulus (m + 3) (ρ k) R,
        density x) =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        (outer ω - inner k ω) ∂(unitSphereMeasure (m + 3)) := by
    exact euclidean_annulus_energy_identity_interior m p z (ρ k) R
      (hρpos k) (hρR k)
      (fun r hr => hp r (hlocal k r hr).1 (hlocal k r hr).2)
      (fun r hr => hp' r (hlocal k r hr).1 (hlocal k r hr).2)
      (fun ω r hr => hz ω r (hlocal k r hr).1 (hlocal k r hr).2)
      (fun r hr => hode r (hlocal k r hr).1 (hlocal k r hr).2)
      (hfluxCont k) (hfluxInt k) (hPolarInt k)
  have hBallLimit : Tendsto
      (fun k => ∫ x in energyPositiveAnnulus (m + 3) (ρ k) R,
        density x) atTop
      (𝓝 (∫ x in energyPositiveClosedBall (m + 3) R,
        density x)) :=
    annulus_integral_tendsto_positiveBall (m + 3) R ρ
      hρpos hρanti hρzero density hDensityInt
  have hInnerLimit : Tendsto
      (fun k => ∫ ω, inner k ω ∂(unitSphereMeasure (m + 3)))
      atTop (𝓝 0) :=
    sphere_integral_uniform_flux_tendsto_zero (m + 3) inner B
      hBzero hInnerBound
  have hFluxLimit : Tendsto
      (fun k => ∫ ω, outer ω - inner k ω
        ∂(unitSphereMeasure (m + 3))) atTop
      (𝓝 (∫ ω, outer ω ∂(unitSphereMeasure (m + 3)))) := by
    have hfun :
        (fun k => ∫ ω, outer ω - inner k ω
          ∂(unitSphereMeasure (m + 3))) =
        (fun k => (∫ ω, outer ω ∂(unitSphereMeasure (m + 3))) -
          ∫ ω, inner k ω ∂(unitSphereMeasure (m + 3))) := by
      funext k
      exact integral_sub hOuterInt (hInnerInt k)
    rw [hfun]
    simpa using (tendsto_const_nhds.sub hInnerLimit)
  have hfun :
      (fun k => ∫ x in energyPositiveAnnulus (m + 3) (ρ k) R,
        density x) =
      (fun k => ∫ ω, outer ω - inner k ω
        ∂(unitSphereMeasure (m + 3))) := by
    funext k
    exact hAnnulus k
  rw [hfun] at hBallLimit
  exact tendsto_nhds_unique hBallLimit hFluxLimit


end

end BrezisOP6
