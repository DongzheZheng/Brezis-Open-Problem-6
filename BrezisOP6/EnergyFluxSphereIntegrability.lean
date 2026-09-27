import BrezisOP6.EnergyActualFieldsIntegrable

/-!
# Integrability of actual spherical profile fluxes

At each fixed positive radius, the quotient flux is a continuous function
of the direction when the smooth numerator is continuous on the ball.
The surface measure is finite, so both inner and outer flux integrability
fields in the single-profile identity follow without extra estimates.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- A continuous spherical trace has an integrable radial boundary flux. -/
theorem radialBoundaryFlux_integrable_of_continuous_ray
    (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ)
    (hz : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        z (energySphereRay (m + 3) ω r))) :
    Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) r)
      (unitSphereMeasure (m + 3)) := by
  have hsq : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖z (energySphereRay (m + 3) ω r)‖ ^ 2) :=
    hz.norm.pow 2
  have hflux : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) r) := by
    unfold radialBoundaryFlux energyRaySq
    fun_prop
  have h : IntegrableOn
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) r)
      Set.univ (unitSphereMeasure (m + 3)) :=
    hflux.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact
        (Set.univ : Set (Metric.sphere
          (0 : GLEuclidean (m + 3)) 1)))
  change Integrable _ ((unitSphereMeasure (m + 3)).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

/-- A continuous numerator makes every positive-radius quotient flux
integrable on the physical unit sphere. -/
theorem quotient_radialBoundaryFlux_integrable_of_C0
    (m : ℕ) (R r : ℝ) (p : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R)) :
    Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p
          (energyRaySq (m + 3)
            (fun x => (p ‖x‖)⁻¹ • u x) ω) r)
      (unitSphereMeasure (m + 3)) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        energySphereRay (m + 3) ω r) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hRayMem (ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1) :
      energySphereRay (m + 3) ω r ∈
        Metric.closedBall (0 : GLEuclidean (m + 3)) R := by
    have hnorm := energySphereRay_norm (m + 3) ω r hr
    simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using hrR
  have huRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        u (energySphereRay (m + 3) ω r)) :=
    hu.comp_continuous hRay hRayMem
  have hzRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (p ‖energySphereRay (m + 3) ω r‖)⁻¹ •
          u (energySphereRay (m + 3) ω r)) := by
    have heq : (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 =>
        (p ‖energySphereRay (m + 3) ω r‖)⁻¹ •
          u (energySphereRay (m + 3) ω r)) =
        fun ω => (p r)⁻¹ • u (energySphereRay (m + 3) ω r) := by
      funext ω
      rw [energySphereRay_norm (m + 3) ω r hr]
    rw [heq]
    exact continuous_const.smul huRay
  exact radialBoundaryFlux_integrable_of_continuous_ray
    m p (fun x => (p ‖x‖)⁻¹ • u x) r hzRay

/-- The profile in the flux may differ from the denominator defining the
shared quotient.  This is the situation for the second, `F`-profile
identity, whose quotient remains `u/f`. -/
theorem radialBoundaryFlux_integrable_of_shared_quotient_C0
    (m : ℕ) (R r : ℝ) (p q : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R)) :
    Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        radialBoundaryFlux m p
          (energyRaySq (m + 3)
            (fun x => (q ‖x‖)⁻¹ • u x) ω) r)
      (unitSphereMeasure (m + 3)) := by
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        energySphereRay (m + 3) ω r) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hRayMem (ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1) :
      energySphereRay (m + 3) ω r ∈
        Metric.closedBall (0 : GLEuclidean (m + 3)) R := by
    have hnorm := energySphereRay_norm (m + 3) ω r hr
    simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using hrR
  have huRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        u (energySphereRay (m + 3) ω r)) :=
    hu.comp_continuous hRay hRayMem
  have hzRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (q ‖energySphereRay (m + 3) ω r‖)⁻¹ •
          u (energySphereRay (m + 3) ω r)) := by
    have heq : (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 =>
        (q ‖energySphereRay (m + 3) ω r‖)⁻¹ •
          u (energySphereRay (m + 3) ω r)) =
        fun ω => (q r)⁻¹ • u (energySphereRay (m + 3) ω r) := by
      funext ω
      rw [energySphereRay_norm (m + 3) ω r hr]
    rw [heq]
    exact continuous_const.smul huRay
  exact radialBoundaryFlux_integrable_of_continuous_ray
    m p (fun x => (q ‖x‖)⁻¹ • u x) r hzRay

end

end BrezisOP6
