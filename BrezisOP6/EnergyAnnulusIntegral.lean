import BrezisOP6.EnergyPolarRadial

/-!
# The actual Euclidean annulus energy identity

The polar formula and `volumeIoiPow` conversion turn the proved raywise
integration-by-parts identity into an identity for the spatial GL energy
density on a positive-radius annulus.  All profile ODE assumptions remain
local to the annulus.  The origin limit is deliberately separate.
-/

namespace BrezisOP6

open MeasureTheory Set Metric

noncomputable section

/-- The annulus with the endpoint convention used by interval integrals. -/
def energyPositiveAnnulus (n : ℕ) (ρ R : ℝ) : Set (GLEuclidean n) :=
  {x | ‖x‖ ∈ Ioc ρ R}

theorem measurableSet_energyPositiveAnnulus (n : ℕ) (ρ R : ℝ) :
    MeasurableSet (energyPositiveAnnulus n ρ R) := by
  unfold energyPositiveAnnulus
  exact measurableSet_Ioc.preimage measurable_norm

/-- Polar/Fubini integration on an actual Euclidean annulus, with the
ordinary radial Jacobian and an oriented interval integral. -/
theorem annulus_integral_eq_sphere_interval
    (n : ℕ) (hn : 1 ≤ n) (ρ R : ℝ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (h : GLEuclidean n → ℝ)
    (hPolarInt : Integrable
      (fun q : Metric.sphere (0 : GLEuclidean n) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean n) (R + 1)).indicator
          ((energyPositiveAnnulus n ρ R).indicator h)
          (unitSpherePolarPoint n q))
      ((unitSphereMeasure n).prod (unitSphereRadiusMeasure n))) :
    (∫ x in energyPositiveAnnulus n ρ R, h x) =
      ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (∫ r in ρ..R, r ^ (n - 1) * h (energySphereRay n ω r)
          ∂volume)
        ∂(unitSphereMeasure n) := by
  have hsub : energyPositiveAnnulus n ρ R ⊆
      Metric.ball (0 : GLEuclidean n) (R + 1) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hx.2
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hpoint (ω : Metric.sphere (0 : GLEuclidean n) 1)
      (r : Ioi (0 : ℝ)) :
      (Metric.ball (0 : GLEuclidean n) (R + 1)).indicator
        ((energyPositiveAnnulus n ρ R).indicator h)
        (unitSpherePolarPoint n (ω, r)) =
      (Ioc ρ R).indicator
        (fun t : ℝ => h (energySphereRay n ω t)) r.1 := by
    have hray : unitSpherePolarPoint n (ω, r) =
        energySphereRay n ω r.1 := rfl
    have hnorm : ‖unitSpherePolarPoint n (ω, r)‖ = r.1 := by
      rw [hray]
      exact energySphereRay_norm n ω r.1 r.2.le
    have hann : unitSpherePolarPoint n (ω, r) ∈
        energyPositiveAnnulus n ρ R ↔ r.1 ∈ Ioc ρ R := by
      simp [energyPositiveAnnulus, hnorm]
    by_cases hr : r.1 ∈ Ioc ρ R
    · have ha := hann.mpr hr
      have hb := hsub ha
      simp [Set.indicator, ha, hb, hr]
      exact congrArg h hray
    · have ha : unitSpherePolarPoint n (ω, r) ∉
          energyPositiveAnnulus n ρ R := fun h => hr (hann.mp h)
      simp [Set.indicator, ha, hr]
  have hpolar := ball_integral_eq_sphere_integral_radius_integral n hn
    (R + 1) ((energyPositiveAnnulus n ρ R).indicator h) hPolarInt
  calc
    (∫ x in energyPositiveAnnulus n ρ R, h x) =
        ∫ x in Metric.ball (0 : GLEuclidean n) (R + 1),
          (energyPositiveAnnulus n ρ R).indicator h x := by
      rw [setIntegral_indicator (measurableSet_energyPositiveAnnulus n ρ R),
        Set.inter_eq_right.mpr hsub]
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ∫ r : Ioi (0 : ℝ),
            (Metric.ball (0 : GLEuclidean n) (R + 1)).indicator
              ((energyPositiveAnnulus n ρ R).indicator h)
              (unitSpherePolarPoint n (ω, r))
            ∂(unitSphereRadiusMeasure n)
          ∂(unitSphereMeasure n) := hpolar
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ∫ r : Ioi (0 : ℝ),
            (Ioc ρ R).indicator
              (fun t : ℝ => h (energySphereRay n ω t)) r.1
            ∂(unitSphereRadiusMeasure n)
          ∂(unitSphereMeasure n) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      filter_upwards [] with r
      exact hpoint ω r
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          (∫ r in ρ..R, r ^ (n - 1) * h (energySphereRay n ω r)
            ∂volume)
          ∂(unitSphereMeasure n) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact radius_integral_annulus_eq_interval n ρ R hρ hρR
        (fun t => h (energySphereRay n ω t))

/-- The reduced density, expressed per unit Euclidean volume at nonzero
points.  Its apparent singularity is harmless on a positive annulus. -/
def energyReducedSpatialDensity (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) : ℝ :=
  radialReducedWeightedDensity m ‖x‖ (p ‖x‖) (‖z x‖ ^ 2)
    (euclideanGradientSq (m + 3) z x) / ‖x‖ ^ (m + 2)

/-- The actual spatial GL energy gap minus the proved reduced density
integrates over a Euclidean annulus to the angular integral of endpoint
fluxes.  The hypotheses are regularity, the local radial ODE, and genuine
integrability of the displayed densities, never the claimed identity. -/
theorem euclidean_annulus_energy_identity (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hp : ∀ r ∈ Set.uIcc ρ R, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ Set.uIcc ρ R, DifferentiableAt ℝ (deriv p) r)
    (hz : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ∀ r ∈ Set.uIcc ρ R,
        DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hode : ∀ r ∈ Set.uIcc ρ R,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
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
    _ = _ := energyRay_annulus_ibp m p z ω ρ R hρ hρR hp hp'
      (hz ω) hode (hfluxInt ω)

end

end BrezisOP6
