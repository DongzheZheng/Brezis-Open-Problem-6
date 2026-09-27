import BrezisOP6.EnergyBallIdentity
import BrezisOP6.EnergyIBPInterior

/-!
# The Euclidean ray energy identity with interior radial ODE

At the outer radius of a finite ball, the radial profile is initially given
only with one-sided regularity.  The GL energy identity needs its ODE on the
open annulus and continuity of the boundary flux, so the boundary ODE is
unnecessary.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

/-- The raywise identity on a closed annulus, using differential inputs only
in its open interior. -/
theorem energyRay_annulus_ibp_interior (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hp : ∀ r ∈ uIoo ρ R, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ uIoo ρ R, DifferentiableAt ℝ (deriv p) r)
    (hz : ∀ r ∈ uIoo ρ R,
      DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hode : ∀ r ∈ uIoo ρ R,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ContinuousOn
      (radialBoundaryFlux m p (energyRaySq (m + 3) z ω))
      (uIcc ρ R))
    (hfluxInt : IntervalIntegrable
      (deriv (radialBoundaryFlux m p (energyRaySq (m + 3) z ω)))
      volume ρ R) :
    (∫ r in ρ..R,
      2 * (r ^ (m + 2) *
          (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y)
              (energySphereRay (m + 3) ω r) -
            euclideanGLDensity (m + 3) (radialVortex (m + 3) p)
              (energySphereRay (m + 3) ω r)) -
        radialReducedWeightedDensity m r (p r)
          (energyRaySq (m + 3) z ω r)
          (energyRayGradientSq (m + 3) z ω r))) =
      radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R -
        radialBoundaryFlux m p (energyRaySq (m + 3) z ω) ρ := by
  have hs : ∀ r ∈ uIoo ρ R,
      DifferentiableAt ℝ (energyRaySq (m + 3) z ω) r := by
    intro r hr
    exact (energyRaySq_hasDerivAt (m + 3) z ω r
      (hz r hr)).differentiableAt
  calc
    _ = ∫ r in ρ..R,
        2 * (radialRawWeightedDensity m r (p r) (deriv p r)
            (energyRaySq (m + 3) z ω r)
            (deriv (energyRaySq (m + 3) z ω) r)
            (energyRayGradientSq (m + 3) z ω r) -
          radialReducedWeightedDensity m r (p r)
            (energyRaySq (m + 3) z ω r)
            (energyRayGradientSq (m + 3) z ω r)) := by
      apply interval_integral_congr_interior
      intro r hr
      have hr' : r ∈ Ioo ρ R := by
        simpa [uIoo_of_le hρR] using hr
      have hrpos : 0 < r := lt_trans hρ hr'.1
      change 2 * (r ^ (m + 2) *
          (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y)
              (energySphereRay (m + 3) ω r) -
            euclideanGLDensity (m + 3) (radialVortex (m + 3) p)
              (energySphereRay (m + 3) ω r)) -
          radialReducedWeightedDensity m r (p r)
            (energyRaySq (m + 3) z ω r)
            (energyRayGradientSq (m + 3) z ω r)) = _
      rw [energyRay_gap_eq_raw m p z ω r hrpos
        (hp r hr).hasDerivAt (hz r hr)]
    _ = _ := radial_weighted_annulus_ibp_interior m p
      (energyRaySq (m + 3) z ω)
      (energyRayGradientSq (m + 3) z ω)
      ρ R hp hp' hs hode hfluxCont hfluxInt

end

end BrezisOP6
