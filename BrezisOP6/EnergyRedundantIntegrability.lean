import BrezisOP6.EnergyOpenBall

/-!
# Integrability consequences inside the single-profile identity

The spatial gap and single-profile densities do not require independent
integrability hypotheses once their three concrete GL/reduced components
are integrable.  This module records those direct consequences so the
analytic interface can be shortened without changing its meaning.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The gap density is integrable whenever the two actual GL densities
and the reduced density are integrable on the punctured ball. -/
theorem energySpatialGapDensity_integrableOn_of_components (m : ℕ)
    (R : ℝ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : IntegrableOn
      (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hv : IntegrableOn
      (euclideanGLDensity (m + 3) (radialVortex (m + 3) p))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hred : IntegrableOn (energyReducedSpatialDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume) :
    IntegrableOn (energySpatialGapDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume := by
  unfold energySpatialGapDensity
  exact ((hu.sub hv).sub hred).const_mul 2

/-- The bridge's single-profile density is the already integrable
reduced density almost everywhere, since the origin has been removed.
The null-boundary conversion gives the ordinary open ball. -/
theorem singleProfileDensity_integrableOn_ball_of_reduced (m : ℕ)
    (R : ℝ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hred : IntegrableOn (energyReducedSpatialDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume) :
    Integrable
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
  have hsingle : IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (energyPositiveClosedBall (m + 3) R) volume := by
    apply hred.congr_fun
    · intro x hx
      have hx0 : x ≠ 0 := by
        intro hzero
        subst x
        simp [energyPositiveClosedBall] at hx
      exact energyReducedSpatialDensity_eq_singleProfileDensity
        m p z x hx0
    · exact measurableSet_energyPositiveClosedBall (m + 3) R
  rw [← energyPositiveClosedBall_restrict_eq_ball m R]
  exact hsingle

end

end BrezisOP6
