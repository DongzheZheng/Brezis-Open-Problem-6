import BrezisOP6.EnergyIBP

/-!
# Radial energy integration by parts with one-sided endpoint data

The finite-ball profile is supplied by the published radial-profile theorem
only up to the boundary radius.  Its ODE and second derivative are therefore
used on the *open* annulus.  The endpoint input for the fundamental theorem
of calculus is continuity of the boundary-flux function on the closed
annulus; no two-sided second derivative or ODE at the outer radius appears.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

/-- The pinned mathlib version has the almost-everywhere interval congruence
theorem.  This specialization discards the null outer endpoint. -/
theorem interval_integral_congr_interior
    {f g : ℝ → ℝ} {a b : ℝ}
    (h : Set.EqOn f g (uIoo a b)) :
    (∫ r in a..b, f r) = ∫ r in a..b, g r := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (max a b)] with r hrb hr
  have hr' : r ∈ Ioc (min a b) (max a b) := by
    simpa [uIoc] using hr
  have hrb' : r < max a b := by
    rcases lt_or_eq_of_le hr'.2 with hlt | heq
    · exact hlt
    · exact False.elim (hrb heq)
  exact h (by simpa [uIoo] using And.intro hr'.1 hrb')

/-- Closed-annulus continuity of the boundary flux follows from continuity
of the profile, its first derivative, and the raywise squared norm.  These
are the standard one-sided endpoint data supplied by a smooth finite-ball
profile and a smooth competitor. -/
theorem radialBoundaryFlux_continuousOn_of_profile_first
    (m : ℕ) (p s : ℝ → ℝ) (a b : ℝ)
    (hp : ContinuousOn p (uIcc a b))
    (hdp : ContinuousOn (deriv p) (uIcc a b))
    (hs : ContinuousOn s (uIcc a b)) :
    ContinuousOn (radialBoundaryFlux m p s) (uIcc a b) := by
  have hpow : ContinuousOn (fun r : ℝ => r ^ (m + 2))
      (uIcc a b) := (continuous_id.pow _).continuousOn
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ))
      (uIcc a b) := continuous_const.continuousOn
  simpa only [radialBoundaryFlux] using
    (((hpow.mul hp).mul hdp).mul (hs.sub hone))

/-- Radial integration by parts when the profile equation and the derivatives
are available only at interior points.  Endpoint behavior is recorded by
continuity of the explicit flux. -/
theorem radial_weighted_annulus_ibp_interior (m : ℕ)
    (p s q : ℝ → ℝ) (a b : ℝ)
    (hp : ∀ r ∈ uIoo a b, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ uIoo a b, DifferentiableAt ℝ (deriv p) r)
    (hs : ∀ r ∈ uIoo a b, DifferentiableAt ℝ s r)
    (hode : ∀ r ∈ uIoo a b,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxCont : ContinuousOn (radialBoundaryFlux m p s) (uIcc a b))
    (hfluxInt : IntervalIntegrable
      (deriv (radialBoundaryFlux m p s)) volume a b) :
    (∫ r in a..b,
      2 * (radialRawWeightedDensity m r (p r) (deriv p r)
          (s r) (deriv s r) (q r) -
        radialReducedWeightedDensity m r (p r) (s r) (q r))) =
      radialBoundaryFlux m p s b - radialBoundaryFlux m p s a := by
  have hfluxDiff : ∀ r ∈ uIoo a b,
      DifferentiableAt ℝ (radialBoundaryFlux m p s) r := by
    intro r hr
    exact (radialBoundaryFlux_hasDerivAt m p s r
      (deriv p r) (deriv (deriv p) r) (deriv s r)
      (hp r hr).hasDerivAt (hp' r hr).hasDerivAt
      (hs r hr).hasDerivAt).differentiableAt
  calc
    _ = ∫ r in a..b, deriv (radialBoundaryFlux m p s) r := by
      apply interval_integral_congr_interior
      intro r hr
      exact radial_weighted_energy_pointwise m p s q r
        (hp r hr) (hp' r hr) (hs r hr) (hode r hr)
    _ = radialBoundaryFlux m p s b - radialBoundaryFlux m p s a :=
      intervalIntegral.integral_deriv_eq_sub_uIoo
        hfluxCont hfluxDiff hfluxInt

end

end BrezisOP6
