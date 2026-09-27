import BrezisOP6.EnergyVortexPointwise
import BrezisOP6.EnergyIBP
import BrezisOP6.EnergyOriginFlux
import BrezisOP6.SpherePolarIntegration

/-!
# The smooth annular energy identity along actual Euclidean rays

This file connects the concrete pointwise Ginzburg--Landau calculation to the
radial ODE integration by parts.  It works on every compact annulus inside
the positive-radius interval, so no global ODE assumption on a finite-ball
profile is introduced.  The radius-to-volume polar measure conversion and
the uniform angular origin trace are separate steps for a full ball theorem.
-/

namespace BrezisOP6

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-- A Euclidean ray based on an actual unit-sphere point. -/
def energySphereRay (n : ℕ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ) : GLEuclidean n :=
  r • (ω : GLEuclidean n)

/-- Squared norm of a vector field restricted to a ray. -/
def energyRaySq (n : ℕ) (z : GLEuclidean n → GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ) : ℝ :=
  ‖z (energySphereRay n ω r)‖ ^ 2

/-- Squared coordinate gradient of a vector field restricted to a ray. -/
def energyRayGradientSq (n : ℕ) (z : GLEuclidean n → GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ) : ℝ :=
  euclideanGradientSq n z (energySphereRay n ω r)

theorem energySphereRay_norm (n : ℕ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (r : ℝ) (hr : 0 ≤ r) : ‖energySphereRay n ω r‖ = r := by
  have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  simp [energySphereRay, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, hω]

theorem energySphereRay_hasDerivAt (n : ℕ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ) :
    HasDerivAt (energySphereRay n ω) (ω : GLEuclidean n) r := by
  simpa [energySphereRay] using
    (hasDerivAt_id r).smul_const (ω : GLEuclidean n)

theorem energyRaySq_hasDerivAt (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ)
    (hz : DifferentiableAt ℝ z (energySphereRay n ω r)) :
    HasDerivAt (energyRaySq n z ω)
      ((fderiv ℝ (fun y : GLEuclidean n => ‖z y‖ ^ 2)
        (energySphereRay n ω r)) (ω : GLEuclidean n)) r := by
  have hsq := hz.hasFDerivAt.norm_sq
  have h := hsq.comp_hasDerivAt r
    (energySphereRay_hasDerivAt n ω r)
  simpa only [energyRaySq, Function.comp_def,
    (hz.hasFDerivAt.norm_sq).fderiv] using h

theorem energyRaySq_deriv (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) (r : ℝ)
    (hz : DifferentiableAt ℝ z (energySphereRay n ω r)) :
    deriv (energyRaySq n z ω) r =
      (fderiv ℝ (fun y : GLEuclidean n => ‖z y‖ ^ 2)
        (energySphereRay n ω r)) (ω : GLEuclidean n) :=
  (energyRaySq_hasDerivAt n z ω r hz).deriv

/-- The pointwise density from `EnergyVortexPointwise` in ray coordinates,
with its radial derivative identified by the chain rule. -/
theorem energyRay_gap_eq_raw (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (r : ℝ) (hr : 0 < r)
    (hp : HasDerivAt p (deriv p r) r)
    (hz : DifferentiableAt ℝ z (energySphereRay (m + 3) ω r)) :
    r ^ (m + 2) *
      (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y)
          (energySphereRay (m + 3) ω r) -
        euclideanGLDensity (m + 3) (radialVortex (m + 3) p)
          (energySphereRay (m + 3) ω r)) =
      radialRawWeightedDensity m r (p r) (deriv p r)
        (energyRaySq (m + 3) z ω r)
        (deriv (energyRaySq (m + 3) z ω) r)
        (energyRayGradientSq (m + 3) z ω r) := by
  let x := energySphereRay (m + 3) ω r
  have hnorm : ‖x‖ = r := energySphereRay_norm (m + 3) ω r hr.le
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact ne_of_gt hr)
  have hdir : ‖x‖⁻¹ • x = (ω : GLEuclidean (m + 3)) := by
    rw [hnorm]
    simp [x, energySphereRay, smul_smul, inv_mul_cancel₀ (ne_of_gt hr)]
  have hgap := euclideanGLDensity_gap_eq_radialRaw m p z x
    (deriv p r) hx (by simpa [hnorm] using hp) hz
  have hds := energyRaySq_deriv (m + 3) z ω r hz
  rw [hdir, hnorm] at hgap
  rw [← hds] at hgap
  simpa only [x, energyRaySq, energyRayGradientSq] using hgap

/-- The exact annulus identity for the actual Euclidean GL energy density
on one sphere ray.  The only ODE and regularity requirements are local to
`[ρ,R]`; the right-hand side is an explicit endpoint flux. -/
theorem energyRay_annulus_ibp (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hp : ∀ r ∈ Set.uIcc ρ R, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ Set.uIcc ρ R, DifferentiableAt ℝ (deriv p) r)
    (hz : ∀ r ∈ Set.uIcc ρ R,
      DifferentiableAt ℝ z (energySphereRay (m + 3) ω r))
    (hode : ∀ r ∈ Set.uIcc ρ R,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
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
  have hs : ∀ r ∈ Set.uIcc ρ R,
      DifferentiableAt ℝ (energyRaySq (m + 3) z ω) r := by
    intro r hr
    exact (energyRaySq_hasDerivAt (m + 3) z ω r (hz r hr)).differentiableAt
  calc
    _ = ∫ r in ρ..R,
        2 * (radialRawWeightedDensity m r (p r) (deriv p r)
            (energyRaySq (m + 3) z ω r)
            (deriv (energyRaySq (m + 3) z ω) r)
            (energyRayGradientSq (m + 3) z ω r) -
          radialReducedWeightedDensity m r (p r)
            (energyRaySq (m + 3) z ω r)
            (energyRayGradientSq (m + 3) z ω r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Set.Icc ρ R := by
        simpa [Set.uIcc_of_le hρR] using hr
      have hrpos : 0 < r := lt_of_lt_of_le hρ hr'.1
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
    _ = _ := radial_weighted_annulus_ibp m p
      (energyRaySq (m + 3) z ω)
      (energyRayGradientSq (m + 3) z ω)
      ρ R hp hp' hs hode hfluxInt

end

end BrezisOP6
