import BrezisOP6.FlowFromProfiles
import Mathlib

/-!
# The differential and radial integration-by-parts part of the energy identity

Here `m + 3` is the spatial dimension.  The first definitions use the actual
Fréchet derivative of a map on Euclidean space and Lebesgue measure on a ball.
The later lemmas prove the radial divergence calculation underlying (2.5):
the weighted difference of the unreduced and reduced densities is the
derivative of an explicit boundary flux.  The annulus lemma is a genuine
one-dimensional integration by parts, with differentiability and
integrability stated explicitly.

Spherical polar integration, the vector-valued angular gradient expansion,
and the uniform-in-angle trace estimate needed to pass from annuli to a ball
are not asserted here.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The Euclidean domain and target for an `n`-component Ginzburg--Landau map. -/
abbrev GLEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The coordinate expression for the squared Hilbert--Schmidt norm of the
actual Fréchet derivative. -/
def euclideanGradientSq (n : ℕ) (u : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) : ℝ :=
  ∑ i : Fin n, ‖(fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2

/-- The actual Ginzburg--Landau energy on an open Euclidean ball. -/
def euclideanBallEnergy (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n) : ℝ :=
  ∫ x, euclideanGradientSq n u x / 2 + (1 - ‖u x‖ ^ 2) ^ 2 / 4
    ∂(volume.restrict (Metric.ball (0 : GLEuclidean n) R))

/-- The Fréchet product rule for the radial scalar profile times a vector
field, at a nonzero spatial point. -/
theorem radial_smul_fderiv (n : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n)
    (hx : x ≠ 0) (hp : DifferentiableAt ℝ p ‖x‖)
    (hz : DifferentiableAt ℝ z x) :
    fderiv ℝ (fun y : GLEuclidean n => p ‖y‖ • z y) x =
      p ‖x‖ • fderiv ℝ z x +
        (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x).smulRight (z x) := by
  have hnorm : DifferentiableAt ℝ (fun y : GLEuclidean n => ‖y‖) x :=
    (differentiableAt_id (x := x)).norm ℝ hx
  have hradial : DifferentiableAt ℝ
      (fun y : GLEuclidean n => p ‖y‖) x := hp.comp x hnorm
  exact fderiv_fun_smul hradial hz

/-- The radial product rule specialized to the concrete squared gradient. -/
theorem euclideanGradientSq_radial_smul (n : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n)
    (hx : x ≠ 0) (hp : DifferentiableAt ℝ p ‖x‖)
    (hz : DifferentiableAt ℝ z x) :
    euclideanGradientSq n (fun y => p ‖y‖ • z y) x =
      ∑ i : Fin n,
        ‖(p ‖x‖ • fderiv ℝ z x +
            (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x).smulRight (z x))
              (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  unfold euclideanGradientSq
  rw [radial_smul_fderiv n p z x hx hp hz]

/-- The weighted raw density after expanding `∇(p z)` and subtracting the
energy of the radial vortex.  Here `s=|z|²`, `ds=∂ᵣs`, and `q=|∇z|²`.
The factors `r^(m+2)` are the radial Jacobian for dimension `m+3`. -/
def radialRawWeightedDensity (m : ℕ)
    (r p dp s ds q : ℝ) : ℝ :=
  (r ^ (m + 2) * (p ^ 2 * q + dp ^ 2 * (s - 1) + p * dp * ds) -
      ((m : ℝ) + 2) * r ^ m * p ^ 2) / 2 +
    r ^ (m + 2) * ((1 - p ^ 2 * s) ^ 2 - (1 - p ^ 2) ^ 2) / 4

/-- The right-hand density of (2.5), with its radial Jacobian included. -/
def radialReducedWeightedDensity (m : ℕ) (r p s q : ℝ) : ℝ :=
  (r ^ (m + 2) * p ^ 2 * q -
      ((m : ℝ) + 2) * r ^ m * p ^ 2 * s) / 2 +
    r ^ (m + 2) * p ^ 4 * (s - 1) ^ 2 / 4

/-- The radial boundary flux before multiplication by the sphere area
measure; it is well defined wherever `p` is differentiable. -/
def radialBoundaryFlux (m : ℕ) (p s : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * p r * deriv p r * (s r - 1)

/-- Algebraic cancellation of the linear potential term by the radial ODE.
This is the pointwise heart of the integration-by-parts identity. -/
theorem radial_weighted_density_algebra (m : ℕ)
    (r p dp ddp s ds q : ℝ)
    (hode : radialODEAt ((m : ℝ) + 3) r p dp ddp) :
    2 * (radialRawWeightedDensity m r p dp s ds q -
      radialReducedWeightedDensity m r p s q) =
      ((m : ℝ) + 2) * r ^ (m + 1) * p * dp * (s - 1) +
        r ^ (m + 2) *
          (dp ^ 2 * (s - 1) + p * ddp * (s - 1) + p * dp * ds) := by
  have hode' : r ^ 2 * ddp + ((m : ℝ) + 2) * r * dp -
      ((m : ℝ) + 2) * p + r ^ 2 * (1 - p ^ 2) * p = 0 := by
    unfold radialODEAt at hode
    nlinarith [hode]
  have hode_mul : r ^ m * p * (s - 1) *
      (r ^ 2 * ddp + ((m : ℝ) + 2) * r * dp -
        ((m : ℝ) + 2) * p + r ^ 2 * (1 - p ^ 2) * p) = 0 := by
    rw [hode']
    ring
  have hpow1 : r ^ (m + 1) = r ^ m * r := by
    rw [pow_succ]
  have hpow2 : r ^ (m + 2) = r ^ m * r ^ 2 := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  unfold radialRawWeightedDensity radialReducedWeightedDensity
  rw [hpow1, hpow2]
  linear_combination -hode_mul

/-- The boundary flux has the expected derivative, with no ODE needed. -/
theorem radialBoundaryFlux_hasDerivAt (m : ℕ) (p s : ℝ → ℝ)
    (r dp ddp ds : ℝ)
    (hp : HasDerivAt p dp r)
    (hp' : HasDerivAt (deriv p) ddp r)
    (hs : HasDerivAt s ds r) :
    HasDerivAt (radialBoundaryFlux m p s)
      (((m : ℝ) + 2) * r ^ (m + 1) * p r * dp * (s r - 1) +
        r ^ (m + 2) *
          (dp ^ 2 * (s r - 1) + p r * ddp * (s r - 1) + p r * dp * ds)) r := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ (m + 2))
      (((m : ℝ) + 2) * r ^ (m + 1)) r := by
    simpa [show m + 2 - 1 = m + 1 by omega] using
      (hasDerivAt_pow (m + 2) r)
  have hflux := ((hpow.mul hp).mul hp').mul (hs.sub_const 1)
  convert hflux using 1
  simp only [Pi.mul_apply, hp.deriv]
  ring

/-- On the punctured radial axis, the ODE turns the raw energy density
minus the reduced density into one half of an actual derivative. -/
theorem radial_weighted_energy_pointwise (m : ℕ) (p s q : ℝ → ℝ)
    (r : ℝ)
    (hp : DifferentiableAt ℝ p r)
    (hp' : DifferentiableAt ℝ (deriv p) r)
    (hs : DifferentiableAt ℝ s r)
    (hode : radialODEAt ((m : ℝ) + 3) r
      (p r) (deriv p r) (deriv (deriv p) r)) :
    2 * (radialRawWeightedDensity m r (p r) (deriv p r)
        (s r) (deriv s r) (q r) -
      radialReducedWeightedDensity m r (p r) (s r) (q r)) =
        deriv (radialBoundaryFlux m p s) r := by
  have hflux := radialBoundaryFlux_hasDerivAt m p s r
    (deriv p r) (deriv (deriv p) r) (deriv s r)
    hp.hasDerivAt hp'.hasDerivAt hs.hasDerivAt
  rw [hflux.deriv]
  exact radial_weighted_density_algebra m r (p r) (deriv p r)
    (deriv (deriv p) r) (s r) (deriv s r) (q r) hode

/-- Integration by parts on a radial annulus.  The profile ODE is needed
only on the interval of integration; there is no whole-axis assumption. -/
theorem radial_weighted_annulus_ibp (m : ℕ)
    (p s q : ℝ → ℝ) (a b : ℝ)
    (hp : ∀ r ∈ Set.uIcc a b, DifferentiableAt ℝ p r)
    (hp' : ∀ r ∈ Set.uIcc a b, DifferentiableAt ℝ (deriv p) r)
    (hs : ∀ r ∈ Set.uIcc a b, DifferentiableAt ℝ s r)
    (hode : ∀ r ∈ Set.uIcc a b,
      radialODEAt ((m : ℝ) + 3) r
        (p r) (deriv p r) (deriv (deriv p) r))
    (hfluxInt : IntervalIntegrable (deriv (radialBoundaryFlux m p s))
      volume a b) :
    (∫ r in a..b,
      2 * (radialRawWeightedDensity m r (p r) (deriv p r)
          (s r) (deriv s r) (q r) -
        radialReducedWeightedDensity m r (p r) (s r) (q r))) =
      radialBoundaryFlux m p s b - radialBoundaryFlux m p s a := by
  calc
    _ = ∫ r in a..b, deriv (radialBoundaryFlux m p s) r := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact radial_weighted_energy_pointwise m p s q r
        (hp r hr) (hp' r hr) (hs r hr) (hode r hr)
    _ = radialBoundaryFlux m p s b - radialBoundaryFlux m p s a :=
      intervalIntegral.integral_deriv_eq_sub
        (fun r hr => (radialBoundaryFlux_hasDerivAt m p s r
          (deriv p r) (deriv (deriv p) r) (deriv s r)
          (hp r hr).hasDerivAt (hp' r hr).hasDerivAt
          (hs r hr).hasDerivAt).differentiableAt)
        hfluxInt

end

end BrezisOP6
