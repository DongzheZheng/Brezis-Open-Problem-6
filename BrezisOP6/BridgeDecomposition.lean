import BrezisOP6.BallZeroModeFromOrigin

/-!
# Abstract angular decomposition for the finite-ball energy bridge

At each radius, the angular field is viewed in a real inner-product space.
The unit vector `e` represents the normalized constant spherical harmonic.
The scalars `c` and `dc` are its coefficients in the field and its radial
derivative.  Orthogonality and the angular spectral gap imply that the full
quadratic bridge density dominates its zero-mode density.

The last theorem integrates this inequality and accepts the exact radial
integration-by-parts identity as a separate analytic interface.  In the PDE
application this interface identifies the zero-mode density with the
`profilePiconeDensity` already controlled by `ball_zero_mode_nonnegative_from_origin_taylor`.
No existence of spherical means, differentiation under their integral, or
spherical Poincare theorem is asserted here.
-/

namespace BrezisOP6

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pythagoras for the coefficient of a unit constant mode. -/
theorem norm_sq_eq_mean_sq_add_orthogonal
    (e v : H) (c : ℝ) (he : ‖e‖ = 1)
    (hv : inner ℝ (v - c • e) e = 0) :
    ‖v‖ ^ 2 = c ^ 2 + ‖v - c • e‖ ^ 2 := by
  have hsplit : v = (v - c • e) + c • e := by abel
  rw [hsplit, norm_add_sq_real, real_inner_smul_right, hv]
  simp [norm_smul, he, Real.norm_eq_abs, sq_abs]
  ring

/-- The quadratic density in the bridge, with abstract angular Dirichlet
energy `angular`.  For a sphere, `H` is its real `L²` space and `angular`
is the integral of the squared spherical gradient. -/
def bridgeQuadraticDensity (m : ℕ) (d : ℝ → ℝ)
    (v dv : ℝ → H) (angular : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * d r * ‖dv r‖ ^ 2 +
    r ^ m * d r * (angular r - (m + 2 : ℝ) * ‖v r‖ ^ 2)

/-- The degree-zero contribution, before the substitution `c=b/r` and
its one-dimensional integration by parts. -/
def bridgeMeanDensity (m : ℕ) (d c dc : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * d r * (dc r) ^ 2 -
    (m + 2 : ℝ) * r ^ m * d r * (c r) ^ 2

/-- The mean-zero angular spectral gap leaves only nonnegative radial and
angular variances after the constant mode is separated. -/
theorem bridgeQuadraticDensity_sub_mean_nonneg
    (m : ℕ) (e v dv : H) (r d c dc angular : ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (he : ‖e‖ = 1)
    (hv : inner ℝ (v - c • e) e = 0)
    (hdv : inner ℝ (dv - dc • e) e = 0)
    (hgap : (m + 2 : ℝ) * ‖v - c • e‖ ^ 2 ≤ angular) :
    0 ≤ r ^ (m + 2) * d * ‖dv‖ ^ 2 +
        r ^ m * d * (angular - (m + 2 : ℝ) * ‖v‖ ^ 2) -
      (r ^ (m + 2) * d * dc ^ 2 -
        (m + 2 : ℝ) * r ^ m * d * c ^ 2) := by
  have hvnorm := norm_sq_eq_mean_sq_add_orthogonal e v c he hv
  have hdvnorm := norm_sq_eq_mean_sq_add_orthogonal e dv dc he hdv
  have hradial : 0 ≤ r ^ (m + 2) * d * ‖dv - dc • e‖ ^ 2 := by
    positivity
  have hang : 0 ≤ r ^ m * d *
      (angular - (m + 2 : ℝ) * ‖v - c • e‖ ^ 2) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg hr _) hd) (sub_nonneg.mpr hgap)
  have hid :
      r ^ (m + 2) * d * ‖dv‖ ^ 2 +
          r ^ m * d * (angular - (m + 2 : ℝ) * ‖v‖ ^ 2) -
        (r ^ (m + 2) * d * dc ^ 2 -
          (m + 2 : ℝ) * r ^ m * d * c ^ 2) =
      r ^ (m + 2) * d * ‖dv - dc • e‖ ^ 2 +
        r ^ m * d *
          (angular - (m + 2 : ℝ) * ‖v - c • e‖ ^ 2) := by
    rw [hvnorm, hdvnorm]
    ring
  rw [hid]
  exact add_nonneg hradial hang

/-- Integrating the slice decomposition transfers a zero-mode integral
estimate to the complete quadratic bridge.  The equality `hmeanPicone` is
the precise radial substitution and endpoint integration-by-parts interface;
it is not an assumption of the desired nonnegativity. -/
theorem bridgeQuadratic_nonnegative_of_zero_mode
    (m : ℕ) (e : H) (d : ℝ → ℝ) (v dv : ℝ → H)
    (angular c dc : ℝ → ℝ) (f F b db : ℝ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (he : ‖e‖ = 1)
    (hd : ∀ r ∈ Set.Icc 0 R, 0 ≤ d r)
    (hv : ∀ r ∈ Set.Icc 0 R,
      inner ℝ (v r - c r • e) e = 0)
    (hdv : ∀ r ∈ Set.Icc 0 R,
      inner ℝ (dv r - dc r • e) e = 0)
    (hgap : ∀ r ∈ Set.Icc 0 R,
      (m + 2 : ℝ) * ‖v r - c r • e‖ ^ 2 ≤ angular r)
    (hfullInt : IntervalIntegrable
      (bridgeQuadraticDensity m d v dv angular)
      MeasureTheory.volume 0 R)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m d c dc)
      MeasureTheory.volume 0 R)
    (hmeanPicone :
      (∫ r in (0 : ℝ)..R, bridgeMeanDensity m d c dc r) =
        ∫ r in (0 : ℝ)..R, profilePiconeDensity m f F b db r)
    (hzero : 0 ≤
      ∫ r in (0 : ℝ)..R, profilePiconeDensity m f F b db r) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeQuadraticDensity m d v dv angular r := by
  have hdiffInt := hfullInt.sub hmeanInt
  have hdiff : 0 ≤ ∫ r in (0 : ℝ)..R,
      (bridgeQuadraticDensity m d v dv angular r -
        bridgeMeanDensity m d c dc r) := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    simpa only [bridgeQuadraticDensity, bridgeMeanDensity] using
      bridgeQuadraticDensity_sub_mean_nonneg m e (v r) (dv r)
        r (d r) (c r) (dc r) (angular r) hr.1
        (hd r hr) he (hv r hr) (hdv r hr) (hgap r hr)
  rw [intervalIntegral.integral_sub hfullInt hmeanInt, hmeanPicone] at hdiff
  linarith

end

end BrezisOP6
