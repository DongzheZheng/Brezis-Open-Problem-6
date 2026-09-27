import Mathlib

/-!
# The nonzero spherical modes

The degree-`ℓ` spherical Laplacian eigenvalue is `ℓ(ℓ+n-2)`.  The algebraic
mode gap makes every `ℓ≥1` contribution in the comparison quadratic form
nonnegative whenever the profile contrast is nonnegative.  Completeness of
the spherical harmonic expansion is an external analytic input.
-/

namespace BrezisOP6

/-- The degree-one eigenvalue equals `n-1`. -/
theorem spherical_eigenvalue_one (n : ℕ) :
    (1 : ℝ) * (1 + (n : ℝ) - 2) = (n : ℝ) - 1 := by
  ring

/-- The angular eigenvalue gap for every nonzero mode in `n≥3`. -/
theorem spherical_eigenvalue_ge (n ell : ℕ) (hn : 3 ≤ n)
    (hell : 1 ≤ ell) :
    (n : ℝ) - 1 ≤ (ell : ℝ) * ((ell : ℝ) + (n : ℝ) - 2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hell' : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  nlinarith [mul_nonneg (sub_nonneg.mpr hell') (sub_nonneg.mpr hn')]

/-- The gap is strict from degree two onward. -/
theorem spherical_eigenvalue_gt (n ell : ℕ) (hn : 3 ≤ n)
    (hell : 2 ≤ ell) :
    (n : ℝ) - 1 < (ell : ℝ) * ((ell : ℝ) + (n : ℝ) - 2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  nlinarith [sq_nonneg ((ell : ℝ) - 2)]

/-- Pointwise nonnegativity of a nonzero angular mode's quadratic density. -/
theorem spherical_mode_density_nonneg
    (n ell : ℕ) (hn : 3 ≤ n) (hell : 1 ≤ ell)
    {r d a da : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    0 ≤ r ^ (n - 1) * d * da ^ 2 +
      ((ell : ℝ) * ((ell : ℝ) + (n : ℝ) - 2) - ((n : ℝ) - 1)) *
        r ^ (n - 3) * d * a ^ 2 := by
  have hgap := spherical_eigenvalue_ge n ell hn hell
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := hn
  have hcoeff : 0 ≤
      (ell : ℝ) * ((ell : ℝ) + (n : ℝ) - 2) - ((n : ℝ) - 1) :=
    sub_nonneg.mpr hgap
  have hfirst : 0 ≤ r ^ (n - 1) * d * da ^ 2 := by positivity
  have hsecond : 0 ≤
      ((ell : ℝ) * ((ell : ℝ) + (n : ℝ) - 2) - ((n : ℝ) - 1)) *
        r ^ (n - 3) * d * a ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hcoeff (le_of_lt (pow_pos hr _))) hd)
      (sq_nonneg a)
  linarith

end BrezisOP6
