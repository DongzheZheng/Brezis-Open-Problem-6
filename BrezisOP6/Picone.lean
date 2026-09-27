import Mathlib

/-!
# One-dimensional Picone transform

This module isolates the pointwise ground-state identity used by the radial
zero mode.  The multiplier `phi` is positive; `theta` records the flux
`h * phi'`.  Keeping `theta` as a separate function avoids assuming a second
derivative of `phi` in the statement.
-/

namespace BrezisOP6

/-- The Picone identity at one radius.  The residual is `q - theta' / phi`,
and the total derivative is the boundary flux.  Positivity of `h` is only
needed when this identity is turned into an inequality. -/
theorem picone_pointwise
    (h q phi theta b : ℝ → ℝ) (r dphi dtheta db : ℝ)
    (hphi : 0 < phi r)
    (hphi_deriv : HasDerivAt phi dphi r)
    (htheta_deriv : HasDerivAt theta dtheta r)
    (hb_deriv : HasDerivAt b db r)
    (htheta : theta r = h r * dphi) :
    h r * db ^ 2 + q r * b r ^ 2 =
      h r * phi r ^ 2 * (db / phi r - b r * dphi / phi r ^ 2) ^ 2
      + deriv (fun x => theta x / phi x * b x ^ 2) r
      + (q r - dtheta / phi r) * b r ^ 2 := by
  have hphi_ne : phi r ≠ 0 := ne_of_gt hphi
  have hflux : HasDerivAt (fun x => theta x / phi x * b x ^ 2)
      ((dtheta * phi r - theta r * dphi) / phi r ^ 2 * b r ^ 2
        + theta r / phi r * (2 * b r * db)) r := by
    convert ((htheta_deriv.div hphi_deriv hphi_ne).mul
      (hb_deriv.pow 2)) using 1
    simp only [Pi.pow_apply, Pi.div_apply]
    ring
  rw [hflux.deriv, htheta]
  field_simp [hphi_ne]
  ring

/-- If the Picone residual is nonnegative, the local quadratic density
dominates the derivative of its boundary flux. -/
theorem picone_pointwise_nonneg
    (h q phi theta b : ℝ → ℝ) (r dphi dtheta db : ℝ)
    (hh : 0 < h r) (hphi : 0 < phi r)
    (hphi_deriv : HasDerivAt phi dphi r)
    (htheta_deriv : HasDerivAt theta dtheta r)
    (hb_deriv : HasDerivAt b db r)
    (htheta : theta r = h r * dphi)
    (hres : 0 ≤ q r - dtheta / phi r) :
    deriv (fun x => theta x / phi x * b x ^ 2) r
      ≤ h r * db ^ 2 + q r * b r ^ 2 := by
  rw [picone_pointwise h q phi theta b r dphi dtheta db hphi
    hphi_deriv htheta_deriv hb_deriv htheta]
  have hsq : 0 ≤ h r * phi r ^ 2 *
      (db / phi r - b r * dphi / phi r ^ 2) ^ 2 := by
    positivity
  nlinarith [mul_nonneg hres (sq_nonneg (b r))]

/-- The Picone identity integrated over a compact interval.  All three
integrability assumptions are explicit: the theorem can therefore be applied
to a regularized interval `[δ,R]` before taking the singular endpoint limit.
The source paper's endpoint bounds are a separate analytic obligation. -/
theorem picone_interval
    (h q phi theta b dphi dtheta db : ℝ → ℝ) (a R : ℝ)
    (hphi : ∀ x ∈ Set.uIcc a R, 0 < phi x)
    (hphi_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt phi (dphi x) x)
    (htheta_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt theta (dtheta x) x)
    (hb_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt b (db x) x)
    (htheta : ∀ x ∈ Set.uIcc a R, theta x = h x * dphi x)
    (hsq_int : IntervalIntegrable
      (fun x => h x * phi x ^ 2 *
        (db x / phi x - b x * dphi x / phi x ^ 2) ^ 2)
      MeasureTheory.volume a R)
    (hflux_int : IntervalIntegrable
      (deriv fun x => theta x / phi x * b x ^ 2)
      MeasureTheory.volume a R)
    (hres_int : IntervalIntegrable
      (fun x => (q x - dtheta x / phi x) * b x ^ 2)
      MeasureTheory.volume a R) :
    (∫ x in a..R, h x * db x ^ 2 + q x * b x ^ 2) =
      (∫ x in a..R, h x * phi x ^ 2 *
        (db x / phi x - b x * dphi x / phi x ^ 2) ^ 2)
      + (theta R / phi R * b R ^ 2 - theta a / phi a * b a ^ 2)
      + (∫ x in a..R, (q x - dtheta x / phi x) * b x ^ 2) := by
  let flux : ℝ → ℝ := fun x => theta x / phi x * b x ^ 2
  let square : ℝ → ℝ := fun x => h x * phi x ^ 2 *
    (db x / phi x - b x * dphi x / phi x ^ 2) ^ 2
  let residual : ℝ → ℝ := fun x => (q x - dtheta x / phi x) * b x ^ 2
  have hflux_diff : ∀ x ∈ Set.uIcc a R, DifferentiableAt ℝ flux x := by
    intro x hx
    exact (((htheta_deriv x hx).div (hphi_deriv x hx)
      (ne_of_gt (hphi x hx))).mul ((hb_deriv x hx).pow 2)).differentiableAt
  have hpoint : Set.EqOn
      (fun x => h x * db x ^ 2 + q x * b x ^ 2)
      (fun x => square x + deriv flux x + residual x)
      (Set.uIcc a R) := by
    intro x hx
    exact picone_pointwise h q phi theta b x (dphi x) (dtheta x) (db x)
      (hphi x hx) (hphi_deriv x hx) (htheta_deriv x hx)
      (hb_deriv x hx) (htheta x hx)
  calc
    (∫ x in a..R, h x * db x ^ 2 + q x * b x ^ 2) =
        ∫ x in a..R, square x + deriv flux x + residual x :=
      intervalIntegral.integral_congr hpoint
    _ = (∫ x in a..R, square x)
          + (flux R - flux a)
          + (∫ x in a..R, residual x) := by
      rw [intervalIntegral.integral_add (hsq_int.add hflux_int) hres_int,
        intervalIntegral.integral_add hsq_int hflux_int,
        intervalIntegral.integral_deriv_eq_sub hflux_diff hflux_int]
    _ = _ := rfl

/-- On an ordered compact interval, positive weight and nonnegative residual
give the integrated ground-state lower bound. -/
theorem picone_interval_nonneg
    (h q phi theta b dphi dtheta db : ℝ → ℝ) (a R : ℝ)
    (haR : a ≤ R)
    (hh : ∀ x ∈ Set.uIcc a R, 0 < h x)
    (hphi : ∀ x ∈ Set.uIcc a R, 0 < phi x)
    (hphi_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt phi (dphi x) x)
    (htheta_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt theta (dtheta x) x)
    (hb_deriv : ∀ x ∈ Set.uIcc a R, HasDerivAt b (db x) x)
    (htheta : ∀ x ∈ Set.uIcc a R, theta x = h x * dphi x)
    (hres : ∀ x ∈ Set.uIcc a R, 0 ≤ q x - dtheta x / phi x)
    (hsq_int : IntervalIntegrable
      (fun x => h x * phi x ^ 2 *
        (db x / phi x - b x * dphi x / phi x ^ 2) ^ 2)
      MeasureTheory.volume a R)
    (hflux_int : IntervalIntegrable
      (deriv fun x => theta x / phi x * b x ^ 2)
      MeasureTheory.volume a R)
    (hres_int : IntervalIntegrable
      (fun x => (q x - dtheta x / phi x) * b x ^ 2)
      MeasureTheory.volume a R) :
    theta R / phi R * b R ^ 2 - theta a / phi a * b a ^ 2
      ≤ ∫ x in a..R, h x * db x ^ 2 + q x * b x ^ 2 := by
  have hsq_nonneg :
      0 ≤ ∫ x in a..R, h x * phi x ^ 2 *
        (db x / phi x - b x * dphi x / phi x ^ 2) ^ 2 := by
    apply intervalIntegral.integral_nonneg haR
    intro x hx
    have hxU : x ∈ Set.uIcc a R := by
      simpa [Set.uIcc_of_le haR] using hx
    have hweight : 0 < h x := hh x hxU
    positivity
  have hres_nonneg :
      0 ≤ ∫ x in a..R, (q x - dtheta x / phi x) * b x ^ 2 := by
    apply intervalIntegral.integral_nonneg haR
    intro x hx
    have hxU : x ∈ Set.uIcc a R := by
      simpa [Set.uIcc_of_le haR] using hx
    exact mul_nonneg (hres x hxU) (sq_nonneg (b x))
  have hident := picone_interval h q phi theta b dphi dtheta db a R
    hphi hphi_deriv htheta_deriv hb_deriv htheta
    hsq_int hflux_int hres_int
  linarith

end BrezisOP6
