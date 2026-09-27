import BrezisOP6.EnergySpatialInterface
import Mathlib

/-!
# The pointwise Euclidean energy calculation on the punctured ball

The radial vortex is represented as `(p(r)/r) • x` for `r=‖x‖`.  This file
derives its actual coordinate-gradient square and identifies the expanded
Ginzburg--Landau energy difference with `radialRawWeightedDensity` from
`EnergyIBP`.  No integration or boundary condition is used.
-/

namespace BrezisOP6

open scoped RealInnerProductSpace

noncomputable section

/-- The radial vortex `p(r)e_r`, defined algebraically also at the origin. -/
def radialVortex (n : ℕ) (p : ℝ → ℝ)
    (x : GLEuclidean n) : GLEuclidean n :=
  (p ‖x‖ / ‖x‖) • x

/-- The pointwise Ginzburg--Landau energy density with the actual coordinate
gradient. -/
def euclideanGLDensity (n : ℕ)
    (u : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n) : ℝ :=
  euclideanGradientSq n u x / 2 + (1 - ‖u x‖ ^ 2) ^ 2 / 4

/-- The squared gradient of the identity map is the dimension. -/
theorem euclideanGradientSq_id (n : ℕ) (x : GLEuclidean n) :
    euclideanGradientSq n id x = (n : ℝ) := by
  unfold euclideanGradientSq
  simp [fderiv_id]

/-- The radial derivative of `‖x‖²` in the unit radial direction is `2‖x‖`. -/
theorem normSq_radial_fderiv_apply (n : ℕ)
    (x : GLEuclidean n) (hx : x ≠ 0) :
    (fderiv ℝ (fun y : GLEuclidean n => ‖y‖ ^ 2) x)
      (‖x‖⁻¹ • x) = 2 * ‖x‖ := by
  have h := vectorNormSq_fderiv_apply n id x (‖x‖⁻¹ • x)
    (differentiableAt_id (x := x))
  have h' :
      (fderiv ℝ (fun y : GLEuclidean n => ‖y‖ ^ 2) x)
        (‖x‖⁻¹ • x) = 2 * inner ℝ (‖x‖⁻¹ • x) x := by
    simpa only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] using h
  rw [h', real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hrne]

/-- The baseline vortex has `|∇(p e_r)|² = p'²+(n-1)p²/r²` away from the
origin.  This is derived from the general scalar-vector product rule by
applying it to the radial scalar `q(r)=p(r)/r` and `z(x)=x`. -/
theorem euclideanGradientSq_radialVortex (n : ℕ)
    (p : ℝ → ℝ) (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖) :
    euclideanGradientSq n (radialVortex n p) x =
      dp ^ 2 + ((n : ℝ) - 1) * (p ‖x‖) ^ 2 / ‖x‖ ^ 2 := by
  let q : ℝ → ℝ := fun r => p r / r
  let dq : ℝ := (dp * ‖x‖ - p ‖x‖) / ‖x‖ ^ 2
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hq : HasDerivAt q dq ‖x‖ := by
    simpa [q, dq] using hp.div (hasDerivAt_id ‖x‖) hrne
  have hgradient := euclideanGradientSq_radial_exact n q id x dq hx hq
    (differentiableAt_id (x := x))
  have hid : euclideanGradientSq n id x = (n : ℝ) :=
    euclideanGradientSq_id n x
  have hradial := normSq_radial_fderiv_apply n x hx
  change euclideanGradientSq n (radialVortex n p) x = _
  calc
    euclideanGradientSq n (radialVortex n p) x =
        (q ‖x‖) ^ 2 * (n : ℝ) + dq ^ 2 * ‖x‖ ^ 2 +
          q ‖x‖ * dq * (2 * ‖x‖) := by
      simpa only [radialVortex, q, id_eq, hid, hradial] using hgradient
    _ = dp ^ 2 + ((n : ℝ) - 1) * (p ‖x‖) ^ 2 / ‖x‖ ^ 2 := by
      dsimp [q, dq]
      field_simp [hrne]
      ring

/-- The vortex has the intended norm `|p(r)e_r|²=p(r)²` off the origin. -/
theorem radialVortex_norm_sq (n : ℕ)
    (p : ℝ → ℝ) (x : GLEuclidean n) (hx : x ≠ 0) :
    ‖radialVortex n p x‖ ^ 2 = (p ‖x‖) ^ 2 := by
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold radialVortex
  rw [norm_smul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs]
  field_simp [hrne]

/-- The actual pointwise energy gap, with radial Jacobian, is precisely
the unreduced density used in the ODE integration-by-parts calculation. -/
theorem euclideanGLDensity_gap_eq_radialRaw (m : ℕ)
    (p : ℝ → ℝ) (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hz : DifferentiableAt ℝ z x) :
    ‖x‖ ^ (m + 2) *
      (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
        euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x) =
      radialRawWeightedDensity m ‖x‖ (p ‖x‖) dp (‖z x‖ ^ 2)
        ((fderiv ℝ (fun y : GLEuclidean (m + 3) => ‖z y‖ ^ 2) x)
          (‖x‖⁻¹ • x))
        (euclideanGradientSq (m + 3) z x) := by
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hprod := euclideanGradientSq_radial_exact (m + 3) p z x dp hx hp hz
  have hvortex := euclideanGradientSq_radialVortex (m + 3) p x dp hx hp
  have hnormProd : ‖p ‖x‖ • z x‖ ^ 2 =
      (p ‖x‖) ^ 2 * ‖z x‖ ^ 2 := by
    rw [norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  have hnormVortex := radialVortex_norm_sq (m + 3) p x hx
  have hpow : ‖x‖ ^ (m + 2) = ‖x‖ ^ m * ‖x‖ ^ 2 := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  unfold euclideanGLDensity radialRawWeightedDensity
  rw [hprod, hvortex, hnormProd, hnormVortex, hpow]
  push_cast
  field_simp [hrne]
  ring

end

end BrezisOP6
