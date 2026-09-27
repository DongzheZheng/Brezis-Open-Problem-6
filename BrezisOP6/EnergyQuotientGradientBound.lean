import BrezisOP6.EnergySmoothBallBridge

/-!
# A weighted gradient estimate for a possibly singular quotient field

The quotient `z=w/p(‖x‖)` need not be bounded at zero.  The correct
quantity in the energy identity is `p²|∇z|²`.  This file derives a
pointwise estimate for that quantity directly from the Fréchet product
rule, with no a priori regularity at the origin.
-/

namespace BrezisOP6

open MeasureTheory
open scoped Topology

noncomputable section

/-- Product differentiation and the elementary two-square inequality give
the quantitative bound needed to control the quotient gradient. -/
theorem weighted_gradient_le_product_gradient (n : ℕ)
    (p : ℝ → ℝ) (z : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hz : DifferentiableAt ℝ z x) :
    p ‖x‖ ^ 2 * euclideanGradientSq n z x ≤
      2 * euclideanGradientSq n (fun y => p ‖y‖ • z y) x +
        2 * dp ^ 2 * ‖z x‖ ^ 2 := by
  let q : GLEuclidean n → ℝ := fun y => p ‖y‖
  let u : GLEuclidean n → GLEuclidean n := fun y => q y • z y
  let e (i : Fin n) : GLEuclidean n := EuclideanSpace.single i 1
  have hproduct := radial_smul_fderiv n p z x hx hp.differentiableAt hz
  have hcoord (i : Fin n) :
      (fderiv ℝ u x) (e i) =
        p ‖x‖ • (fderiv ℝ z x) (e i) +
          ((fderiv ℝ q x) (e i)) • z x := by
    simpa only [u, q, e, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] using congrArg
        (fun A : GLEuclidean n →L[ℝ] GLEuclidean n => A (e i)) hproduct
  have hcoordBound (i : Fin n) :
      ‖p ‖x‖ • (fderiv ℝ z x) (e i)‖ ^ 2 ≤
        2 * ‖(fderiv ℝ u x) (e i)‖ ^ 2 +
          2 * ‖((fderiv ℝ q x) (e i)) • z x‖ ^ 2 := by
    let a := p ‖x‖ • (fderiv ℝ z x) (e i)
    let b := ((fderiv ℝ q x) (e i)) • z x
    let c := (fderiv ℝ u x) (e i)
    have hc : c = a + b := hcoord i
    have ha : a = c - b := by rw [hc]; abel
    have htri : ‖a‖ ≤ ‖c‖ + ‖b‖ := by
      rw [ha]
      exact norm_sub_le c b
    have hsq : ‖a‖ ^ 2 ≤ (‖c‖ + ‖b‖) ^ 2 := by
      nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
    have htwo : (‖c‖ + ‖b‖) ^ 2 ≤
        2 * ‖c‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c‖ - ‖b‖)]
    exact le_trans hsq htwo
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => hcoordBound i)
  have hleft :
      (∑ i : Fin n, ‖p ‖x‖ • (fderiv ℝ z x) (e i)‖ ^ 2) =
        p ‖x‖ ^ 2 * euclideanGradientSq n z x := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.mul_sum]
    rfl
  have hright :
      (∑ i : Fin n, ‖((fderiv ℝ q x) (e i)) • z x‖ ^ 2) =
        dp ^ 2 * ‖z x‖ ^ 2 := by
    have hradial := radialProfile_coordinate_sq_sum n p x dp hx hp
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.sum_mul]
    simpa only [q, e] using congrArg (fun t : ℝ => t * ‖z x‖ ^ 2) hradial
  rw [hleft] at hsum
  calc
    p ‖x‖ ^ 2 * euclideanGradientSq n z x ≤
        ∑ i : Fin n,
          (2 * ‖(fderiv ℝ u x) (e i)‖ ^ 2 +
            2 * ‖((fderiv ℝ q x) (e i)) • z x‖ ^ 2) := hsum
    _ = 2 * euclideanGradientSq n u x +
          2 * dp ^ 2 * ‖z x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hright]
      simp only [euclideanGradientSq, e, u, q]
      ring

/-- The concrete quotient of a differentiable numerator by a nonvanishing
radial profile is differentiable off the origin. -/
theorem energyQuotient_differentiableAt (n : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (hx : x ≠ 0)
    (hp : DifferentiableAt ℝ p ‖x‖) (hpx : p ‖x‖ ≠ 0)
    (hw : DifferentiableAt ℝ w x) :
    DifferentiableAt ℝ
      (fun y : GLEuclidean n => (p ‖y‖)⁻¹ • w y) x := by
  have hnorm : DifferentiableAt ℝ
      (fun y : GLEuclidean n => ‖y‖) x :=
    (differentiableAt_id (x := x)).norm ℝ hx
  have hradial : DifferentiableAt ℝ
      (fun y : GLEuclidean n => p ‖y‖) x := hp.comp x hnorm
  exact (hradial.inv hpx).smul hw

/-- At a point where the profile is nonzero, multiplication by the profile
recovers the actual smooth numerator, including its Fréchet derivative.
Consequently the weighted quotient gradient obeys the product estimate
with `|∇w|²` on the right. -/
theorem energyQuotient_weighted_gradient_le (n : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hpx : p ‖x‖ ≠ 0) (hw : DifferentiableAt ℝ w x) :
    p ‖x‖ ^ 2 * euclideanGradientSq n
        (fun y : GLEuclidean n => (p ‖y‖)⁻¹ • w y) x ≤
      2 * euclideanGradientSq n w x +
        2 * dp ^ 2 * (‖w x‖ ^ 2 / p ‖x‖ ^ 2) := by
  let z : GLEuclidean n → GLEuclidean n :=
    fun y => (p ‖y‖)⁻¹ • w y
  have hz := energyQuotient_differentiableAt n p w x hx
    hp.differentiableAt hpx hw
  have hradial : ContinuousAt (fun y : GLEuclidean n => p ‖y‖) x :=
    (hp.differentiableAt.comp x
      ((differentiableAt_id (x := x)).norm ℝ hx)).continuousAt
  have hevent : (fun y : GLEuclidean n => p ‖y‖ • z y) =ᶠ[𝓝 x] w := by
    filter_upwards [hradial.eventually_ne hpx] with y hy
    simp only [z, smul_smul]
    simp [hy]
  have hgrad : euclideanGradientSq n (fun y => p ‖y‖ • z y) x =
      euclideanGradientSq n w x := by
    unfold euclideanGradientSq
    rw [hevent.fderiv_eq]
  have hnorm : ‖z x‖ ^ 2 = ‖w x‖ ^ 2 / p ‖x‖ ^ 2 := by
    simp only [z, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hpx]
  have hbound := weighted_gradient_le_product_gradient n p z x dp
    hx hp hz
  simpa only [z, hgrad, hnorm] using hbound

/-- A positive-radius reciprocal-slope bound controls the apparent pole
of the concrete quotient.  This is the squared-norm estimate needed for
the `r⁻²` integrability argument. -/
theorem energyQuotient_norm_sq_le_inverse_square (n : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (Cratio Cw : ℝ)
    (hx : x ≠ 0) (hpx : p ‖x‖ ≠ 0)
    (hCratio : 0 ≤ Cratio) (hCw : 0 ≤ Cw)
    (hratio : |‖x‖ / p ‖x‖| ≤ Cratio)
    (hw : ‖w x‖ ≤ Cw) :
    ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 ≤
      Cratio ^ 2 * Cw ^ 2 * ‖x‖⁻¹ ^ 2 := by
  have hrne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hratioSq : (‖x‖ / p ‖x‖) ^ 2 ≤ Cratio ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hCratio] using hratio
  have hwSq : ‖w x‖ ^ 2 ≤ Cw ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hCw).2 hw
  have hbound :
      (‖x‖ / p ‖x‖) ^ 2 * ‖w x‖ ^ 2 * ‖x‖⁻¹ ^ 2 ≤
        Cratio ^ 2 * Cw ^ 2 * ‖x‖⁻¹ ^ 2 := by
    have hmul : (‖x‖ / p ‖x‖) ^ 2 * ‖w x‖ ^ 2 ≤
        Cratio ^ 2 * Cw ^ 2 := by
      calc
        _ ≤ Cratio ^ 2 * ‖w x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hratioSq (sq_nonneg _)
        _ ≤ Cratio ^ 2 * Cw ^ 2 :=
          mul_le_mul_of_nonneg_left hwSq (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right hmul (sq_nonneg _)
  have hidentity :
      ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 =
        (‖x‖ / p ‖x‖) ^ 2 * ‖w x‖ ^ 2 * ‖x‖⁻¹ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hrne, hpx]
  rw [hidentity]
  exact hbound

/-- The actual weighted quotient gradient is bounded by a constant plus
an inverse-square pole when the numerator has uniform `C¹` bounds and the
profile has its regular-origin derivative and reciprocal-slope bounds. -/
theorem energyQuotient_weighted_gradient_le_inverse_square (n : ℕ)
    (p : ℝ → ℝ) (w : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp Cdp Cratio Cw Cg : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hpx : p ‖x‖ ≠ 0) (hwDiff : DifferentiableAt ℝ w x)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCw : 0 ≤ Cw)
    (hdp : |dp| ≤ Cdp)
    (hratio : |‖x‖ / p ‖x‖| ≤ Cratio)
    (hw : ‖w x‖ ≤ Cw)
    (hgrad : euclideanGradientSq n w x ≤ Cg) :
    p ‖x‖ ^ 2 * euclideanGradientSq n
        (fun y : GLEuclidean n => (p ‖y‖)⁻¹ • w y) x ≤
      2 * Cg + 2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2 * ‖x‖⁻¹ ^ 2 := by
  have hmain := energyQuotient_weighted_gradient_le n p w x dp
    hx hp hpx hwDiff
  have hnorm := energyQuotient_norm_sq_le_inverse_square n p w x
    Cratio Cw hx hpx hCratio hCw hratio hw
  have hdpSq : dp ^ 2 ≤ Cdp ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hCdp] using hdp
  calc
    _ ≤ 2 * euclideanGradientSq n w x +
        2 * dp ^ 2 * (‖w x‖ ^ 2 / p ‖x‖ ^ 2) := hmain
    _ ≤ 2 * Cg +
        2 * Cdp ^ 2 * Cratio ^ 2 * Cw ^ 2 * ‖x‖⁻¹ ^ 2 := by
      have hnormEq : ‖w x‖ ^ 2 / p ‖x‖ ^ 2 =
          ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        field_simp [hpx]
      rw [hnormEq]
      have hnonneg : 0 ≤ ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 := sq_nonneg _
      have hmul1 : dp ^ 2 * ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 ≤
          Cdp ^ 2 * ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hdpSq hnonneg
      have hmul2 : Cdp ^ 2 * ‖(p ‖x‖)⁻¹ • w x‖ ^ 2 ≤
          Cdp ^ 2 * (Cratio ^ 2 * Cw ^ 2 * ‖x‖⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
      nlinarith [hmul1, hmul2]

end

end BrezisOP6
