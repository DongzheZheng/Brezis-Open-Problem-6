import BrezisOP6.EnergyIBP
import Mathlib

/-!
# Spatial energy algebra for the Euclidean energy identity

The algebra below expands the actual coordinate gradient of `p(‖x‖)z(x)`.
The two scalar equalities needed to identify its radial terms are kept
separate: they concern the coordinate derivative of `p(‖x‖)` and the radial
derivative of `‖z‖²`.
-/

namespace BrezisOP6

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-- A concrete Fréchet derivative of the Euclidean norm away from zero,
obtained from the derivative of the squared norm and the square root. -/
theorem euclideanNorm_hasFDerivAt (n : ℕ)
    (x : GLEuclidean n) (hx : x ≠ 0) :
    HasFDerivAt (fun y : GLEuclidean n => ‖y‖)
      ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
  have hxnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt hxnorm)

/-- The radial profile derivative evaluated in an arbitrary spatial
direction. -/
theorem radialProfile_fderiv_apply (n : ℕ) (p : ℝ → ℝ)
    (x h : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖) :
    (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x) h =
      dp * inner ℝ x h / ‖x‖ := by
  have hnorm := euclideanNorm_hasFDerivAt n x hx
  have hcomp := hp.comp_hasFDerivAt x hnorm
  have hderiv : fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x =
      dp • ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  rw [hderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hxnorm]
  ring

/-- The sum of squared coordinate derivatives of a radial profile is
exactly the square of its one-dimensional derivative. -/
theorem radialProfile_coordinate_sq_sum (n : ℕ) (p : ℝ → ℝ)
    (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖) :
    (∑ i : Fin n,
      ((fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
        (EuclideanSpace.single i (1 : ℝ))) ^ 2) = dp ^ 2 := by
  have hcoord (i : Fin n) :
      (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
          (EuclideanSpace.single i (1 : ℝ)) =
        dp * x i / ‖x‖ := by
    rw [radialProfile_fderiv_apply n p x
      (EuclideanSpace.single i (1 : ℝ)) dp hx hp]
    have hi := EuclideanSpace.inner_basisFun_real (ι := Fin n) x i
    rw [EuclideanSpace.basisFun_apply] at hi
    rw [hi]
  have hsum : (∑ i : Fin n, (x i) ^ 2) = ‖x‖ ^ 2 := by
    calc
      (∑ i : Fin n, (x i) ^ 2) =
          ∑ i : Fin n,
            inner ℝ x ((EuclideanSpace.basisFun (Fin n) ℝ) i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [EuclideanSpace.inner_basisFun_real]
      _ = ‖x‖ ^ 2 :=
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left x
  simp_rw [hcoord]
  have heach (i : Fin n) : (dp * x i / ‖x‖) ^ 2 =
      (dp ^ 2 / ‖x‖ ^ 2) * (x i) ^ 2 := by ring
  simp_rw [heach]
  rw [← Finset.mul_sum, hsum]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hxnorm]

/-- The coordinate cross term is the directional derivative of `z` in the
radial direction, expressed through the standard Euclidean basis. -/
theorem radialProfile_coordinate_cross_sum (n : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖) :
    2 * (∑ i : Fin n,
      ((fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
          (EuclideanSpace.single i (1 : ℝ))) *
        inner ℝ ((fderiv ℝ z x) (EuclideanSpace.single i (1 : ℝ))) (z x)) =
      dp * (2 * inner ℝ
        ((fderiv ℝ z x) (‖x‖⁻¹ • x)) (z x)) := by
  let A := fderiv ℝ z x
  have hcoord (i : Fin n) :
      (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
          (EuclideanSpace.single i (1 : ℝ)) =
        dp * x i / ‖x‖ := by
    rw [radialProfile_fderiv_apply n p x
      (EuclideanSpace.single i (1 : ℝ)) dp hx hp]
    have hi := EuclideanSpace.inner_basisFun_real (ι := Fin n) x i
    rw [EuclideanSpace.basisFun_apply] at hi
    rw [hi]
  have hrepr :
      (∑ i : Fin n, (x i) • EuclideanSpace.single i (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x)
  have hsumA :
      (∑ i : Fin n, (x i) • A (EuclideanSpace.single i (1 : ℝ))) = A x := by
    calc
      _ = A (∑ i : Fin n,
          (x i) • EuclideanSpace.single i (1 : ℝ)) := by
            simp only [map_sum, map_smul]
      _ = A x := by rw [hrepr]
  have hsumInner :
      (∑ i : Fin n,
        x i * inner ℝ (A (EuclideanSpace.single i (1 : ℝ))) (z x)) =
          inner ℝ (A x) (z x) := by
    calc
      _ = ∑ i : Fin n,
          inner ℝ ((x i) • A (EuclideanSpace.single i (1 : ℝ))) (z x) := by
            simp only [real_inner_smul_left]
      _ = inner ℝ
          (∑ i : Fin n, (x i) • A (EuclideanSpace.single i (1 : ℝ)))
          (z x) := by rw [sum_inner]
      _ = inner ℝ (A x) (z x) := by rw [hsumA]
  simp_rw [hcoord]
  have hterm (i : Fin n) :
      (dp * x i / ‖x‖) *
          inner ℝ (A (EuclideanSpace.single i (1 : ℝ))) (z x) =
        (dp / ‖x‖) *
          (x i * inner ℝ (A (EuclideanSpace.single i (1 : ℝ))) (z x)) := by ring
  change 2 * (∑ i : Fin n,
    (dp * x i / ‖x‖) *
      inner ℝ (A (EuclideanSpace.single i (1 : ℝ))) (z x)) =
    dp * (2 * inner ℝ (A (‖x‖⁻¹ • x)) (z x))
  simp_rw [hterm]
  rw [← Finset.mul_sum, hsumInner]
  simp only [map_smul, real_inner_smul_left]
  dsimp [A]
  ring

/-- Quadratic expansion of a sum of two vectors in a real Hilbert space. -/
theorem norm_real_smul_add_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (u z : E) :
    ‖a • u + b • z‖ ^ 2 =
      a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖z‖ ^ 2 +
        2 * a * b * inner ℝ u z := by
  rw [norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Coordinatewise expansion of the squared gradient after a scalar-vector
product rule. -/
theorem sum_norm_real_smul_add_sq (n : ℕ)
    (a : ℝ) (b : Fin n → ℝ)
    (u : Fin n → GLEuclidean n) (z : GLEuclidean n) :
    (∑ i : Fin n, ‖a • u i + b i • z‖ ^ 2) =
      a ^ 2 * (∑ i : Fin n, ‖u i‖ ^ 2) +
        (∑ i : Fin n, (b i) ^ 2) * ‖z‖ ^ 2 +
          a * (2 * ∑ i : Fin n, b i * inner ℝ (u i) z) := by
  simp_rw [norm_real_smul_add_sq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  have hcross :
      (∑ i : Fin n, 2 * a * b i * inner ℝ (u i) z) =
        a * (2 * ∑ i : Fin n, b i * inner ℝ (u i) z) := by
    simp_rw [show ∀ i : Fin n,
      2 * a * b i * inner ℝ (u i) z =
        (2 * a) * (b i * inner ℝ (u i) z) from by
          intro i
          ring]
    rw [← Finset.mul_sum]
    ring
  rw [hcross]

/-- The exact expansion of the concrete Euclidean squared gradient.  The
two scalar hypotheses are the radial chain-rule and `∂ᵣ‖z‖²` identities in
coordinate form, not an energy or integral identity. -/
theorem euclideanGradientSq_radial_expansion (n : ℕ)
    (p : ℝ → ℝ) (z : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp ds : ℝ)
    (hx : x ≠ 0) (hp : DifferentiableAt ℝ p ‖x‖)
    (hz : DifferentiableAt ℝ z x)
    (hRadialNorm :
      (∑ i : Fin n,
        ((fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
          (EuclideanSpace.single i (1 : ℝ))) ^ 2) = dp ^ 2)
    (hRadialCross :
      2 * (∑ i : Fin n,
        ((fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
            (EuclideanSpace.single i (1 : ℝ))) *
          inner ℝ ((fderiv ℝ z x) (EuclideanSpace.single i (1 : ℝ))) (z x)) =
        dp * ds) :
    euclideanGradientSq n (fun y => p ‖y‖ • z y) x =
      (p ‖x‖) ^ 2 * euclideanGradientSq n z x +
        dp ^ 2 * ‖z x‖ ^ 2 + p ‖x‖ * dp * ds := by
  rw [euclideanGradientSq_radial_smul n p z x hx hp hz]
  simp_rw [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [sum_norm_real_smul_add_sq n (p ‖x‖)
    (fun i => (fderiv ℝ (fun y : GLEuclidean n => p ‖y‖) x)
      (EuclideanSpace.single i (1 : ℝ)))
    (fun i => (fderiv ℝ z x) (EuclideanSpace.single i (1 : ℝ))) (z x)]
  rw [hRadialNorm, hRadialCross]
  simp only [euclideanGradientSq]
  ring

/-- The Fréchet derivative of the squared norm of a vector field, evaluated
in any spatial direction. -/
theorem vectorNormSq_fderiv_apply (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (x h : GLEuclidean n) (hz : DifferentiableAt ℝ z x) :
    (fderiv ℝ (fun y : GLEuclidean n => ‖z y‖ ^ 2) x) h =
      2 * inner ℝ ((fderiv ℝ z x) h) (z x) := by
  rw [(hz.hasFDerivAt.norm_sq).fderiv]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  rw [real_inner_comm]
  simp only [nsmul_eq_mul]
  norm_num

/-- The full pointwise spatial-gradient expansion for a smooth radial
profile, with no scalar cross-term hypotheses. -/
theorem euclideanGradientSq_radial_exact (n : ℕ)
    (p : ℝ → ℝ) (z : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (dp : ℝ)
    (hx : x ≠ 0) (hp : HasDerivAt p dp ‖x‖)
    (hz : DifferentiableAt ℝ z x) :
    euclideanGradientSq n (fun y => p ‖y‖ • z y) x =
      (p ‖x‖) ^ 2 * euclideanGradientSq n z x +
        dp ^ 2 * ‖z x‖ ^ 2 + p ‖x‖ * dp *
          ((fderiv ℝ (fun y : GLEuclidean n => ‖z y‖ ^ 2) x)
            (‖x‖⁻¹ • x)) := by
  apply euclideanGradientSq_radial_expansion n p z x dp
    ((fderiv ℝ (fun y : GLEuclidean n => ‖z y‖ ^ 2) x)
      (‖x‖⁻¹ • x)) hx hp.differentiableAt hz
  · exact radialProfile_coordinate_sq_sum n p x dp hx hp
  · rw [vectorNormSq_fderiv_apply n z x (‖x‖⁻¹ • x) hz]
    exact radialProfile_coordinate_cross_sum n p z x dp hx hp

/-- The theorem-valued published minimality input specialized to the
actual Euclidean-ball Ginzburg--Landau energy.  `admissible R w` represents
the published compact-support or `H₀¹ ∩ L⁴` perturbation class. -/
structure EuclideanVortexBallMinimality (n : ℕ)
    (V : GLEuclidean n → GLEuclidean n)
    (admissible : ℝ → (GLEuclidean n → GLEuclidean n) → Prop) : Prop where
  energy_le : ∀ (R : ℝ) (_hR : 0 < R)
    (w : GLEuclidean n → GLEuclidean n), admissible R w →
      euclideanBallEnergy n R V ≤
        euclideanBallEnergy n R (fun x => V x + w x)

end

end BrezisOP6
