import BrezisOP6.WeakDilationBasics
import BrezisOP6.WeakBallEnergy

/-!
# Gradient-field scaling for inward dilation

This module scales a *candidate* weak gradient and its `L²` cost.  Its
identification as the distributional gradient of the scaled field is a
separate weak-chain-rule statement.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The gradient predicted by the weak chain rule for `w(a⁻¹ x)`. -/
def inwardGradient (n : ℕ) (a : ℝ)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) : GLEuclidean n →L[ℝ] GLEuclidean n :=
  a⁻¹ • G (a⁻¹ • x)

theorem weakGradientSq_inwardGradient (n : ℕ) (a : ℝ)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) :
    weakGradientSq n (inwardGradient n a G) x =
      (a⁻¹) ^ 2 * weakGradientSq n G (a⁻¹ • x) := by
  unfold weakGradientSq inwardGradient
  calc
    (∑ i : Fin n,
      ‖(a⁻¹ • G (a⁻¹ • x)) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) =
        ∑ i : Fin n,
          (a⁻¹) ^ 2 *
            ‖G (a⁻¹ • x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
      nlinarith [sq_abs (a⁻¹)]
    _ = (a⁻¹) ^ 2 *
          ∑ i : Fin n,
            ‖G (a⁻¹ • x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem inwardGradient_sq_integrable (n : ℕ) (a : ℝ) (ha : 0 < a)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (hG : Integrable (weakGradientSq n G) volume) :
    Integrable (weakGradientSq n (inwardGradient n a G)) volume := by
  have hcomp : Integrable
      (fun x => weakGradientSq n G (a⁻¹ • x)) volume :=
    hG.comp_smul (inv_ne_zero ha.ne')
  have hfun : weakGradientSq n (inwardGradient n a G) =
      fun x => (a⁻¹) ^ 2 * weakGradientSq n G (a⁻¹ • x) := by
    funext x
    exact weakGradientSq_inwardGradient n a G x
  rw [hfun]
  exact hcomp.const_mul ((a⁻¹) ^ 2)

theorem inwardGradient_sq_integral (n : ℕ) (a : ℝ) (ha : 0 < a)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) :
    (∫ x, weakGradientSq n (inwardGradient n a G) x) =
      (a⁻¹) ^ 2 * (a ^ n * ∫ x, weakGradientSq n G x) := by
  simp only [weakGradientSq_inwardGradient, integral_const_mul]
  congr 1
  simpa only [smul_eq_mul,
    show Module.finrank ℝ (GLEuclidean n) = n by simp] using
    (Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure (GLEuclidean n))
      (weakGradientSq n G) ha.le)

end

end BrezisOP6
