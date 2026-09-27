import BrezisOP6.WeakBallEnergy
import BrezisOP6.EnergyC1Integrability

/-!
# The smooth-to-weak derivative bridge: product-rule reduction

For a smooth vector field and an interior scalar test, the weak derivative
identity reduces to one generic analytic fact: the integral of the
coordinate derivative of a compactly supported vector field is zero.
This module proves the product rule, the integrability of both tested
products, and the resulting integral algebra.  The remaining input is the
general compact-support derivative-integral theorem; it is displayed as a
premise rather than hidden in the weak-gradient definition.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- The concrete coordinate product rule behind distributional integration
by parts. -/
theorem classical_scalar_vector_test_product_rule
    (n : ℕ) (φ : GLEuclidean n → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (i : Fin n)
    (hφ : DifferentiableAt ℝ φ x)
    (hu : DifferentiableAt ℝ u x) :
    (fderiv ℝ (fun y => φ y • u y) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x +
        φ x • (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ)) := by
  rw [fderiv_fun_smul hφ hu]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  abel

/-- For a globally `C¹` map and test, both terms in the weak derivative
identity are Bochner integrable on the finite ball.  This discharges the
integrability half of `HasWeakGradientOnBall` independently of integration
by parts. -/
theorem classical_test_products_integrable
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u)
    (φ : GLEuclidean n → ℝ)
    (hφ : C1ScalarInteriorTest n R φ)
    (i : Fin n) :
    Integrable (fun x =>
      (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x)
      (weakBallMeasure n R) ∧
    Integrable (fun x =>
      φ x • (fderiv ℝ u x)
        (EuclideanSpace.single i (1 : ℝ)))
      (weakBallMeasure n R) := by
  have hφeval : Continuous (fun x : GLEuclidean n =>
      (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ))) := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using
      (hφ.1.continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
  have hueval : Continuous (fun x : GLEuclidean n =>
      (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using
      (hu.continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
  have hA : Continuous (fun x : GLEuclidean n =>
      (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x) :=
    hφeval.smul hu.continuous
  have hB : Continuous (fun x : GLEuclidean n =>
      φ x • (fderiv ℝ u x)
        (EuclideanSpace.single i (1 : ℝ))) :=
    hφ.1.continuous.smul hueval
  have hsubset : Metric.ball (0 : GLEuclidean n) R ⊆
      Metric.closedBall (0 : GLEuclidean n) R := by
    intro x hx
    exact Metric.ball_subset_closedBall hx
  constructor
  · change IntegrableOn _ (Metric.ball (0 : GLEuclidean n) R) volume
    exact (hA.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set hsubset
  · change IntegrableOn _ (Metric.ball (0 : GLEuclidean n) R) volume
    exact (hB.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set hsubset

/-- If the compactly supported product has zero integrated coordinate
derivative and both terms are integrable, then the actual classical
derivative satisfies the distributional weak-gradient identity. -/
theorem hasWeakGradientOnBall_of_test_product_derivative_zero
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u)
    (hDerivativeZero : ∀ (φ : GLEuclidean n → ℝ),
      C1ScalarInteriorTest n R φ → ∀ i : Fin n,
      (∫ x, (fderiv ℝ (fun y => φ y • u y) x)
        (EuclideanSpace.single i (1 : ℝ))
        ∂(weakBallMeasure n R)) = 0) :
    HasWeakGradientOnBall n R u (fderiv ℝ u) := by
  intro φ hφ i
  obtain ⟨hA, hB⟩ :=
    classical_test_products_integrable n R u hu φ hφ i
  refine ⟨hA, hB, ?_⟩
  have hpoint (x : GLEuclidean n) :
      (fderiv ℝ (fun y => φ y • u y) x)
          (EuclideanSpace.single i (1 : ℝ)) =
        (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x +
          φ x • (fderiv ℝ u x)
            (EuclideanSpace.single i (1 : ℝ)) :=
    classical_scalar_vector_test_product_rule n φ u x i
      (hφ.1.differentiable_one x) (hu.differentiable_one x)
  have hpointFun :
      (fun x => (fderiv ℝ (fun y => φ y • u y) x)
        (EuclideanSpace.single i (1 : ℝ))) =
      (fun x =>
        (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x +
          φ x • (fderiv ℝ u x)
            (EuclideanSpace.single i (1 : ℝ))) := by
    funext x
    exact hpoint x
  have hzero := hDerivativeZero φ hφ i
  rw [hpointFun, integral_add hA hB] at hzero
  exact (eq_neg_iff_add_eq_zero).2 hzero

/-- Every globally `C¹` field on a finite ball satisfies all measurability,
`L²`, `L⁴`, and classical-gradient `L²` requirements automatically.  The
only remaining condition for its canonical weak-gradient certificate is
the standard compact-support derivative-integral lemma. -/
def WeakH1L4BallField.ofGlobalC1_of_derivative_integral_zero
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hu : ContDiff ℝ 1 u)
    (hDerivativeZero : ∀ (φ : GLEuclidean n → ℝ),
      C1ScalarInteriorTest n R φ → ∀ i : Fin n,
      (∫ x, (fderiv ℝ (fun y => φ y • u y) x)
        (EuclideanSpace.single i (1 : ℝ))
        ∂(weakBallMeasure n R)) = 0) :
    WeakH1L4BallField n R := by
  have hclosedSubset : Metric.ball (0 : GLEuclidean n) R ⊆
      Metric.closedBall (0 : GLEuclidean n) R := by
    intro x hx
    exact Metric.ball_subset_closedBall hx
  have hcompact : IsCompact
      (Metric.closedBall (0 : GLEuclidean n) R) :=
    isCompact_closedBall _ _
  have huL2 : Integrable (fun x => ‖u x‖ ^ 2)
      (weakBallMeasure n R) := by
    change IntegrableOn (fun x => ‖u x‖ ^ 2)
      (Metric.ball (0 : GLEuclidean n) R) volume
    exact ((hu.continuous.continuousOn.norm.pow 2).integrableOn_compact
      hcompact).mono_set hclosedSubset
  have huL4 : Integrable (fun x => ‖u x‖ ^ 4)
      (weakBallMeasure n R) := by
    change IntegrableOn (fun x => ‖u x‖ ^ 4)
      (Metric.ball (0 : GLEuclidean n) R) volume
    exact ((hu.continuous.continuousOn.norm.pow 4).integrableOn_compact
      hcompact).mono_set hclosedSubset
  have hgradL2 : Integrable (euclideanGradientSq n u)
      (weakBallMeasure n R) := by
    change IntegrableOn (euclideanGradientSq n u)
      (Metric.ball (0 : GLEuclidean n) R) volume
    have hgradCont : ContinuousOn (euclideanGradientSq n u)
        (Metric.closedBall (0 : GLEuclidean n) R) :=
      euclideanGradientSq_continuousOn_of_fderiv n u _
        ((hu.continuous_fderiv (by norm_num)).continuousOn)
    exact (hgradCont.integrableOn_compact hcompact).mono_set
      hclosedSubset
  exact WeakH1L4BallField.ofClassical n R u
    hu.continuous.aestronglyMeasurable
    (hu.continuous_fderiv (by norm_num)).aestronglyMeasurable
    huL2 huL4 hgradL2
    (hasWeakGradientOnBall_of_test_product_derivative_zero
      n R u hu hDerivativeZero)

end

end BrezisOP6
