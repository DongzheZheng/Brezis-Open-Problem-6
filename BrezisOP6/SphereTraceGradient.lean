import BrezisOP6.SphereGradientDecomposition
import BrezisOP6.SphereVectorBridge

/-!
# The gradient of a scaled spherical trace

The angular term of the bridge is the actual tangential derivative of the
ambient competitor on each Euclidean sphere.  The scalar chain rule first
gives the factor `r²`; the coordinate projections of a differentiable vector
field then identify the finite target-coordinate sum with the Euclidean
vector norm.  No angular-gradient identity is assumed as an input.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- The angular energy integrand of the scaled trace `ω ↦ g(rω)` is `r²`
times the squared ambient tangential derivatives at `rω`. -/
theorem sphereAngularIntegrand_scaled (n : ℕ)
    (g : GLEuclidean n → ℝ) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) :
    ‖fderiv ℝ (fun y : GLEuclidean n => g (r • y))
        (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2 =
      r ^ 2 * ∑ i : Fin n,
        ((fderiv ℝ g (r • (ω : GLEuclidean n)))
          (EuclideanSpace.single i (1 : ℝ) -
            ((ω : GLEuclidean n) i) • (ω : GLEuclidean n))) ^ 2 := by
  rw [sphereAngularIntegrand_eq_tangent_sq n
    (fun y : GLEuclidean n => g (r • y)) ω]
  have hchain :
      fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n) =
        r • fderiv ℝ g (r • (ω : GLEuclidean n)) := by
    simpa only using
      (fderiv_comp_smul (f := g) (x := (ω : GLEuclidean n)) r)
  rw [hchain]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

/-- Projection onto one target coordinate commutes with the actual Fréchet
derivative of a differentiable Euclidean vector field. -/
theorem sphereVectorCoord_fderiv_apply (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (x h : GLEuclidean n)
    (k : Fin n) (hz : DifferentiableAt ℝ z x) :
    (fderiv ℝ (fun y : GLEuclidean n => (z y) k) x) h =
      ((fderiv ℝ z x) h) k := by
  have hcomp :
      fderiv ℝ (fun y : GLEuclidean n => (z y) k) x =
        (EuclideanSpace.proj k).comp (fderiv ℝ z x) := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj k).hasFDerivAt.comp x hz.hasFDerivAt).fderiv
  rw [hcomp]
  rfl

/-- The ordinary radial derivative of the actual ambient vector field is
its Fréchet derivative applied to the unit radial direction. -/
theorem vectorSphereRay_hasDerivAt (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    HasDerivAt (fun s : ℝ => z (s • (ω : GLEuclidean n)))
      ((fderiv ℝ z (r • (ω : GLEuclidean n)))
        (ω : GLEuclidean n)) r := by
  have hray : HasDerivAt
      (fun s : ℝ => s • (ω : GLEuclidean n))
      (ω : GLEuclidean n) r := by
    simpa using
      (hasDerivAt_id r).smul_const (ω : GLEuclidean n)
  exact hz.hasFDerivAt.comp_hasDerivAt r hray

/-- In the exact polar gradient identity the radial square is the square
of an ordinary one-variable derivative, provided the ambient vector field
is differentiable at the ray point. -/
theorem euclideanGradientSq_eq_ray_deriv_add_tangent (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    euclideanGradientSq n z (r • (ω : GLEuclidean n)) =
      ‖deriv (fun s : ℝ => z (s • (ω : GLEuclidean n))) r‖ ^ 2 +
        euclideanTangentialGradientSq n z
          (r • (ω : GLEuclidean n)) ω := by
  rw [euclideanGradientSq_eq_radial_add_tangent]
  rw [(vectorSphereRay_hasDerivAt n z r ω hz).deriv]

/-- The independent geometric tangential gradient of a vector field is
the sum of the scalar tangential gradients of its target coordinates. -/
theorem euclideanTangentialGradientSq_eq_coordinate_sum (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hz : DifferentiableAt ℝ z x) :
    euclideanTangentialGradientSq n z x ω =
      ∑ k : Fin n, ∑ i : Fin n,
        ((fderiv ℝ (fun y : GLEuclidean n => (z y) k) x)
          (EuclideanSpace.single i (1 : ℝ) -
            ((ω : GLEuclidean n) i) • (ω : GLEuclidean n))) ^ 2 := by
  have hnormsq (v : GLEuclidean n) :
      ‖v‖ ^ 2 = ∑ k : Fin n, (v k) ^ 2 := by
    calc
      ‖v‖ ^ 2 = ∑ k : Fin n,
          inner ℝ v ((EuclideanSpace.basisFun (Fin n) ℝ) k) ^ 2 :=
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left v).symm
      _ = ∑ k : Fin n, (v k) ^ 2 := by
        simp only [EuclideanSpace.inner_basisFun_real]
  unfold euclideanTangentialGradientSq
  simp_rw [hnormsq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [sphereVectorCoord_fderiv_apply n z x
    (EuclideanSpace.single i (1 : ℝ) -
      ((ω : GLEuclidean n) i) • (ω : GLEuclidean n)) k hz]

/-- The target-coordinate sum of the angular energy integrands of the
scaled vector trace is exactly `r²` times the ambient tangential gradient
square at `rω`. -/
theorem vectorScaledSphereAngularIntegrand_eq_tangent (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    (∑ k : Fin n,
      (‖fderiv ℝ
          (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ
          (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2)) =
      r ^ 2 * euclideanTangentialGradientSq n z
        (r • (ω : GLEuclidean n)) ω := by
  calc
    _ = ∑ k : Fin n, r ^ 2 *
        (∑ i : Fin n,
          ((fderiv ℝ (fun x : GLEuclidean n => (z x) k)
              (r • (ω : GLEuclidean n)))
            (EuclideanSpace.single i (1 : ℝ) -
              ((ω : GLEuclidean n) i) • (ω : GLEuclidean n))) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k _
          exact sphereAngularIntegrand_scaled n
            (fun x : GLEuclidean n => (z x) k) r ω
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (euclideanTangentialGradientSq_eq_coordinate_sum
        n z (r • (ω : GLEuclidean n)) ω hz).symm

/-- At a positive or negative radius alike, the coordinate-gradient
energy of the actual ambient field splits into a radial ray derivative and
the angular energy integrand of its scaled spherical trace. -/
theorem euclideanGradientSq_scaled_trace_pointwise (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    r ^ 2 * euclideanGradientSq n z
      (r • (ω : GLEuclidean n)) =
      r ^ 2 *
        ‖deriv (fun s : ℝ => z (s • (ω : GLEuclidean n))) r‖ ^ 2 +
        ∑ k : Fin n,
          (‖fderiv ℝ
              (fun y : GLEuclidean n => (z (r • y)) k)
              (ω : GLEuclidean n)‖ ^ 2 -
            ((fderiv ℝ
              (fun y : GLEuclidean n => (z (r • y)) k)
              (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2) := by
  rw [euclideanGradientSq_eq_ray_deriv_add_tangent n z r ω hz]
  rw [vectorScaledSphereAngularIntegrand_eq_tangent n z r ω hz]
  ring

/-- The same identity after integration over the actual polar surface
measure.  Integrability of each scalar angular density is stated explicitly
so that finite-sum/integral interchange has its usual analytic hypothesis. -/
theorem vectorSphereAngularEnergy_scaled_eq_tangent_integral (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n) (r : ℝ)
    (hz : ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
      DifferentiableAt ℝ z (r • (ω : GLEuclidean n)))
    (hInt : ∀ k : Fin n,
      Integrable (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        ‖fderiv ℝ
          (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)‖ ^ 2 -
          ((fderiv ℝ
            (fun y : GLEuclidean n => (z (r • y)) k)
            (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2)
        (unitSphereMeasure n)) :
    vectorSphereAngularEnergy n (fun y => z (r • y)) =
      r ^ 2 * ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        euclideanTangentialGradientSq n z
          (r • (ω : GLEuclidean n)) ω ∂(unitSphereMeasure n) := by
  let F : Fin n → Metric.sphere (0 : GLEuclidean n) 1 → ℝ :=
    fun k ω =>
      ‖fderiv ℝ (fun y : GLEuclidean n => (z (r • y)) k)
        (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ (fun y : GLEuclidean n => (z (r • y)) k)
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2
  change (∑ k : Fin n, ∫ ω, F k ω ∂(unitSphereMeasure n)) = _
  calc
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        (∑ k : Fin n, F k ω) ∂(unitSphereMeasure n) := by
          rw [integral_finset_sum]
          intro k _
          exact hInt k
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        r ^ 2 * euclideanTangentialGradientSq n z
          (r • (ω : GLEuclidean n)) ω ∂(unitSphereMeasure n) := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact vectorScaledSphereAngularIntegrand_eq_tangent
            n z r ω (hz ω)
    _ = _ := by rw [integral_const_mul]

/-- `C¹` regularity makes the concrete spherical angular density
integrable: the unit sphere is compact, and both the derivative and its
normal evaluation are continuous. -/
theorem sphereAngularIntegrand_integrable (n : ℕ)
    (g : GLEuclidean n → ℝ) (hg : ContDiff ℝ 1 g) :
    Integrable (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      ‖fderiv ℝ g (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ g (ω : GLEuclidean n))
          (ω : GLEuclidean n)) ^ 2)
      (unitSphereMeasure n) := by
  have hF : Continuous (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      fderiv ℝ g (ω : GLEuclidean n)) :=
    (hg.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  have hnormal : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (fderiv ℝ g (ω : GLEuclidean n))
          (ω : GLEuclidean n)) :=
    hF.clm_apply continuous_subtype_val
  have hcont : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        ‖fderiv ℝ g (ω : GLEuclidean n)‖ ^ 2 -
          ((fderiv ℝ g (ω : GLEuclidean n))
            (ω : GLEuclidean n)) ^ 2) :=
    (hF.norm.pow 2).sub (hnormal.pow 2)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- For a `C¹` vector field, the spherical integrability and
differentiability hypotheses of the preceding polar-gradient identity
follow from regularity of the ambient field. -/
theorem vectorSphereAngularEnergy_scaled_eq_tangent_integral_of_contDiff
    (n : ℕ) (z : GLEuclidean n → GLEuclidean n)
    (r : ℝ) (hz : ContDiff ℝ 1 z) :
    vectorSphereAngularEnergy n (fun y => z (r • y)) =
      r ^ 2 * ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        euclideanTangentialGradientSq n z
          (r • (ω : GLEuclidean n)) ω ∂(unitSphereMeasure n) := by
  apply vectorSphereAngularEnergy_scaled_eq_tangent_integral n z r
  · intro ω
    exact hz.differentiable_one _
  · intro k
    have hScaled : ContDiff ℝ 1
        (fun y : GLEuclidean n => (z (r • y)) k) := by
      simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k).contDiff.comp
          (hz.comp (contDiff_const_smul r))
    exact sphereAngularIntegrand_integrable n _ hScaled

end

end BrezisOP6
