import BrezisOP6.SphereTraceGradient
import BrezisOP6.SphereRadialL2FiniteBall

/-!
# Angular energy of a field smooth only on a punctured finite ball

The actual quotient field in the finite-ball comparison need not be `C¹`
at the origin or outside the ball.  At a fixed interior radius its scaled
spherical trace has a continuous tangential derivative.  Compactness of the
unit sphere then supplies angular integrability without a global extension
assumption.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

private theorem ray_mem_puncturedBall (n : ℕ) (R r : ℝ)
    (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (hr : r ∈ Ioo (0 : ℝ) R) :
    r • (ω : GLEuclidean n) ∈
      {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} := by
  have hω : ‖(ω : GLEuclidean n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hnorm : ‖r • (ω : GLEuclidean n)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hω]
    ring
  change 0 < ‖r • (ω : GLEuclidean n)‖ ∧
    ‖r • (ω : GLEuclidean n)‖ < R
  rw [hnorm]
  exact hr

/-- The angular density of the scaled trace is integrable at every
interior positive radius when the ambient scalar field is `C¹` only on
the punctured ball. -/
theorem sphereAngularIntegrand_scaled_integrable_of_contDiffOn
    (n : ℕ) (R r : ℝ) (g : GLEuclidean n → ℝ)
    (hg : ContDiffOn ℝ 1 g {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hr : r ∈ Ioo (0 : ℝ) R) :
    Integrable (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
      ‖fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n)‖ ^ 2 -
        ((fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2)
      (unitSphereMeasure n) := by
  let U : Set (GLEuclidean n) := {x | 0 < ‖x‖ ∧ ‖x‖ < R}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hRay : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        r • (ω : GLEuclidean n)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have hF : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        fderiv ℝ g (r • (ω : GLEuclidean n))) :=
    (hg.continuousOn_fderiv_of_isOpen hopen (by norm_num)).comp_continuous
      hRay (fun ω => ray_mem_puncturedBall n R r ω hr)
  have hScaled : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n)) := by
    have heq :
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          fderiv ℝ (fun y : GLEuclidean n => g (r • y))
            (ω : GLEuclidean n)) =
        (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
          r • fderiv ℝ g (r • (ω : GLEuclidean n))) := by
      funext ω
      exact fderiv_comp_smul (f := g) (x := (ω : GLEuclidean n)) r
    rw [heq]
    exact (continuous_const_smul r).comp hF
  have hnormal : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        (fderiv ℝ (fun y : GLEuclidean n => g (r • y))
          (ω : GLEuclidean n)) (ω : GLEuclidean n)) :=
    hScaled.clm_apply continuous_subtype_val
  have hcont : Continuous
      (fun ω : Metric.sphere (0 : GLEuclidean n) 1 =>
        ‖fderiv ℝ (fun y : GLEuclidean n => g (r • y))
            (ω : GLEuclidean n)‖ ^ 2 -
          ((fderiv ℝ (fun y : GLEuclidean n => g (r • y))
            (ω : GLEuclidean n)) (ω : GLEuclidean n)) ^ 2) :=
    (hScaled.norm.pow 2).sub (hnormal.pow 2)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The punctured-`C¹` hypothesis supplies every coordinate's angular
integrability and the actual tangential energy identity on an interior
sphere. -/
theorem vectorSphereAngularEnergy_scaled_eq_tangent_integral_of_contDiffOn
    (n : ℕ) (R r : ℝ)
    (z : GLEuclidean n → GLEuclidean n)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hr : r ∈ Ioo (0 : ℝ) R) :
    vectorSphereAngularEnergy n (fun y => z (r • y)) =
      r ^ 2 * ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
        euclideanTangentialGradientSq n z
          (r • (ω : GLEuclidean n)) ω ∂(unitSphereMeasure n) := by
  apply vectorSphereAngularEnergy_scaled_eq_tangent_integral n z r
  · intro ω
    have hopen : IsOpen
        {x : GLEuclidean n | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact hz.differentiableOn_one |>.differentiableAt
      (hopen.mem_nhds (ray_mem_puncturedBall n R r ω hr))
  · intro k
    have hk : ContDiffOn ℝ 1
        (fun x : GLEuclidean n => (z x) k)
        {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
      simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
    exact sphereAngularIntegrand_scaled_integrable_of_contDiffOn
      n R r (fun x => (z x) k) hk hr

end

end BrezisOP6
