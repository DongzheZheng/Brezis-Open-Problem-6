import BrezisOP6.SphereBridgeSpatialDensity
import BrezisOP6.SphereTraceGradient

/-!
# Coordinate summation and the actual spatial bridge

For a vector field on a punctured ball the sum of all target-coordinate
spherical bridge integrands is exactly the radial Jacobian times the
Euclidean quadratic bridge integrand.  This provides the geometric link
from the proved Hilbert-space bridge to the density in the energy comparison.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

/-- Pointwise target-coordinate sum of the genuine sphere bridge. -/
def vectorSphereBridgePointwise (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ) (ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1) : ℝ :=
  ∑ k : Fin (m + 3),
    scalarSphereBridgePointwise m f F
      (fun s y => (z (s • y)) k) r ω

/-- The actual quadratic bridge density per unit Euclidean volume away
from the origin.  Its radial factor is the squared profile contrast. -/
def euclideanQuadraticBridgeDensity (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) : ℝ :=
  (f ‖x‖ ^ 2 - F ‖x‖ ^ 2) *
    (euclideanGradientSq (m + 3) z x -
      (m + 2 : ℝ) * ‖z x‖ ^ 2 / ‖x‖ ^ 2)

/-- The squared Euclidean norm of a vector is the sum of the squares of
its target coordinates. -/
theorem sphereVector_norm_sq_eq_sum_coords (n : ℕ)
    (v : GLEuclidean n) :
    ‖v‖ ^ 2 = ∑ k : Fin n, (v k) ^ 2 := by
  calc
    ‖v‖ ^ 2 = ∑ k : Fin n,
        inner ℝ v ((EuclideanSpace.basisFun (Fin n) ℝ) k) ^ 2 :=
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_left v).symm
    _ = ∑ k : Fin n, (v k) ^ 2 := by
      simp only [EuclideanSpace.inner_basisFun_real]

/-- Taking a target coordinate commutes with the radial derivative of a
differentiable vector field. -/
theorem sphereRay_coord_deriv (n : ℕ)
    (z : GLEuclidean n → GLEuclidean n)
    (r : ℝ) (ω : Metric.sphere (0 : GLEuclidean n) 1)
    (k : Fin n)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean n))) :
    deriv (fun s : ℝ => (z (s • (ω : GLEuclidean n))) k) r =
      (deriv (fun s : ℝ => z (s • (ω : GLEuclidean n))) r) k := by
  have hvec := vectorSphereRay_hasDerivAt n z r ω hz
  have hcoord := (EuclideanSpace.proj k).hasFDerivAt.comp_hasDerivAt r hvec
  have hc := hcoord.deriv
  simp only [Function.comp_def, EuclideanSpace.coe_proj] at hc
  exact hc.trans (congrArg (fun u : GLEuclidean n => u k) hvec.deriv.symm)

/-- At any regular polar point the target-coordinate sphere bridge is the
Jacobian-weighted actual Euclidean gradient bridge.  The formula is written
without inverse powers of `r`; multiplying by `r^(m+2)` gives the usual
spatial density on the positive radius axis. -/
theorem vectorSphereBridgePointwise_eq_spatial (m : ℕ)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ) (ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean (m + 3)))) :
    vectorSphereBridgePointwise m f F z r ω =
      r ^ m * (f r ^ 2 - F r ^ 2) *
        (r ^ 2 * euclideanGradientSq (m + 3) z
            (r • (ω : GLEuclidean (m + 3))) -
          (m + 2 : ℝ) *
            ‖z (r • (ω : GLEuclidean (m + 3)))‖ ^ 2) := by
  let E := GLEuclidean (m + 3)
  let x : E := r • (ω : E)
  let d : ℝ := f r ^ 2 - F r ^ 2
  let v : E := deriv (fun s : ℝ => z (s • (ω : E))) r
  let T : ℝ := euclideanTangentialGradientSq (m + 3) z x ω
  have hRad :
      (∑ k : Fin (m + 3),
        (deriv (fun s : ℝ => (z (s • (ω : E))) k) r) ^ 2) =
      ‖v‖ ^ 2 := by
    rw [sphereVector_norm_sq_eq_sum_coords]
    apply Finset.sum_congr rfl
    intro k _
    rw [sphereRay_coord_deriv (m + 3) z r ω k hz]
  have hAng := vectorScaledSphereAngularIntegrand_eq_tangent
    (m + 3) z r ω hz
  have hZ :
      (∑ k : Fin (m + 3), ((z x) k) ^ 2) = ‖z x‖ ^ 2 :=
    (sphereVector_norm_sq_eq_sum_coords (m + 3) (z x)).symm
  have hGrad : euclideanGradientSq (m + 3) z x = ‖v‖ ^ 2 + T := by
    simpa only [E, x, v, T] using
      euclideanGradientSq_eq_ray_deriv_add_tangent
        (m + 3) z r ω hz
  unfold vectorSphereBridgePointwise scalarSphereBridgePointwise
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hRad, Finset.sum_sub_distrib, hAng]
  rw [← Finset.mul_sum, hZ]
  rw [hGrad]
  ring

/-- Multiplying the true Euclidean bridge density by the polar Jacobian
recovers the coordinate-summed spherical bridge integrand at every
positive radius. -/
theorem vectorSphereBridgePointwise_eq_jacobian_spatial (m : ℕ)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ) (hr : 0 < r)
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (hz : DifferentiableAt ℝ z (r • (ω : GLEuclidean (m + 3)))) :
    vectorSphereBridgePointwise m f F z r ω =
      r ^ (m + 2) * euclideanQuadraticBridgeDensity m f F z
        (r • (ω : GLEuclidean (m + 3))) := by
  rw [vectorSphereBridgePointwise_eq_spatial m f F z r ω hz]
  have hω : ‖(ω : GLEuclidean (m + 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hnorm : ‖r • (ω : GLEuclidean (m + 3))‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω]
    ring
  simp only [euclideanQuadraticBridgeDensity, hnorm]
  have hrnz : r ≠ 0 := ne_of_gt hr
  rw [pow_add]
  field_simp [hrnz]

/-- The vector Hilbert bridge is the actual unit-sphere integral of its
pointwise coordinate-summed derivative density. -/
theorem vectorSphereBridgeDensity_eq_surface_integral
    (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hg : ∀ (s : ℝ) (k : Fin (m + 3)),
      MemLp (fun ω : Metric.sphere
        (0 : GLEuclidean (m + 3)) 1 =>
          (z (s • (ω : GLEuclidean (m + 3)))) k) 2
        (unitSphereMeasure (m + 3)))
    (dv : ℝ → Fin (m + 3) → UnitSphereL2 (m + 3))
    (r : ℝ)
    (hrep : ∀ k : Fin (m + 3),
      dv r k =ᶠ[ae (unitSphereMeasure (m + 3))]
        (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
          deriv (fun s : ℝ => (z (s • (ω : GLEuclidean (m + 3)))) k) r))
    (hDInt : ∀ k : Fin (m + 3), Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (deriv (fun s : ℝ => (z (s • (ω : GLEuclidean (m + 3)))) k) r) ^ 2)
      (unitSphereMeasure (m + 3)))
    (hAngInt : ∀ k : Fin (m + 3), Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
            (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ
            (fun y : GLEuclidean (m + 3) => (z (r • y)) k)
            (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2)
      (unitSphereMeasure (m + 3)))
    (hPointInt : ∀ k : Fin (m + 3), Integrable
      (scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r)
      (unitSphereMeasure (m + 3))) :
    vectorSphereBridgeDensity m f F
        (fun s y => z (s • y)) hg dv r =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        vectorSphereBridgePointwise m f F z r ω
          ∂(unitSphereMeasure (m + 3)) := by
  unfold vectorSphereBridgeDensity vectorSphereBridgePointwise
  calc
    (∑ k : Fin (m + 3),
      scalarSphereBridgeDensity m f F
        (fun s y => (z (s • y)) k) (fun s => hg s k)
        (fun s => dv s k) r) =
      ∑ k : Fin (m + 3),
        ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
          scalarSphereBridgePointwise m f F
            (fun s y => (z (s • y)) k) r ω
            ∂(unitSphereMeasure (m + 3)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact scalarSphereBridgeDensity_eq_surface_integral m f F
        (fun s y => (z (s • y)) k) (fun s => hg s k)
        (fun s => dv s k) r (hrep k) (hDInt k) (hAngInt k)
    _ = _ := by
      rw [integral_finset_sum]
      intro k _
      exact hPointInt k

end

end BrezisOP6
