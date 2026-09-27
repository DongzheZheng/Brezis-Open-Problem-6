import BrezisOP6.SphereFiniteFamily
import BrezisOP6.SphereBridgePolarSpatial
import BrezisOP6.SpherePuncturedAngular

/-!
# The finite-ball family represents the actual spatial bridge

At every strictly interior radius the radius-indexed `L²` family is the
physical quotient field.  Its value at the outer endpoint is only a trace;
no derivative is claimed there.  The theorem below identifies the Hilbert
bridge with the surface integral of the actual Euclidean bridge at every
strictly interior radius.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set
open scoped Topology

theorem finiteBallSphereFamily_scalarBridgePointwise_eq_actual
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (k : Fin (m + 3)) :
    scalarSphereBridgePointwise m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k) r ω =
      scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r ω := by
  have hnear :
      (fun s : ℝ => (finiteBallSphereFamily (m + 3) R z s ω) k) =ᶠ[𝓝 r]
        (fun s : ℝ => (z (s • (ω : GLEuclidean (m + 3)))) k) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [finiteBallSphereFamily_interior (m + 3) R z s hs]
  have hderiv :
      deriv (fun s : ℝ =>
        (finiteBallSphereFamily (m + 3) R z s ω) k) r =
      deriv (fun s : ℝ => (z (s • (ω : GLEuclidean (m + 3)))) k) r :=
    Filter.EventuallyEq.deriv_eq hnear
  simp only [scalarSphereBridgePointwise,
    finiteBallSphereFamily_interior (m + 3) R z r hr, hderiv]

/-- All pointwise bridge terms on an interior sphere are integrable.
This follows from punctured `C¹` regularity and compactness of the sphere. -/
theorem finiteBallSphereFamily_scalarBridgePointwise_integrable
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (k : Fin (m + 3)) :
    Integrable (scalarSphereBridgePointwise m f F
      (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k) r)
      (unitSphereMeasure (m + 3)) := by
  let g : ℝ → GLEuclidean (m + 3) → ℝ :=
    fun s y => (finiteBallSphereFamily (m + 3) R z s y) k
  let μ := unitSphereMeasure (m + 3)
  have hD : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (deriv (fun s : ℝ => g s ω) r) ^ 2) μ :=
    finiteBallSphereFamily_rayDeriv_sq_integrable
      (m + 3) R z hz r hr k
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean (m + 3) => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hA : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (g r) (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ (g r) (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2) μ := by
    simpa only [g, finiteBallSphereFamily_interior
      (m + 3) R z r hr] using
      sphereAngularIntegrand_scaled_integrable_of_contDiffOn
        (m + 3) R r (fun x => (z x) k) hk hr
  have hQ : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        (g r ω) ^ 2) μ := by
    have hLp := finiteBallSphereFamily_memLp (m + 3) R z hz r k
    convert hLp.integrable_norm_pow (p := 2) (by norm_num) using 1
    ext ω
    simp [g, Real.norm_eq_abs, sq_abs]
  change Integrable (scalarSphereBridgePointwise m f F g r) μ
  unfold scalarSphereBridgePointwise
  exact (hD.const_mul _).add
    ((hA.sub (hQ.const_mul _)).const_mul _)

/-- The finite-ball `L²` bridge equals the genuine surface integral of the
Euclidean bridge at each strictly interior radius. -/
theorem finiteBallSphereBridgeDensity_eq_actual_surface_integral
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
    vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r =
      ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        vectorSphereBridgePointwise m f F z r ω
          ∂(unitSphereMeasure (m + 3)) := by
  let g := finiteBallSphereFamily (m + 3) R z
  let hg := fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k
  let dv := finiteBallSphereFamilyRadialL2 (m + 3) R z hz
  have hAng (k : Fin (m + 3)) : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (fun y : GLEuclidean (m + 3) => (g r y) k)
            (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ
            (fun y : GLEuclidean (m + 3) => (g r y) k)
            (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2)
      (unitSphereMeasure (m + 3)) := by
    have hk : ContDiffOn ℝ 1
        (fun x : GLEuclidean (m + 3) => (z x) k)
        {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
      simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
    simpa only [g, finiteBallSphereFamily_interior
      (m + 3) R z r hr] using
      sphereAngularIntegrand_scaled_integrable_of_contDiffOn
        (m + 3) R r (fun x => (z x) k) hk hr
  have hsurface := vectorSphereBridgeDensity_eq_surface_integral_general
    m f F g hg dv r
    (fun k => finiteBallSphereFamilyRadialL2_ae_eq_ray_deriv
      (m + 3) R z hz r hr k)
    (fun k => finiteBallSphereFamily_rayDeriv_sq_integrable
      (m + 3) R z hz r hr k)
    hAng
    (fun k => finiteBallSphereFamily_scalarBridgePointwise_integrable
      m f F R z hz r hr k)
  calc
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
          (∑ k : Fin (m + 3),
            scalarSphereBridgePointwise m f F
              (fun s y => (g s y) k) r ω)
            ∂(unitSphereMeasure (m + 3)) := hsurface
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [vectorSphereBridgePointwise]
      apply Finset.sum_congr rfl
      intro k _
      exact finiteBallSphereFamily_scalarBridgePointwise_eq_actual
        m f F R z r hr ω k

end

end BrezisOP6
