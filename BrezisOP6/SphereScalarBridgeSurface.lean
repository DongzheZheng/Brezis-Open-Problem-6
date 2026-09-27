import BrezisOP6.SphereScalarGradientDomination
import BrezisOP6.SphereFiniteFamilySpatial

/-!
# A single target-coordinate spherical bridge as a surface integral

The existing polar bridge identity sums over target coordinates.  Absolute
integrability requires each coordinate separately, so this file exposes
the scalar version with its actual Fréchet and radial derivatives.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem finiteBallSphereFamily_scalarBridgeDensity_eq_actual_surface_integral
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R)
    (k : Fin (m + 3)) :
    scalarSphereBridgeDensity m f F
      (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
      (fun s => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
      (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k) r =
    ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      scalarSphereBridgePointwise m f F
        (fun s y => (z (s • y)) k) r ω
        ∂(unitSphereMeasure (m + 3)) := by
  let g : ℝ → GLEuclidean (m + 3) → ℝ :=
    fun s y => (finiteBallSphereFamily (m + 3) R z s y) k
  let hg := fun s =>
    finiteBallSphereFamily_memLp (m + 3) R z hz s k
  let dv : ℝ → UnitSphereL2 (m + 3) :=
    fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z hz s k
  have hk : ContDiffOn ℝ 1
      (fun x : GLEuclidean (m + 3) => (z x) k)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
    simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj k).contDiff.comp_contDiffOn hz
  have hAng : Integrable
      (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
        ‖fderiv ℝ (g r) (ω : GLEuclidean (m + 3))‖ ^ 2 -
          ((fderiv ℝ (g r) (ω : GLEuclidean (m + 3)))
            (ω : GLEuclidean (m + 3))) ^ 2)
      (unitSphereMeasure (m + 3)) := by
    simpa only [g, finiteBallSphereFamily_interior
      (m + 3) R z r hr] using
      sphereAngularIntegrand_scaled_integrable_of_contDiffOn
        (m + 3) R r (fun x => (z x) k) hk hr
  have hsurface := scalarSphereBridgeDensity_eq_surface_integral
    m f F g hg dv r
    (finiteBallSphereFamilyRadialL2_ae_eq_ray_deriv
      (m + 3) R z hz r hr k)
    (finiteBallSphereFamily_rayDeriv_sq_integrable
      (m + 3) R z hz r hr k)
    hAng
  calc
    _ = ∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        scalarSphereBridgePointwise m f F g r ω
          ∂(unitSphereMeasure (m + 3)) := hsurface
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact finiteBallSphereFamily_scalarBridgePointwise_eq_actual
        m f F R z r hr ω k

end

end BrezisOP6
