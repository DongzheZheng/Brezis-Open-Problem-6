import BrezisOP6.SphereEqualityVector
import BrezisOP6.SphereFiniteFamilyOuterL2
import BrezisOP6.SphereFiniteFamilyNonnegative
import BrezisOP6.EnergyEqualityPrelude

/-!
# Equality rigidity for an actual smooth competitor

This theorem combines the exact spatial-to-spherical bridge identity, the
coordinatewise equality mechanism, the genuine outer `L²` trace of the
physical quotient, and the quartic equality constraint.  Its hypotheses are
the ordinary integrability and profile conditions used by the minimum
theorem.  It does not assume that any coordinate bridge vanishes or that the
quotient is sphere-valued.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology

theorem actual_quotient_identity_on_sphere_rays_of_bridge_equalities
    (m : ℕ) (R : ℝ) (hR : 0 < R) (f F : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hdpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r ^ 2 - F r ^ 2)
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFlt : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 → F ‖x‖ < f ‖x‖)
    (hquadInt : Integrable
      (euclideanQuadraticBridgeDensity m f F
        (fun x => (f ‖x‖)⁻¹ • u x))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hquarticInt : Integrable
      (euclideanQuarticBridgeDensity m f F
        (fun x => (f ‖x‖)⁻¹ • u x))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hfullInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (scalarSphereBridgeDensity m f F
        (fun s y => (finiteBallSphereFamily (m + 3) R
          (fun x => (f ‖x‖)⁻¹ • u x) s y) k)
        (fun s => finiteBallSphereFamily_memLp (m + 3) R
          (fun x => (f ‖x‖)⁻¹ • u x)
          (radialQuotient_contDiffOn_puncturedBall (m + 3) R
            f u hfC1 hfpos huC1) s k)
        (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R
          (fun x => (f ‖x‖)⁻¹ • u x)
          (radialQuotient_contDiffOn_puncturedBall (m + 3) R
            f u hfC1 hfpos huC1) s k))
      volume 0 R)
    (hmeanInt : ∀ k : Fin (m + 3), IntervalIntegrable
      (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R
              (fun x => (f ‖x‖)⁻¹ • u x) t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R
              (fun x => (f ‖x‖)⁻¹ • u x)
              (radialQuotient_contDiffOn_puncturedBall (m + 3) R
                f u hfC1 hfpos huC1) t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R
            (fun x => (f ‖x‖)⁻¹ • u x)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              f u hfC1 hfpos huC1) s k)))
      volume 0 R)
    (hmeanNonneg : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R
              (fun x => (f ‖x‖)⁻¹ • u x) t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R
              (fun x => (f ‖x‖)⁻¹ • u x)
              (radialQuotient_contDiffOn_puncturedBall (m + 3) R
                f u hfC1 hfpos huC1) t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R
            (fun x => (f ‖x‖)⁻¹ • u x)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              f u hfC1 hfpos huC1) s k)) r)
    (hquadZero : (∫ x,
      euclideanQuadraticBridgeDensity m f F
        (fun y => (f ‖y‖)⁻¹ • u y) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0)
    (hquarticZero : (∫ x,
      euclideanQuarticBridgeDensity m f F
        (fun y => (f ‖y‖)⁻¹ • u y) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) = 0) :
    ∀ r : ℝ, r ∈ Ioo (0 : ℝ) R →
      ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
        (f ‖r • (ω : GLEuclidean (m + 3))‖)⁻¹ •
          u (r • (ω : GLEuclidean (m + 3))) =
            (ω : GLEuclidean (m + 3)) := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos huC1
  have hvectorInt : IntervalIntegrable
      (vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz))
      volume 0 R :=
    finiteBallSphereBridge_intervalIntegrable_of_coordinates
      m f F R z hz hfullInt
  have hvectorZero : (∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r) = 0 := by
    rw [← euclideanQuadraticBridge_ball_integral_eq_finiteFamily
      m f F R hR z hz hquadInt hvectorInt]
    exact hquadZero
  have hderivZero := finiteBall_vector_bridge_zero_forces_radial_ae
    m f F R hR z hz hLocal hd hdpos
    hfullInt hmeanInt hmeanNonneg hvectorZero
  have hunit : ∀ x : GLEuclidean (m + 3),
      0 < ‖x‖ → ‖x‖ < R → ‖z x‖ ^ 2 = 1 :=
    quotient_norm_sq_one_on_punctured_of_quartic_integral_zero
      m R f F z hz.continuousOn hquarticInt
      hFnonneg hFlt hquarticZero
  have hOuterLimit (k : Fin (m + 3)) : Tendsto
      (fun s => sphereMeanZeroPart (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
          (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) s))
      (𝓝[<] R)
      (𝓝 (sphereMeanZeroPart (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
          (fun t => finiteBallSphereFamily_memLp (m + 3) R z hz t k) R))) := by
    have hTrace :=
      actual_quotient_finiteBallSphereFamily_trace_tendsto_outer_left
        (m + 3) R hR f u hfC1 hfpos huC1 huBoundary k
    have hProj : Continuous (sphereMeanZeroPart (m + 3)) := by
      unfold sphereMeanZeroPart sphereMeanCoefficient
      fun_prop
    exact hProj.continuousAt.tendsto.comp hTrace
  intro r hr ω
  exact finiteBallSphereFamily_eq_identity_of_radial_rigidity
    (m + 3) (by omega) R hR z hz hOdd hunit hderivZero
    hOuterLimit r hr ω

end

end BrezisOP6
