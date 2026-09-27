import BrezisOP6.SphereFiniteFamilySpatial
import BrezisOP6.SphereAnnulusRadiusOuter

/-!
# Annular spatial integral of the finite-ball bridge

The actual annular change of variables is joined to the strictly interior
surface identification.  Fubini is applied to the original polar product
measure, so ordinary spatial integrability supplies every product premise.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem euclideanQuadraticBridge_annulus_eq_finiteFamily_interval
    (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hPolarInt : Integrable
      (fun q : Metric.sphere
          (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
          ((energyPositiveAnnulus (m + 3) ρ R).indicator
            (euclideanQuadraticBridgeDensity m f F z))
          (unitSpherePolarPoint (m + 3) q))
      ((unitSphereMeasure (m + 3)).prod
        (unitSphereRadiusMeasure (m + 3)))) :
    (∫ x in energyPositiveAnnulus (m + 3) ρ R,
      euclideanQuadraticBridgeDensity m f F z x) =
      ∫ r in ρ..R,
        vectorSphereBridgeDensity m f F
          (finiteBallSphereFamily (m + 3) R z)
          (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r := by
  have hzInterior (ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1) (r : ℝ)
      (hr : r ∈ Ioo ρ R) :
      DifferentiableAt ℝ z (energySphereRay (m + 3) ω r) := by
    have hrpos : 0 < r := lt_trans hρ hr.1
    have hnorm : ‖energySphereRay (m + 3) ω r‖ = r := by
      simpa only [energySphereRay] using
        (energySphereRay_norm (m + 3) ω r hrpos.le)
    have hx : energySphereRay (m + 3) ω r ∈
        {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} := by
      change 0 < ‖energySphereRay (m + 3) ω r‖ ∧
        ‖energySphereRay (m + 3) ω r‖ < R
      rw [hnorm]
      exact ⟨hrpos, hr.2⟩
    have hopen : IsOpen
        {x : GLEuclidean (m + 3) | 0 < ‖x‖ ∧ ‖x‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact (hz.differentiableOn_one).differentiableAt
      (hopen.mem_nhds hx)
  have hpolar := annulus_integral_eq_interval_sphere_integral
    (m + 3) (by omega) ρ R hρ hρR
    (euclideanQuadraticBridgeDensity m f F z) hPolarInt
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using (measure_singleton R : volume {R} = 0)
  have hInterior : ∀ᵐ r : ℝ ∂volume.restrict (Ioc ρ R),
      r ∈ Ioo ρ R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  calc
    _ = ∫ r in ρ..R,
          r ^ ((m + 3) - 1) *
            (∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
              euclideanQuadraticBridgeDensity m f F z
                (energySphereRay (m + 3) ω r)
                ∂(unitSphereMeasure (m + 3))) ∂volume := hpolar
    _ = _ := by
      rw [intervalIntegral.integral_of_le hρR]
      rw [intervalIntegral.integral_of_le hρR]
      apply integral_congr_ae
      filter_upwards [hInterior] with r hr
      have hr0 : r ∈ Ioo (0 : ℝ) R :=
        ⟨lt_trans hρ hr.1, hr.2⟩
      have hsurface := finiteBallSphereBridgeDensity_eq_actual_surface_integral
        m f F R z hz r hr0
      rw [hsurface]
      simp only [show (m + 3) - 1 = m + 2 by omega]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (vectorSphereBridgePointwise_eq_jacobian_spatial
        m f F z r hr0.1 ω (hzInterior ω r hr)).symm

end

end BrezisOP6
