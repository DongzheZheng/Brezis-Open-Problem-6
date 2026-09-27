import BrezisOP6.EnergyBridgeNonnegative

/-!
# Quantitative lower bound by the quadratic bridge

The quartic piece of the two-profile bridge is nonnegative under the
proved profile order.  Keeping it in the exact decomposition shows that
the full energy bridge controls one half of the quadratic bridge.  This
quantitative form is needed for annular stability of near-minimizers.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Metric

theorem bridgeEnergyIntegral_ge_half_quadratic
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hQuadInt : Integrable (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hQuarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    (∫ x, euclideanQuadraticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) / 2 ≤
      ∫ x,
        bridgeEnergyDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => f ‖y‖)
          (fun y : GLEuclidean (m + 3) => F ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)) := by
  let μ : Measure (GLEuclidean (m + 3)) :=
    volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)
  let b : GLEuclidean (m + 3) → ℝ :=
    bridgeEnergyDensity (m + 3)
      (fun y => f ‖y‖) (fun y => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
  let q := euclideanQuadraticBridgeDensity m f F z
  let t := euclideanQuarticBridgeDensity m f F z
  have htNonneg : 0 ≤ ∫ x, t x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact bridge_quartic_nonneg (hFnonneg x hx) (hFle x hx)
  have hIdentity : (∫ x, b x ∂μ) =
      (∫ x, q x ∂μ) / 2 + (∫ x, t x ∂μ) / 4 := by
    have heq : b = fun x => q x / 2 + t x / 4 := by
      funext x
      exact bridgeEnergyDensity_eq_quadratic_add_quartic m f F z x
    rw [heq, integral_add (hQuadInt.div_const 2)
      (hQuarticInt.div_const 4)]
    simp only [integral_div]
    rfl
  rw [hIdentity]
  linarith

/-- If the two-profile bridge lies below the physical energy gap, its
quadratic part lies below twice that gap.  The only analytic inputs are
the integrability and profile-order facts stated explicitly here. -/
theorem quadraticBridgeIntegral_le_two_energy_gap
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hQuadInt : Integrable (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hQuarticInt : Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖)
    (hBridgeLe :
      (∫ x,
        bridgeEnergyDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => f ‖y‖)
          (fun y : GLEuclidean (m + 3) => F ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R))) ≤
      euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f)) :
    (∫ x, euclideanQuadraticBridgeDensity m f F z x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) ≤
      2 * (euclideanBallEnergy (m + 3) R u -
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) f)) := by
  have hHalf := bridgeEnergyIntegral_ge_half_quadratic
    m R f F z hQuadInt hQuarticInt hFnonneg hFle
  linarith

end

end BrezisOP6
