import BrezisOP6.EnergySmoothBallBridgeInterior
import BrezisOP6.SphereBridgePolarSpatial

/-!
# From the quadratic bridge to the full energy bridge

The angular and Picone arguments control the quadratic part of the bridge.
The remaining quartic part is pointwise nonnegative because the finite-ball
profile dominates the entire profile. This module performs the final
integration step on the actual Euclidean ball.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- Integrability of both single-profile densities automatically supplies
integrability of their two-profile bridge. -/
theorem bridgeEnergyDensity_integrable_of_single (m : ℕ)
    (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfInt : Integrable
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hFInt : Integrable
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R))) :
    Integrable
      (bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)) := by
  have heq :
      (bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2)) =
      fun x =>
        singleProfileDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => f ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x -
        singleProfileDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => F ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x := by
    funext x
    exact (singleProfileDensity_sub_eq_bridge
      (m + 3) (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x).symm
  rw [heq]
  exact hfInt.sub hFInt

/-- The quartic contribution to the two-profile energy bridge. -/
def euclideanQuarticBridgeDensity (m : ℕ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) : ℝ :=
  (f ‖x‖ ^ 4 - F ‖x‖ ^ 4) * (‖z x‖ ^ 2 - 1) ^ 2

/-- The concrete two-profile density is the sum of its quadratic and
quartic pieces, with the coefficients in the Ginzburg--Landau energy. -/
theorem bridgeEnergyDensity_eq_quadratic_add_quartic (m : ℕ)
    (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) :
    bridgeEnergyDensity (m + 3)
      (fun y : GLEuclidean (m + 3) => f ‖y‖)
      (fun y : GLEuclidean (m + 3) => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2)
      (fun y => ‖y‖⁻¹ ^ 2) x =
    euclideanQuadraticBridgeDensity m f F z x / 2 +
      euclideanQuarticBridgeDensity m f F z x / 4 := by
  have hdim : (((m + 3 : ℕ) : ℝ) - 1) = (m + 2 : ℝ) := by
    push_cast
    ring
  simp only [bridgeEnergyDensity, euclideanQuadraticBridgeDensity,
    euclideanQuarticBridgeDensity, hdim, div_eq_mul_inv, ← inv_pow]
  ring

/-- The full bridge integral is nonnegative as soon as the angular/Picone
quadratic integral is nonnegative and the ordered profiles make the quartic
term nonnegative. All integrability statements concern the true ball measure. -/
theorem bridgeEnergyIntegral_nonneg_of_quadratic (m : ℕ)
    (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hbridgeInt : Integrable
      (bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hquadInt : Integrable (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)))
    (hquad : 0 ≤
      ∫ x, euclideanQuadraticBridgeDensity m f F z x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    0 ≤ ∫ x, bridgeEnergyDensity (m + 3)
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
  have hpoint (x : GLEuclidean (m + 3)) :
      b x = q x / 2 + t x / 4 :=
    bridgeEnergyDensity_eq_quadratic_add_quartic m f F z x
  have htEq : t = fun x => 4 * (b x - q x / 2) := by
    funext x
    linarith [hpoint x]
  have htInt : Integrable t μ := by
    rw [htEq]
    exact (hbridgeInt.sub (hquadInt.div_const 2)).const_mul 4
  have htNonneg : 0 ≤ ∫ x, t x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact bridge_quartic_nonneg (hFnonneg x hx) (hFle x hx)
  have hsum : (∫ x, b x ∂μ) =
      (∫ x, q x ∂μ) / 2 + (∫ x, t x ∂μ) / 4 := by
    have heq : b = fun x => q x / 2 + t x / 4 := by
      funext x
      exact hpoint x
    rw [heq, integral_add (hquadInt.div_const 2) (htInt.div_const 4)]
    simp only [integral_div]
    rfl
  change 0 ≤ ∫ x, b x ∂μ
  rw [hsum]
  linarith

end

end BrezisOP6
