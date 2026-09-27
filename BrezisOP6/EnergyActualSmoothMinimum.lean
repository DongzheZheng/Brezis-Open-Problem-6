import BrezisOP6.EnergyRegularBallBridge
import BrezisOP6.EnergyQuadraticIntegrability
import BrezisOP6.EnergyBridgeNonnegative

/-!
# Smooth ball minimality for the actual competitor

The energy bridge is applied to a genuine `C¹` field `u` with the vortex
boundary trace.  The quotient is used only in the integrals on the
punctured ball, and the transformed field has its correct removable
origin value.  The remaining quadratic sign is supplied by the geometric
sphere/Picone theorem.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

theorem actualSmoothBallEnergy_minimality_of_quadraticBridge
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hfData : SmoothProfileBallInteriorData m f
      (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
      R ρf Bf)
    (hFData : SmoothProfileBallInteriorData m F
      (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
      R ρF BF)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α) (hβ : 0 < β)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hquarticInt : Integrable
      (euclideanQuarticBridgeDensity m f F
        (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hquadNonneg : 0 ≤ ∫ x,
      euclideanQuadraticBridgeDensity m f F
        (fun y : GLEuclidean (m + 3) => (f ‖y‖)⁻¹ • u y) x
      ∂(volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hfData.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hFData.reduced_density_integrable
  have hbridgeInt := bridgeEnergyDensity_integrable_of_single
    m R f F z hfInt hFInt
  have hquadInt := euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    m R f F z hbridgeInt hquarticInt
  have hbridgeNonneg := bridgeEnergyIntegral_nonneg_of_quadratic
    m R f F z hbridgeInt hquadInt hquadNonneg hFnonneg hFle
  have hbridgeLe := euclideanBall_energy_gap_ge_bridge_of_regular_competitor
    m R hR f F Hf HF α β u ρf Bf ρF BF
    hfData hFData hPublished hHf hHF hHf0 hHF0 hβ
    hfFactor hFFactor hfpos huC1 huBoundary
  linarith

end

end BrezisOP6
