import BrezisOP6.EnergyActualSmoothMinimum
import BrezisOP6.EnergyConcreteQuartic
import BrezisOP6.SphereBridgeFullBall

/-!
# From the sphere/Picone bridge to smooth ball minimality

This is the explicit meeting point of the actual Euclidean energy argument
and the finite-ball spherical bridge.  The spherical interval estimate is
transported to the signed spatial quadratic density before the quartic
remainder and the published entire-vortex minimum are used.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

/-- The totalized quotient field; all derivative calculations use it only
away from the radial origin. -/
def radialQuotientField (n : ℕ) (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n) :
    GLEuclidean n → GLEuclidean n :=
  fun x => (f ‖x‖)⁻¹ • u x

theorem actualSmoothBallEnergy_minimality_of_sphereBridge
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ρf Bf ρF BF : ℕ → ℝ)
    (hfData : SmoothProfileBallInteriorData m f
      (radialQuotientField (m + 3) f u) R ρf Bf)
    (hFData : SmoothProfileBallInteriorData m F
      (radialQuotientField (m + 3) f u) R ρF BF)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α) (hβ : 0 < β)
    (hfC0 : Continuous f) (hFC0 : Continuous F)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hz : ContDiffOn ℝ 1 (radialQuotientField (m + 3) f u)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hSphereInt : IntervalIntegrable
      (vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R
          (radialQuotientField (m + 3) f u))
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R
          (radialQuotientField (m + 3) f u) hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R
          (radialQuotientField (m + 3) f u) hz))
      volume 0 R)
    (hSphereNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R
          (radialQuotientField (m + 3) f u))
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R
          (radialQuotientField (m + 3) f u) hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R
          (radialQuotientField (m + 3) f u) hz) r)
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u := by
  let z := radialQuotientField (m + 3) f u
  have hquarticInt : Integrable
      (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) :=
    euclideanQuarticBridgeDensity_actual_quotient_integrable
      m R f F Hf HF α β u hβ hHf0 hHF0 hfFactor hFFactor
      hfpos hHf hHF hfC0 hFC0 huC1
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hfData.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hFData.reduced_density_integrable
  have hbridgeInt := bridgeEnergyDensity_integrable_of_single
    m R f F z hfInt hFInt
  have hquadInt := euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    m R f F z hbridgeInt hquarticInt
  have hquad := euclideanQuadraticBridge_ball_nonneg_of_finiteFamily
    m f F R hR z hz hquadInt hSphereInt hSphereNonneg
  exact actualSmoothBallEnergy_minimality_of_quadraticBridge
    m R hR f F Hf HF α β u ρf Bf ρF BF hfData hFData
    hPublished hHf hHF hHf0 hHF0 hβ hfFactor hFFactor
    hfpos huC1 huBoundary hquarticInt hquad hFnonneg hFle

end

end BrezisOP6
