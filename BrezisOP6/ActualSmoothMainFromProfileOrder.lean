import BrezisOP6.ActualSmoothMainFromMean
import BrezisOP6.ProfileOrderToBridge

/-!
# Smooth minimum and equality from the radial order and zero-mode theorem

This removes the paired-energy-data and bridge-sign premises from the
previous theorem. The same regular-origin profile assumptions construct
the full two-profile energy identities for the actual competitor.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

theorem actual_smooth_ball_minimum_and_ae_equality_of_profile_order_and_mean
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ)
    (β α Af Bf AF BF : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
    (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (hβ : 0 < β) (hα : 0 < α)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α)
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hFC1 : ContDiff ℝ 1 F)
    (hdFC1 : ContDiff ℝ 1 (deriv F))
    (hHf : ContDiff ℝ 1 Hf)
    (hHF : ContDiff ℝ 1 HF)
    (huC1 : ContDiff ℝ 1 u)
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r)
    (hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (hfODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r))
    (hFODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3))
    (hMeanNonneg : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
        (fun s => sphereMeanCoefficient (m + 3)
          (scalarSphereFamilyTrace (m + 3)
            (fun t y => (finiteBallSphereFamily (m + 3) R
              (radialQuotientField (m + 3) f u) t y) k)
            (fun t => finiteBallSphereFamily_memLp (m + 3) R
              (radialQuotientField (m + 3) f u)
              (radialQuotient_contDiffOn_puncturedBall (m + 3) R
                f u hfC1 hfpos huC1.contDiffOn) t k) s))
        (fun s => sphereMeanCoefficient (m + 3)
          (finiteBallSphereFamilyRadialL2 (m + 3) R
            (radialQuotientField (m + 3) f u)
            (radialQuotient_contDiffOn_puncturedBall (m + 3) R
              f u hfC1 hfpos huC1.contDiffOn) s k)) r) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) f) := by
  have hFleRad : ∀ r, 0 < r → r ≤ R →
      0 ≤ F r ∧ F r ≤ f r := by
    intro r hr hrR
    exact ⟨(hFpos r ⟨hr, hrR⟩).le,
      (horder r ⟨hr, hrR⟩).le⟩
  obtain ⟨ρ, BfFlux, BFFlux, hfData, hFData⟩ :=
    actual_smooth_competitor_has_paired_interior_data
      m R hR f F Hf HF β α Af Bf AF BF u
      hfTaylor hFTaylor hf0 hF0 hβ hα hHf0
      hfC1 hFC1 hdfC1 hdFC1 huC1 hHf hHF
      hfpos hFleRad hfFactor hFFactor hfODE hFODE
  have hPaired : ∃ (ρf Bf' ρF BF' : ℕ → ℝ),
      SmoothProfileBallInteriorData m f
        (radialQuotientField (m + 3) f u) R ρf Bf' ∧
      SmoothProfileBallInteriorData m F
        (radialQuotientField (m + 3) f u) R ρF BF' :=
    ⟨ρ, BfFlux, ρ, BFFlux, hfData, hFData⟩
  obtain ⟨hd, hdpos, hFnonneg, hFle, hFlt⟩ :=
    bridge_signs_of_strict_profile_order m R f F hf0 hF0
      hFpos horder
  exact actual_smooth_ball_minimum_and_ae_equality_of_mean_nonnegative
    m R hR f F Hf HF α β u
    hfC1 hdfC1 hFC1 hHf hHF huC1
    hHf0 hHF0 hβ hfFactor hFFactor hfpos huBoundary
    hPublished hLocal hOdd hd hdpos
    hFnonneg hFle hFlt hPaired hMeanNonneg

end

end BrezisOP6
