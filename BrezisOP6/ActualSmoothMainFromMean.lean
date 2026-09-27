import BrezisOP6.ActualModeCertificate
import BrezisOP6.EnergyActualInteriorPair
import BrezisOP6.BallPuncturedEqualityAE

/-!
# Smooth finite-ball theorem from the proved analytic components

The premise `hMeanNonneg` is the exact conclusion of the actual Picone
zero-mode theorem.  All coordinate bridge and mean-density integrability
is constructed for the physical smooth competitor in this module.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

theorem actual_smooth_ball_minimum_and_ae_equality_of_mean_nonnegative
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hFC1 : ContDiff ℝ 1 F)
    (hHf : ContDiff ℝ 1 Hf)
    (hHF : ContDiff ℝ 1 HF)
    (huC1 : ContDiff ℝ 1 u)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α) (hβ : 0 < β)
    (hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3))
    (hd : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
    (hdpos : ∀ r ∈ Ioo (0 : ℝ) R, 0 < f r ^ 2 - F r ^ 2)
    (hFnonneg : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, 0 ≤ F ‖x‖)
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖)
    (hFlt : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 → F ‖x‖ < f ‖x‖)
    (hPaired : ∃ (ρf Bf ρF BF : ℕ → ℝ),
      SmoothProfileBallInteriorData m f
        (radialQuotientField (m + 3) f u) R ρf Bf ∧
      SmoothProfileBallInteriorData m F
        (radialQuotientField (m + 3) f u) R ρF BF)
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
  obtain ⟨ρf, Bf, ρF, BF, hfData, hFData⟩ := hPaired
  have hModes : FiniteBallModeCertificate m f F R
      (radialQuotientField (m + 3) f u) :=
    actual_smooth_mode_certificate_of_mean_nonnegative
      m R hR f F Hf HF u hfC1 hdfC1 hFC1 hHf hHF huC1
      (by rw [hHf0]; exact ne_of_gt hβ)
      hfFactor hFFactor hfpos
      (fun r hr => le_of_lt (hdpos r hr)) hMeanNonneg
  have hMain :=
    actual_smooth_ball_minimum_and_equality_punctured_of_mode_certificate
      m R hR f F Hf HF α β u ρf Bf ρF BF
      hfData hFData hPublished hHf hHF hHf0 hHF0 hβ
      hfC1 hFC1 hfFactor hFFactor hfpos
      huC1.contDiffOn huBoundary hLocal hOdd hd hdpos
      hFnonneg hFle hFlt hModes
  refine ⟨hMain.1, ?_⟩
  intro heq
  exact ae_eq_on_ball_of_eq_punctured m R u (radialVortex (m + 3) f)
    (hMain.2 heq)

end

end BrezisOP6
