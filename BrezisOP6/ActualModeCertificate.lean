import BrezisOP6.ActualSmoothMinimizerCore
import BrezisOP6.SphereActualScalarBridgeIntegrable
import BrezisOP6.SphereActualMeanIntegrable
import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# The actual smooth mode certificate

For the physical quotient of a smooth competitor, both integrability
fields in the finite-ball mode certificate follow from regular-origin
factorization and the profile order.  The remaining nonnegative mean
integral is supplied by the Picone theorem.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

theorem actual_smooth_mode_certificate_of_mean_nonnegative
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfC1 : ContDiff ℝ 1 f)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hFC1 : ContDiff ℝ 1 F)
    (hHf : ContDiff ℝ 1 Hf)
    (hHF : ContDiff ℝ 1 HF)
    (huC1 : ContDiff ℝ 1 u)
    (hHf0 : Hf 0 ≠ 0)
    (hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (hfpos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (hd0 : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2)
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
    FiniteBallModeCertificate m f F R
      (radialQuotientField (m + 3) f u) := by
  let z := radialQuotientField (m + 3) f u
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfpos huC1.contDiffOn
  refine ⟨hz, ?_, ?_, ?_⟩
  · intro k
    simpa only [z, radialQuotientField] using
      actual_finiteBall_scalarBridge_intervalIntegrable
        m R hR f F Hf u hfC1 hdfC1 hFC1 hHf huC1
        hHf0 hfFactor hfpos hd0 k
  · intro k
    simpa only [z, radialQuotientField] using
      actual_finiteBallSphere_meanDensity_intervalIntegrable
        m R hR f F Hf HF u hfC1 hHf hHF huC1
        hHf0 hfFactor hFFactor hfpos k
  · exact hMeanNonneg

end

end BrezisOP6
