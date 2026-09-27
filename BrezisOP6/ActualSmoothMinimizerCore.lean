import BrezisOP6.SphereEqualityActual
import BrezisOP6.SphereEqualityVector
import BrezisOP6.EnergyActualSphereMinimum
import BrezisOP6.EnergyEqualityPrelude
import BrezisOP6.SphereRaysPointwise

/-!
# Smooth finite-ball minimum and equality: the final composition core

The certificate below records analytic facts about the actual spherical
slices of the physical quotient. Separate modules construct its fields
from the regular-origin profiles and a smooth competitor. It contains no
energy inequality or equality conclusion.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

structure FiniteBallModeCertificate (m : ℕ) (f F : ℝ → ℝ) (R : ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3)) : Prop where
  smooth : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R}
  full_integrable : ∀ k : Fin (m + 3), IntervalIntegrable
    (scalarSphereBridgeDensity m f F
      (fun s y => (finiteBallSphereFamily (m + 3) R z s y) k)
      (fun s => finiteBallSphereFamily_memLp (m + 3) R z smooth s k)
      (fun s => finiteBallSphereFamilyRadialL2 (m + 3) R z smooth s k))
    volume 0 R
  mean_integrable : ∀ k : Fin (m + 3), IntervalIntegrable
    (bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
          (fun t => finiteBallSphereFamily_memLp (m + 3) R z smooth t k) s))
      (fun s => sphereMeanCoefficient (m + 3)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z smooth s k)))
    volume 0 R
  mean_nonnegative : ∀ k : Fin (m + 3), 0 ≤ ∫ r in (0 : ℝ)..R,
    bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
      (fun s => sphereMeanCoefficient (m + 3)
        (scalarSphereFamilyTrace (m + 3)
          (fun t y => (finiteBallSphereFamily (m + 3) R z t y) k)
          (fun t => finiteBallSphereFamily_memLp (m + 3) R z smooth t k) s))
      (fun s => sphereMeanCoefficient (m + 3)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z smooth s k)) r

/-- Energy minimality and equality rigidity for the actual smooth
competitor, conditional only on the named mode certificate and on the
published/geometric/profile inputs displayed in the signature. In
particular, neither a vanishing bridge integral nor sphere-valuedness of
the quotient is assumed. -/
theorem actual_smooth_ball_minimum_and_equality_punctured_of_mode_certificate
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
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
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
    (hFle : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, F ‖x‖ ≤ f ‖x‖)
    (hFlt : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 → F ‖x‖ < f ‖x‖)
    (hModes : FiniteBallModeCertificate m f F R
      (radialQuotientField (m + 3) f u)) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
      ∀ x : GLEuclidean (m + 3),
        x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R →
          x ≠ 0 → u x = radialVortex (m + 3) f x) := by
  let z := radialQuotientField (m + 3) f u
  have hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    hModes.smooth
  have hSphereInt := finiteBallSphereBridge_intervalIntegrable_of_coordinates
    m f F R z hz hModes.full_integrable
  have hSphereNonneg := finiteBallSphereBridge_integral_nonneg_of_mean_nonneg
    m f F R hR z hz hLocal hd hModes.full_integrable
    hModes.mean_integrable hModes.mean_nonnegative
  have hmin := actualSmoothBallEnergy_minimality_of_sphereBridge
    m R hR f F Hf HF α β u ρf Bf ρF BF hfData hFData
    hPublished hHf hHF hHf0 hHF0 hβ
    hfC1.continuous hFC1.continuous hfFactor hFFactor hfpos
    huC1 huBoundary hz hSphereInt hSphereNonneg hFnonneg hFle
  constructor
  · exact hmin
  intro heq x hx hx0
  have hquarticInt : Integrable
      (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) :=
    euclideanQuarticBridgeDensity_actual_quotient_integrable
      m R f F Hf HF α β u hβ hHf0 hHF0 hfFactor hFFactor
      hfpos hHf hHF hfC1.continuous hFC1.continuous huC1
  have hfInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R f z hfData.reduced_density_integrable
  have hFInt := singleProfileDensity_integrableOn_ball_of_reduced
    m R F z hFData.reduced_density_integrable
  have hbridgeInt := bridgeEnergyDensity_integrable_of_single
    m R f F z hfInt hFInt
  have hquadInt := euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    m R f F z hbridgeInt hquarticInt
  have hquadNonneg := euclideanQuadraticBridge_ball_nonneg_of_finiteFamily
    m f F R hR z hz hquadInt hSphereInt hSphereNonneg
  have hbridgeLe := euclideanBall_energy_gap_ge_bridge_of_regular_competitor
    m R hR f F Hf HF α β u ρf Bf ρF BF
    hfData hFData hPublished hHf hHF hHf0 hHF0 hβ
    hfFactor hFFactor hfpos huC1 huBoundary
  have hbridgeNonpos :
      (∫ x, bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2) x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R))) ≤ 0 := by
    dsimp [z] at hbridgeLe ⊢
    rw [heq] at hbridgeLe
    simpa only [sub_self] using hbridgeLe
  have hzeros := bridge_component_integrals_zero_of_bridge_nonpos
    m R f F z hquadInt hquarticInt hquadNonneg
    hFnonneg hFle hbridgeNonpos
  have hRays := actual_quotient_identity_on_sphere_rays_of_bridge_equalities
    m R hR f F u hfC1 hfpos huC1 huBoundary
    hLocal hOdd hd hdpos hFnonneg hFlt
    hquadInt hquarticInt hModes.full_integrable
    hModes.mean_integrable hModes.mean_nonnegative
    hzeros.1 hzeros.2
  exact vortex_eq_of_quotient_eq_on_rays (m + 3) R f u
    (fun r hr hrR => hfpos r hr hrR.le) hRays x hx hx0

end

end BrezisOP6
