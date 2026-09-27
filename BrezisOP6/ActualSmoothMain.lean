import BrezisOP6.ActualSmoothMainFromProfileOrder
import BrezisOP6.PhysicalProfileOrder
import BrezisOP6.SphereActualMeanNonnegativeC2

/-!
# Smooth finite-ball minimum and rigidity from the radial data

This is the top-level assembly of the higher-dimensional comparison argument.
The strict order of the two profiles is proved from the radial equations and
terminal inequality, and the constant spherical mode is proved by the actual
Picone estimate.  In particular, neither of those conclusions is an input.

The existence and regularity of the physical radial profiles, the sharp
sphere spectral gap, and the published entire-vortex minimum are displayed
as external analytic inputs.  The separate Sobolev closure needed for the
full PDE statement is outside this smooth theorem.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

theorem actual_smooth_ball_minimum_and_ae_equality_from_radial_data
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F y k₀ f₂ F₂ Hf HF : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (α β Af Bf AF BF : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α)
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hdFC1 : ContDiff ℝ 1 (deriv F))
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (huC1 : ContDiff ℝ 1 u)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Icc (0 : ℝ) R))
    (hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY F r < 1)
    (hFone : Tendsto F atTop (𝓝 (1 : ℝ)))
    (hF2diffAll : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R))
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hfODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r))
    (hScont : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)))
    (hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (hOdd : UnitSphereCoordinateMeanZero (m + 3)) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) f) := by
  have hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 F := hFC2.of_le (by norm_num)
  have horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r :=
    (physical_radial_profiles_ordered_from_terminal
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hkpos hterminal hRatioFluxCont
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
      hdf hdF hode_f hode_F).1
  have hMean :=
    actual_finiteBallSphere_mean_integral_nonneg_of_C2_profiles
      m f F y k₀ f₂ F₂ Hf HF u R α β Af Bf AF BF
      hR hα hfTaylor hFTaylor hFpos hfpos hflt
      hkcont hkevent hkpos hterminal horder hRatioFluxCont
      hSlopeFluxCont hyFlt hFone hF2diffAll hyDiff hyMatch
      hFposAll hFltAll hFodeAll hηcont hfC2 hFC2
      hdf hdF hode_f hode_F hScont huC1 hHf hHF
      hFFactor huBoundary (by rw [hHf0]; exact ne_of_gt hβ)
      hfFactor hOdd
  exact actual_smooth_ball_minimum_and_ae_equality_of_profile_order_and_mean
    m R hR f F Hf HF β α Af Bf AF BF u
    (hfTaylor.toClosed hR) (hFTaylor.toClosed hR)
    hf0 hF0 hβ hα hHf0 hHF0
    hfC1 hdfC1 hFC1 hdFC1 hHf hHF huC1
    (fun r hr hrR => hfpos r ⟨hr, hrR⟩)
    hFpos horder hfFactor hFFactor hfODE
    (fun r hr _ => hFodeAll r hr)
    huBoundary hPublished hLocal hOdd hMean

end

end BrezisOP6
