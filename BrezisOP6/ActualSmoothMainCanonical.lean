import BrezisOP6.ActualSmoothMain
import BrezisOP6.PhysicalRadialRegularity
import BrezisOP6.SphereCoordinateOddness

/-!
# Smooth finite-ball minimum with the canonical profile quotient

This is the top-level assembly of the higher-dimensional comparison argument.
The physical finite-ball boundary condition `f(R)=1` and the entire-space
bound `F(R)<1` give the terminal comparison.  The regular-origin ratio
is constructed as a piecewise function, so no independent quotient
extension is required in this public interface.

The existence and regularity of the physical radial profiles, the sharp
sphere spectral gap, and the published entire-vortex minimum are displayed
as external analytic inputs.  The separate Sobolev closure needed for the
full PDE statement is outside this smooth theorem.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

theorem actual_smooth_ball_minimum_and_ae_equality_canonical
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F y Hf HF : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (α β Af Bf AF BF : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α)
    (hfC2 : ContDiff ℝ 2 f) (hFC2 : ContDiff ℝ 2 F)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (huC1 : ContDiff ℝ 1 u)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hflt : ∀ r ∈ Ioo (0 : ℝ) R, f r < 1)
    (hfR : f R = 1)
    (hyFlt : ∀ r ∈ Ioc (0 : ℝ) R, profileY F r < 1)
    (hFone : Tendsto F atTop (𝓝 (1 : ℝ)))
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r, 0 < r → y r = profileY F r)
    (hFposAll : ∀ r, 0 < r → 0 < F r)
    (hFltAll : ∀ r, 0 < r → F r < 1)
    (hFodeAll : ∀ r, 0 < r →
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r)
        (deriv (deriv F) r))
    (hfODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r))
    (hfFactor : ∀ r, 0 < r → r ≤ R → f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R → F r = r * HF (r ^ 2))
    (huBoundary : ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3)) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) f) := by
  have hfC1 : ContDiff ℝ 1 f := hfC2.of_le (by norm_num)
  have hFC1 : ContDiff ℝ 1 F := hFC2.of_le (by norm_num)
  have hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r := by
    intro r hr
    exact hFposAll r hr.1
  have hdfC1 : ContDiff ℝ 1 (deriv f) :=
    radial_profile_deriv_contDiff_one f hfC2
  have hdFC1 : ContDiff ℝ 1 (deriv F) :=
    radial_profile_deriv_contDiff_one F hFC2
  let f₂ : ℝ → ℝ := deriv (deriv f)
  let F₂ : ℝ → ℝ := deriv (deriv F)
  have hF2diffAll : ∀ r, 0 < r →
      DifferentiableAt ℝ (deriv F) r :=
    radial_profile_deriv_differentiable_positive F hFC2
  have hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt f hfC2 r
  have hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r := by
    intro r _
    exact radial_profile_deriv_hasDerivAt F hFC2 r
  have hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r) := by
    intro r hr
    exact hfODE r hr.1 hr.2
  have hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r) := by
    intro r hr
    exact hFodeAll r hr.1
  have hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R) := by
    have hraw : Continuous (fun r : ℝ =>
        r ^ (m + 2) * (F r * deriv f r - f r * deriv F r)) :=
      (continuous_id.pow (m + 2)).mul
        ((hFC1.continuous.mul hdfC1.continuous).sub
          (hfC1.continuous.mul hdFC1.continuous))
    simpa only [ratioFlux] using hraw.continuousOn
  have hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Icc (0 : ℝ) R) := by
    have hraw : Continuous (fun r : ℝ =>
        r ^ (m + 2) * (r * deriv f r - f r)) :=
      (continuous_id.pow (m + 2)).mul
        ((continuous_id.mul hdfC1.continuous).sub hfC1.continuous)
    simpa only [slopeFlux] using hraw.continuousOn
  let k₀ := physicalProfileRatioExtension f F α β
  obtain ⟨hkcont, hkevent, hkpos⟩ :=
    physical_profile_ratio_extension_data f F R α β Af Bf AF BF
      hR hα hβ hfTaylor hFTaylor hfpos hFpos
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
  have hterminal : F R < f R := by
    rw [hfR]
    exact hFltAll R hR
  have horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r :=
    (physical_radial_profiles_ordered_from_terminal
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hkpos hterminal hRatioFluxCont
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
      hdf hdF hode_f hode_F).1
  have hαβ : α < β :=
    physical_radial_initial_slopes_ordered_from_terminal
      m f F k₀ f₂ F₂ R α β Af Bf AF BF hR hα
      hfTaylor hFTaylor hFpos hkcont hkevent hkpos
      hterminal hRatioFluxCont
      (fun r => hfC1.differentiable_one r)
      (fun r => hFC1.differentiable_one r)
      hdf hdF hode_f hode_F
  have hηcont : ContinuousOn (profileEta f F) (Icc (0 : ℝ) R) :=
    physical_profile_eta_continuousOn m f F R α β Af Bf AF BF
      hR hα hαβ hfTaylor hFTaylor hfC2 hFC2 hFpos horder
      hfODE (fun r hr _ => hFodeAll r hr)
  have hScont : Tendsto (profileContactResidual f F)
      (𝓝[<] R) (𝓝 (profileContactResidual f F R)) :=
    physical_profile_contact_left_limit f F R hR hfC1 hFC1
      (hFpos R ⟨hR, le_rfl⟩) hηcont
  exact actual_smooth_ball_minimum_and_ae_equality_from_radial_data
    m R hR f F y k₀ f₂ F₂ Hf HF u α β Af Bf AF BF
    hα hβ hfTaylor hFTaylor hf0 hF0 hHf0 hHF0
    hfC2 hFC2 hdfC1 hdFC1 hHf hHF huC1
    hFpos hfpos hflt hkcont hkevent hkpos hterminal
    hRatioFluxCont hSlopeFluxCont hyFlt hFone hF2diffAll
    hyDiff hyMatch hFposAll hFltAll hFodeAll hηcont
    hdf hdF hode_f hode_F hfODE hScont hfFactor hFFactor
    huBoundary hPublished hLocal
    (unitSphereCoordinateMeanZero_actual (m + 3))

end

end BrezisOP6
