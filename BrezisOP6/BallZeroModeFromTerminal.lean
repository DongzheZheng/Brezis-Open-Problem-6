import BrezisOP6.ProfileBoundsAssembly
import BrezisOP6.BallZeroMode

/-!
# From the terminal comparison to the zero spherical mode

The finite-ball ratio comparison supplies `f>F`, hence the positive Picone
weight.  Its contact theorem supplies the positive residual.  Combining
these two outputs with the interval Picone identity proves the zero-mode
quadratic inequality.  The profile barrier, regular-origin extension, and
test-function endpoint conditions are kept as explicit assumptions.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

theorem ball_zero_mode_nonnegative_from_terminal_flux
    (m : ℕ) (f F k₀ b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hfpos : ∀ r ∈ Set.Ioc 0 R, 0 < f r)
    (hflt : ∀ r ∈ Set.Ioo 0 R, f r < 1)
    (hkcont : ContinuousOn k₀ (Set.Icc 0 R))
    (hkevent : ∀ r ∈ Set.Ioc 0 R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Set.Icc 0 R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Set.Ioc 0 R, k₀ r = 1)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Set.Icc 0 R))
    (hSlopeFluxCont : ContinuousOn (slopeFlux (m + 2) f)
      (Set.Icc 0 R))
    (hyFlt : ∀ r ∈ Set.Ioc 0 R, profileY F r < 1)
    (hbarrier : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ F r ^ 2 - profileY F r)
    (hetaSmall : ∀ r ∈ Set.Ioc 0 R,
      profileEta f F r < r / Real.sqrt 2)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r))
    (hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r)
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        MeasureTheory.volume δ R)
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        MeasureTheory.volume δ R)
    (hfactor : Filter.Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hbcont : ContinuousAt b 0) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hk0 := profile_initial_ratio_gt_one_from_terminal
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  have horder := profile_ratio_ordering_on_ball_from_flux
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont hFpos hkevent
    hk0 hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  have hMpos : ∀ r ∈ Set.Ioc 0 R,
      0 < profileM f F r := by
    intro r hr
    have hkgt : 1 < profileK f F r := by
      unfold profileK
      exact (lt_div_iff₀ (hFpos r hr)).2
        (by simpa using horder.1 r hr)
    unfold profileM ratioM
    nlinarith
  have hS := profileContact_positive_on_ball_from_terminal_flux
    m f F k₀ f₂ F₂ R hR hFpos hfpos hflt hkcont hkevent
    hkpos hterminal hunique_origin hRatioFluxCont hSlopeFluxCont
    hyFlt hbarrier hetaSmall hfDiff hFDiff hdf hdF
    hode_f hode_F hnear
  apply profilePicone_zero_mode_nonnegative m f F b db f₂ F₂ R hR
    hFpos hMpos hfDiff hFDiff hdf hdF hode_f hode_F hb
  · intro r hr
    have h := hS r hr
    simpa only [profileContactResidual, profileM, ratioM] using h.le
  · exact hbR
  · exact hDint
  · exact hsq_int
  · exact hflux_int
  · exact hrem_int
  · exact hfactor
  · exact hbcont

end

end BrezisOP6
