import BrezisOP6.BallZeroModeFromTerminal
import BrezisOP6.OriginFluxFactor

/-!
# The finite-ball zero-mode theorem with its origin conditions discharged

The two local Taylor ansätze and the radial equations imply both the
small-radius contact sign and the vanishing Picone boundary flux factor.
The remaining assumptions describe the finite-ball profiles, the two
barrier conclusions, and the admissibility of a radial test coefficient.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

theorem ball_zero_mode_nonnegative_from_origin_taylor
    (m : ℕ) (f F k₀ b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
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
    (hbcont : ContinuousAt b 0) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  have hn : (3 : ℝ) ≤ (m : ℝ) + 3 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hodefDiv : ∀ r : ℝ, 0 < r → r ≤ R →
      radialGLResidual ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r) = 0 := by
    intro r hr hrR
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (f r) (deriv f r) (f₂ r) hr).mp
      (hode_f r ⟨hr, hrR⟩)
    simpa only [radialGLResidual, (hdf r ⟨hr, hrR⟩).deriv] using h
  have hodeFDiv : ∀ r : ℝ, 0 < r → r ≤ R →
      radialGLResidual ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r) = 0 := by
    intro r hr hrR
    have h := (radialODEAt_iff_divided ((m : ℝ) + 3) r
      (F r) (deriv F r) (F₂ r) hr).mp
      (hode_F r ⟨hr, hrR⟩)
    simpa only [radialGLResidual, (hdF r ⟨hr, hrR⟩).deriv] using h
  have hdiff_f : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ f r :=
    fun r _ _ => hfDiff r
  have hdiff_F : ∀ r : ℝ, 0 < r → r ≤ R → DifferentiableAt ℝ F r :=
    fun r _ _ => hFDiff r
  have hk0 := profile_initial_ratio_gt_one_from_terminal
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
    hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
    (by intro r hr; exact hdf r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hdF r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_f r ⟨hr.1, hr.2.le⟩)
    (by intro r hr; exact hode_F r ⟨hr.1, hr.2.le⟩)
  have hβα : α < β := initial_slope_order_from_origin_ratio
    hR hα hfTaylor hFTaylor hkcont hkevent hk0
  have hnear' := original_profiles_contact_pos_near_origin_on_localTaylor
    hn hR hα hβα hfTaylor hFTaylor hdiff_f hdiff_F
    hodefDiv hodeFDiv
  have hnear : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r, 0 < r → r < ρ → r ≤ R →
        0 < profileContactResidual f F r := by
    obtain ⟨ρ, hρ, hsmall⟩ := hnear'
    exact ⟨ρ, hρ, by
      intro r hr hrρ _
      simpa only [profileContactResidual] using hsmall r hr hrρ⟩
  have hfactor := original_profiles_origin_factor_tendsto_zero_on_ball_localTaylor
    hn hR hα hβα hfTaylor hFTaylor hdiff_f hdiff_F
    hodefDiv hodeFDiv
  exact ball_zero_mode_nonnegative_from_terminal_flux
    m f F k₀ b db f₂ F₂ R hR hFpos hfpos hflt
    hkcont hkevent hkpos hterminal hunique_origin
    hRatioFluxCont hSlopeFluxCont hyFlt hbarrier hetaSmall
    hfDiff hFDiff hdf hdF hode_f hode_F hnear
    hb hbR hDint hsq_int hflux_int hrem_int hfactor hbcont

end

end BrezisOP6
