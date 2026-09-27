import BrezisOP6.OriginRatioGlobalProfile
import BrezisOP6.PositiveRadiusProfileUniqueness
import BrezisOP6.ProfileBoundsAssembly
import BrezisOP6.OriginTaylorInterior
import BrezisOP6.OriginFluxFactor

/-!
# Strict order of the physical radial profiles

The terminal inequality `F R < f R` and the two radial equations imply
`F < f` throughout the punctured finite ball.  At the singular origin the
ratio is represented by its regular extension `k₀`; the equality case of
its initial value is ruled out by the origin contraction and ordinary
positive-radius ODE uniqueness.  Neither global profile order nor an
ODE-uniqueness oracle is an input of the result.

The regularity, positivity, and flux-continuity hypotheses for `k₀` remain
displayed.  They describe exactly the origin-extension interface needed
by the weighted-ratio comparison theorem.
-/

namespace BrezisOP6

open Set Filter
open scoped Topology

noncomputable section

/-- The regular-origin value of the physical quotient is the ratio of
initial slopes.  Away from zero this is exactly `f/F`, including in a
full neighborhood of the outer radius. -/
def physicalProfileRatioExtension
    (f F : ℝ → ℝ) (α β : ℝ) (r : ℝ) : ℝ :=
  if r = 0 then β / α else profileK f F r

theorem physical_profile_ratio_extension_data
    (f F : ℝ → ℝ) (R α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F) :
    ContinuousOn (physicalProfileRatioExtension f F α β)
        (Icc (0 : ℝ) R) ∧
    (∀ r ∈ Ioc (0 : ℝ) R,
      physicalProfileRatioExtension f F α β =ᶠ[𝓝 r]
        profileK f F) ∧
    (∀ r ∈ Icc (0 : ℝ) R,
      0 < physicalProfileRatioExtension f F α β r) := by
  let k₀ := physicalProfileRatioExtension f F α β
  have hnear : ∀ r : ℝ, r ≠ 0 →
      k₀ =ᶠ[𝓝 r] profileK f F := by
    intro r hr
    filter_upwards [eventually_ne_nhds hr] with t ht
    simp [k₀, physicalProfileRatioExtension, ht]
  have hright : Tendsto k₀ (𝓝[>] (0 : ℝ)) (𝓝 (β / α)) := by
    have heq : k₀ =ᶠ[𝓝[>] (0 : ℝ)] profileK f F := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hrpos : 0 < r := hr
      simp [k₀, physicalProfileRatioExtension, ne_of_gt hrpos]
    exact (tendsto_congr' heq).2
      (profileK_origin_limit hα
        (hfTaylor.toGlobal hR) (hFTaylor.toGlobal hR))
  have hfilter : 𝓝[Ioc (0 : ℝ) R] (0 : ℝ) = 𝓝[>] (0 : ℝ) := by
    apply le_antisymm
    · exact nhdsWithin_mono _ Ioc_subset_Ioi_self
    · exact nhdsWithin_le_iff.mpr (Ioc_mem_nhdsGT hR)
  have hcont0 : ContinuousWithinAt k₀ (Icc (0 : ℝ) R) 0 := by
    have hcontRight : ContinuousWithinAt k₀ (Ioc (0 : ℝ) R) 0 := by
      change Tendsto k₀ (𝓝[Ioc (0 : ℝ) R] 0) (𝓝 (k₀ 0))
      rw [hfilter]
      simpa [k₀, physicalProfileRatioExtension] using hright
    have hset : insert (0 : ℝ) (Ioc (0 : ℝ) R) = Icc (0 : ℝ) R := by
      ext r
      simp only [mem_insert_iff, mem_Ioc, mem_Icc]
      constructor
      · rintro (rfl | ⟨hr, hrR⟩)
        · exact ⟨le_rfl, hR.le⟩
        · exact ⟨hr.le, hrR⟩
      · intro hr
        rcases eq_or_lt_of_le hr.1 with heq | hlt
        · exact Or.inl heq.symm
        · exact Or.inr ⟨hlt, hr.2⟩
    rw [← hset]
    exact continuousWithinAt_insert_self.mpr hcontRight
  have hcont : ContinuousOn k₀ (Icc (0 : ℝ) R) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with heq | hrpos
    · subst r
      exact hcont0
    · have hFne : F r ≠ 0 := ne_of_gt (hFpos r ⟨hrpos, hr.2⟩)
      have hcontK : ContinuousAt (profileK f F) r := by
        simpa only [profileK] using
          (hfDiff r).continuousAt.div (hFDiff r).continuousAt hFne
      have hnear' := hnear r (ne_of_gt hrpos)
      exact (hcontK.congr_of_eventuallyEq hnear').continuousWithinAt
  have hpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with heq | hrpos
    · subst r
      simpa [k₀, physicalProfileRatioExtension] using div_pos hβ hα
    · have hfr := hfpos r ⟨hrpos, hr.2⟩
      have hFr := hFpos r ⟨hrpos, hr.2⟩
      simpa [k₀, physicalProfileRatioExtension, ne_of_gt hrpos,
        profileK] using div_pos hfr hFr
  exact ⟨hcont, (fun r hr => hnear r (ne_of_gt hr.1)), hpos⟩

theorem physical_radial_profiles_ordered_from_terminal
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ) (R α AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    (∀ r ∈ Ioc (0 : ℝ) R, F r < f r) ∧
    (∀ r ∈ Ioc (0 : ℝ) R,
      0 < deriv (profileK f F) r) := by
  have hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Ioc (0 : ℝ) R, k₀ r = 1 :=
    ratio_origin_one_implies_identically_one_of_regular_ode_uniqueness
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hRatioFluxCont hfDiff hFDiff hdf hdF
      hode_f hode_F
      (radial_profile_positive_radius_ivp_unique
        m f F f₂ F₂ R hfDiff hFDiff hdf hdF hode_f hode_F)
  have hk0 : 1 < k₀ 0 :=
    profile_initial_ratio_gt_one_from_terminal
      m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
      hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
      hdf hdF hode_f hode_F
  exact profile_ratio_ordering_on_ball_from_flux
    m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont hFpos
    hkevent hk0 hfDiff hFDiff hdf hdF hode_f hode_F

/-- The same profile-order mechanism also proves that the finite-ball
initial slope exceeds the entire-space initial slope.  This is exposed
separately because regularity of the interaction variable at the origin
uses the strict slope inequality. -/
theorem physical_radial_initial_slopes_ordered_from_terminal
    (m : ℕ) (f F k₀ f₂ F₂ : ℝ → ℝ)
    (R α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hkcont : ContinuousOn k₀ (Icc (0 : ℝ) R))
    (hkevent : ∀ r ∈ Ioc (0 : ℝ) R,
      k₀ =ᶠ[𝓝 r] profileK f F)
    (hkpos : ∀ r ∈ Icc (0 : ℝ) R, 0 < k₀ r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    α < β := by
  have hunique_origin : k₀ 0 = 1 →
      ∀ r ∈ Ioc (0 : ℝ) R, k₀ r = 1 :=
    ratio_origin_one_implies_identically_one_of_regular_ode_uniqueness
      m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
      hkcont hkevent hRatioFluxCont hfDiff hFDiff hdf hdF
      hode_f hode_F
      (radial_profile_positive_radius_ivp_unique
        m f F f₂ F₂ R hfDiff hFDiff hdf hdF hode_f hode_F)
  have hk0 : 1 < k₀ 0 :=
    profile_initial_ratio_gt_one_from_terminal
      m f F k₀ f₂ F₂ R hR hkcont hRatioFluxCont
      hFpos hkevent hkpos hterminal hunique_origin hfDiff hFDiff
      hdf hdF hode_f hode_F
  exact initial_slope_order_from_origin_ratio hR hα
    (hfTaylor.toClosed hR) (hFTaylor.toClosed hR)
    hkcont hkevent hk0

/-- A version using the canonical piecewise quotient extension.  The
initial slopes and positivity hypotheses construct the extension rather
than supplying it as a separate object.  The only remaining origin
regularity hypothesis is continuity of the weighted ratio flux. -/
theorem physical_radial_profiles_ordered_from_terminal_canonical
    (m : ℕ) (f F f₂ F₂ : ℝ → ℝ)
    (R α β Af Bf AF BF : ℝ)
    (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hfTaylor : RadialOriginTaylorInterior f β Af Bf R)
    (hFTaylor : RadialOriginTaylorInterior F α AF BF R)
    (hfpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < f r)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (hterminal : F R < f R)
    (hRatioFluxCont : ContinuousOn (ratioFlux (m + 2) f F)
      (Icc (0 : ℝ) R))
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Ioo (0 : ℝ) R,
      radialODEAt ((m : ℝ) + 3)
        r (F r) (deriv F r) (F₂ r)) :
    (∀ r ∈ Ioc (0 : ℝ) R, F r < f r) ∧
    (∀ r ∈ Ioc (0 : ℝ) R,
      0 < deriv (profileK f F) r) := by
  let k₀ := physicalProfileRatioExtension f F α β
  obtain ⟨hkcont, hkevent, hkpos⟩ :=
    physical_profile_ratio_extension_data f F R α β Af Bf AF BF
      hR hα hβ hfTaylor hFTaylor hfpos hFpos hfDiff hFDiff
  exact physical_radial_profiles_ordered_from_terminal
    m f F k₀ f₂ F₂ R α AF BF hR hα hFTaylor hFpos
    hkcont hkevent hkpos hterminal hRatioFluxCont
    hfDiff hFDiff hdf hdF hode_f hode_F

end

end BrezisOP6
