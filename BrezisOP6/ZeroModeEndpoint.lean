import BrezisOP6.ProfilePiconeInterval
import BrezisOP6.OriginEndpoint

/-!
# The zero-mode Picone inequality at the regular origin

The finite-interval profile identity controls the quadratic density on
`[δ,R]` by its inner boundary flux.  The profile flux has exactly the
`r^(m+1) h(r) b(r)^2` form of `OriginEndpoint` after cancellation of
the positive Picone multiplier.  Interval integrability of the density
then makes its left-endpoint integral continuous at zero.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The factor multiplying `r^(m+1)b²` in the profile Picone flux. -/
def profilePiconeOriginFactor (f F : ℝ → ℝ) (r : ℝ) : ℝ :=
  piconeWeightFromProfiles f F r *
    piconeMultiplierLogSlope
      (profileY F r) (profileK f F r) (profileEta f F r)

/-- The finite-radius Picone boundary term is the regular-origin flux
from `OriginEndpoint` whenever the multiplier is nonzero. -/
theorem profilePiconeBoundaryFlux_eq_origin_form
    (m : ℕ) (f F b : ℝ → ℝ) (r : ℝ)
    (hphi : piconeMultiplierFromProfiles f F r ≠ 0) :
    profilePiconeBoundaryFlux m f F b r =
      r ^ (m + 1) * profilePiconeOriginFactor f F r * b r ^ 2 := by
  unfold profilePiconeBoundaryFlux radialPiconeTheta
    profilePiconeOriginFactor
  field_simp [hphi]

/-- The profile boundary flux vanishes at the regular origin.  Only a
finite one-sided limit of the combined factor `h·ψ` is required. -/
theorem profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
    (m : ℕ) (f F b : ℝ → ℝ) (R B : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hfactor : Filter.Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hb : Filter.Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Filter.Tendsto (profilePiconeBoundaryFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hEq : (profilePiconeBoundaryFlux m f F b) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => r ^ (m + 1) *
        profilePiconeOriginFactor f F r * b r ^ 2) := by
    filter_upwards [Ioc_mem_nhdsGT hR] with r hr
    have hphi : piconeMultiplierFromProfiles f F r ≠ 0 :=
      ne_of_gt (piconeMultiplier_pos f F r hr.1
        (hFpos r hr) (hMpos r hr))
    exact profilePiconeBoundaryFlux_eq_origin_form m f F b r hphi
  have hlim := zeroMode_origin_flux_tendsto_of_one_sided m
    hfactor hb
  exact hlim.congr' hEq.symm

/-- This continuous-at-zero specialization is retained for the older
interfaces.  Actual smooth competitors may have a nonzero right limit
for the regularized mean even when its totalized value at zero is zero. -/
theorem profilePiconeBoundaryFlux_tendsto_zero
    (m : ℕ) (f F b : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hfactor : Filter.Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hb : ContinuousAt b 0) :
    Filter.Tendsto (profilePiconeBoundaryFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  exact profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
    m f F b R (b 0) hR hFpos hMpos hfactor
    (hb.tendsto.mono_left nhdsWithin_le_nhds)

/-- Interval integrability on `[0,R]` gives the required continuity of
the left-truncated density integral.  No separate integral-limit axiom is
used. -/
theorem profilePiconeDensity_left_tendsto
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R) :
    Filter.Tendsto
      (fun δ : ℝ => ∫ r in δ..R,
        profilePiconeDensity m f F b db r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r)) := by
  have hcontRight : ContinuousOn
      (fun δ : ℝ => ∫ r in R..δ,
        profilePiconeDensity m f F b db r)
      (Set.Icc 0 R) := by
    simpa [Set.uIcc_of_le hR.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        hDint (show R ∈ Set.uIcc (0 : ℝ) R by
          simpa [Set.uIcc_of_le hR.le] using
            (Set.right_mem_Icc.mpr hR.le)))
  have hcontLeft : ContinuousOn
      (fun δ : ℝ => ∫ r in δ..R,
        profilePiconeDensity m f F b db r)
      (Set.Icc 0 R) := by
    convert hcontRight.neg using 1
    ext δ
    exact intervalIntegral.integral_symm R δ
  have hwithin : (𝓝[>] (0 : ℝ)) ≤
      (𝓝[Set.Icc (0 : ℝ) R] (0 : ℝ)) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT hR)
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 R := ⟨le_rfl, hR.le⟩
  exact (hcontLeft.continuousWithinAt h0mem).tendsto.mono_left hwithin

/-- The zero-mode quadratic density is nonnegative on the full radial
interval.  The square, flux derivative, and remainder need only be
integrable on each regular `[δ,R]`; the density itself must be interval
integrable down to zero to pass to the endpoint. -/
theorem profilePicone_zero_mode_nonnegative
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3) r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioc 0 R,
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r) (F₂ r))
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hS : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r))
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
  have hfluxlim := profilePiconeBoundaryFlux_tendsto_zero
    m f F b R hR hFpos hMpos hfactor hbcont
  have hDlim := profilePiconeDensity_left_tendsto
    m f F b db R hR hDint
  have hineq : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      -profilePiconeBoundaryFlux m f F b δ ≤
        ∫ r in δ..R, profilePiconeDensity m f F b db r := by
    filter_upwards [Ioc_mem_nhdsGT hR] with δ hδ
    have hsubset : Set.uIcc δ R ⊆ Set.Ioc 0 R := by
      intro r hr
      have hrI : r ∈ Set.Icc δ R := by
        simpa [Set.uIcc_of_le hδ.2] using hr
      exact ⟨lt_of_lt_of_le hδ.1 hrI.1, hrI.2⟩
    exact profilePicone_interval_lower_bound m f F b db f₂ F₂ δ R
      hδ.1 hδ.2
      (fun r hr => hFpos r (hsubset hr))
      (fun r hr => hMpos r (hsubset hr))
      hfDiff hFDiff
      (fun r hr => hdf r (hsubset hr))
      (fun r hr => hdF r (hsubset hr))
      (fun r hr => hode_f r (hsubset hr))
      (fun r hr => hode_F r (hsubset hr))
      (fun r hr => hb r (hsubset hr))
      (fun r hr => hS r (hsubset hr))
      hbR
      (hsq_int δ hδ.1 hδ.2)
      (hflux_int δ hδ.1 hδ.2)
      (hrem_int δ hδ.1 hδ.2)
  have hneglim : Filter.Tendsto
      (fun δ : ℝ => -profilePiconeBoundaryFlux m f F b δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hfluxlim.neg
  exact le_of_tendsto_of_tendsto hneglim hDlim hineq

end

end BrezisOP6
