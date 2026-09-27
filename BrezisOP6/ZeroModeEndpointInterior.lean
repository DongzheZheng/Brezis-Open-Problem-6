import BrezisOP6.ZeroModeEndpoint
import BrezisOP6.ProfilePiconeIntervalInterior

/-!
# The regular-origin zero mode with an interior profile ODE

Picone integration on each `[δ,R]` uses the radial equations and second
derivatives only on `(δ,R)`.  A continuous endpoint flux is sufficient for
the finite-interval fundamental theorem.
-/

namespace BrezisOP6

open Filter Set
open scoped Topology

noncomputable section

theorem profilePicone_zero_mode_nonnegative_interior
    (m : ℕ) (f F b db f₂ F₂ : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R)
    (hFpos : ∀ r ∈ Set.Ioc 0 R, 0 < F r)
    (hMpos : ∀ r ∈ Set.Ioc 0 R, 0 < profileM f F r)
    (hfDiff : Differentiable ℝ f)
    (hFDiff : Differentiable ℝ F)
    (hdf : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv f) (f₂ r) r)
    (hdF : ∀ r ∈ Set.Ioo 0 R,
      HasDerivAt (deriv F) (F₂ r) r)
    (hode_f : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3) r (f r) (deriv f r) (f₂ r))
    (hode_F : ∀ r ∈ Set.Ioo 0 R,
      radialODEAt ((m : ℝ) + 3) r (F r) (deriv F r) (F₂ r))
    (hb : ∀ r ∈ Set.Ioo 0 R, HasDerivAt b (db r) r)
    (hS : ∀ r ∈ Set.Ioc 0 R,
      0 ≤ contactResidual r (profileT F r) (profileY F r)
        (profileK f F r ^ 2 - 1) (profileEta f F r))
    (hbR : b R = 0)
    (hDint : IntervalIntegrable (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hsq_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeSquare m f F b db)
        MeasureTheory.volume δ R)
    (hflux_cont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m f F b)
        (Set.uIcc δ R))
    (hflux_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m f F b))
        MeasureTheory.volume δ R)
    (hrem_int : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      IntervalIntegrable (profilePiconeRemainder m f F b)
        MeasureTheory.volume δ R)
    (hfactor : Filter.Tendsto (profilePiconeOriginFactor f F)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    0 ≤ ∫ r in (0 : ℝ)..R,
      profilePiconeDensity m f F b db r := by
  obtain ⟨B, hbRight⟩ := hblim
  have hfluxlim := profilePiconeBoundaryFlux_tendsto_zero_of_right_limit
    m f F b R B hR hFpos hMpos hfactor hbRight
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
    have hsubsetOpen : Set.uIoo δ R ⊆ Set.Ioo 0 R := by
      intro r hr
      have hrI : r ∈ Set.Ioo δ R := by
        simpa [Set.uIoo_of_le hδ.2] using hr
      exact ⟨lt_trans hδ.1 hrI.1, hrI.2⟩
    exact profilePicone_interval_lower_bound_interior m f F b db f₂ F₂ δ R
      hδ.1 hδ.2
      (fun r hr => hFpos r (hsubset hr))
      (fun r hr => hMpos r (hsubset hr))
      hfDiff hFDiff
      (fun r hr => hdf r (hsubsetOpen hr))
      (fun r hr => hdF r (hsubsetOpen hr))
      (fun r hr => hode_f r (hsubsetOpen hr))
      (fun r hr => hode_F r (hsubsetOpen hr))
      (fun r hr => hb r (hsubsetOpen hr))
      (fun r hr => hS r (hsubset hr))
      hbR
      (hsq_int δ hδ.1 hδ.2)
      (hflux_cont δ hδ.1 hδ.2)
      (hflux_int δ hδ.1 hδ.2)
      (hrem_int δ hδ.1 hδ.2)
  have hneglim : Filter.Tendsto
      (fun δ : ℝ => -profilePiconeBoundaryFlux m f F b δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hfluxlim.neg
  exact le_of_tendsto_of_tendsto hneglim hDlim hineq


end

end BrezisOP6
