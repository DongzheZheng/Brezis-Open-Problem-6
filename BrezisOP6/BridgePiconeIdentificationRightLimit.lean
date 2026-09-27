import BrezisOP6.BridgeFluxRightEndpoint

/-!
# The Picone bridge with a one-sided origin trace

The actual regularized spherical mean is totalized to zero at radius zero,
although its right limit may be nonzero.  Integration by parts therefore
uses annuli and passes to the origin, rather than assuming continuity of the
mean or of the elementary bridge flux on the closed ball.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

private theorem interval_integral_left_tendsto_of_integrable_bridge
    (g : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hInt : IntervalIntegrable g volume 0 R) :
    Tendsto (fun δ : ℝ => ∫ r in δ..R, g r)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..R, g r)) := by
  have hcontRight : ContinuousOn (fun δ : ℝ => ∫ r in R..δ, g r)
      (Icc (0 : ℝ) R) := by
    simpa [uIcc_of_le hR.le] using
      (intervalIntegral.continuousOn_primitive_interval'
        hInt (show R ∈ uIcc (0 : ℝ) R by
          simpa [uIcc_of_le hR.le] using
            (Set.right_mem_Icc.mpr hR.le)))
  have hcontLeft : ContinuousOn (fun δ : ℝ => ∫ r in δ..R, g r)
      (Icc (0 : ℝ) R) := by
    convert hcontRight.neg using 1
    ext δ
    exact intervalIntegral.integral_symm R δ
  have hwithin : (𝓝[>] (0 : ℝ)) ≤
      (𝓝[Icc (0 : ℝ) R] (0 : ℝ)) :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT hR)
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) R := ⟨le_rfl, hR.le⟩
  exact (hcontLeft.continuousWithinAt h0mem).tendsto.mono_left hwithin

/-- Picone integrability follows from integrability of the actual mean
density and the elementary flux derivative; it is not an independent
endpoint assumption. -/
theorem profilePiconeDensity_intervalIntegrable_of_mean_flux
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hh : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hmeanInt : IntervalIntegrable
      (bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
        (fun x => b x / x) (fun x => deriv (fun s => b s / s) x))
      volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R) :
    IntervalIntegrable
      (profilePiconeDensity m f F b db) volume 0 R := by
  have hRnull : ∀ᵐ r : ℝ ∂volume, r ≠ R := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton R : volume {R} = 0)
  have hInterior : ∀ᵐ r : ℝ ∂volume.restrict (uIoc (0 : ℝ) R),
      r ∈ Ioo (0 : ℝ) R := by
    rw [uIoc_of_le hR.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hRnull] with r hr hrNe
    exact ⟨hr.1, lt_of_le_of_ne hr.2 hrNe⟩
  apply (hmeanInt.add hfluxInt).congr_ae
  filter_upwards [hInterior] with r hr
  have hid := bridgeMeanDensity_eq_picone_sub_flux_deriv
    m f F b db r hr.1 (hh r hr) (hb r hr)
  linarith

/-- Annular FTC with a finite right origin flux.  A two-sided derivative at
the outer radius and a closed-interval continuity hypothesis at zero are
both unnecessary. -/
theorem bridgeMeanDensity_integral_eq_profilePiconeDensity_rightLimit
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ)
    (hR : 0 < R) (hbR : b R = 0)
    (hh : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hfluxCont : ∀ δ : ℝ, 0 < δ → δ ≤ R →
      ContinuousOn (bridgeOriginFlux m f F b) (uIcc δ R))
    (hfluxLim : Tendsto (bridgeOriginFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hPicInt : IntervalIntegrable
      (profilePiconeDensity m f F b db) volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R) :
    (∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
        (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
      ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r := by
  let Flux := bridgeOriginFlux m f F b
  have hfluxDiff : ∀ r ∈ Ioo (0 : ℝ) R,
      DifferentiableAt ℝ Flux r := by
    intro r hr
    have hweight := hh r hr
    have hbr := hb r hr
    dsimp [Flux, bridgeOriginFlux]
    exact (((hasDerivAt_pow (m + 1) r).mul hweight).mul
      (hbr.pow 2)).differentiableAt
  have hFTCevent :
      (fun δ : ℝ => ∫ r in δ..R, deriv Flux r) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ => Flux R - Flux δ) := by
    filter_upwards [Ioc_mem_nhdsGT hR] with δ hδ
    have hDiff : ∀ r ∈ uIoo δ R,
        DifferentiableAt ℝ Flux r := by
      intro r hr
      have hr' : r ∈ Ioo δ R := by
        simpa [uIoo_of_le hδ.2] using hr
      exact hfluxDiff r ⟨lt_trans hδ.1 hr'.1, hr'.2⟩
    have hAnnInt : IntervalIntegrable (deriv Flux) volume δ R := by
      apply hfluxInt.mono_set
      intro r hr
      have hr' : r ∈ Icc δ R := by
        simpa [uIcc_of_le hδ.2] using hr
      simpa [uIcc_of_le hR.le] using
        (show r ∈ Icc (0 : ℝ) R from
          ⟨le_trans hδ.1.le hr'.1, hr'.2⟩)
    exact intervalIntegral.integral_deriv_eq_sub_uIoo
      (hfluxCont δ hδ.1 hδ.2) hDiff
      hAnnInt
  have hFTC :
      (∫ r in (0 : ℝ)..R, deriv Flux r) = Flux R := by
    have hIntLim := interval_integral_left_tendsto_of_integrable_bridge
      (deriv Flux) R hR hfluxInt
    have hFluxLim : Tendsto (fun δ : ℝ => Flux R - Flux δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (Flux R)) := by
      convert tendsto_const_nhds.sub hfluxLim using 1 <;> simp
    exact tendsto_nhds_unique hIntLim
      (hFluxLim.congr' hFTCevent.symm)
  have hcongr :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
          (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r - deriv Flux r := by
    apply interval_integral_congr_interior
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := by
      simpa [uIoo_of_le hR.le] using hr
    exact bridgeMeanDensity_eq_picone_sub_flux_deriv m f F b db r
      hr'.1 (hh r hr') (hb r hr')
  have hfluxR : Flux R = 0 := by
    simp [Flux, bridgeOriginFlux, hbR]
  rw [hcongr, intervalIntegral.integral_sub hPicInt hfluxInt,
    hFTC, hfluxR]
  ring

end

end BrezisOP6
