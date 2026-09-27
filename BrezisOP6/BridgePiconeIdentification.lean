import BrezisOP6.BridgeDecomposition
import BrezisOP6.ZeroMode

/-!
# Identifying the bridge's spherical mean with the radial Picone density

For a mean coefficient `c=b/r` and contrast `d=f²-F²`, the zero-mode
integration by parts changes the mean part of the multidimensional bridge
into `profilePiconeDensity`.  The pointwise identity holds away from the
origin.  The integral proof ignores the single point at zero and uses the
ordinary fundamental theorem for the endpoint flux.  The flux regularity
at zero and integrability are explicit analytic interfaces.
-/

namespace BrezisOP6

noncomputable section

/-- The zero-mode integration-by-parts flux. -/
def bridgeOriginFlux (m : ℕ) (f F b : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 1) * piconeWeightFromProfiles f F r * b r ^ 2

/-- The mean density is the Picone density minus the derivative of its
boundary flux at every positive radius. -/
theorem bridgeMeanDensity_eq_picone_sub_flux_deriv
    (m : ℕ) (f F b db : ℝ → ℝ) (r : ℝ)
    (hr : 0 < r)
    (hh : HasDerivAt (piconeWeightFromProfiles f F)
      (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : HasDerivAt b (db r) r) :
    bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
        (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r =
      profilePiconeDensity m f F b db r -
        deriv (bridgeOriginFlux m f F b) r := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hd : f r ^ 2 - F r ^ 2 =
      r ^ 2 * piconeWeightFromProfiles f F r := by
    unfold piconeWeightFromProfiles
    field_simp [hrne]
  have hraw := zeroMode_pointwise m
    (piconeWeightFromProfiles f F) b r
    (deriv (piconeWeightFromProfiles f F) r) (db r) hr hh hb
  have hquot : deriv (fun s => b s / s) r =
      db r / r - b r / r ^ 2 := by
    have hderiv := hb.div (hasDerivAt_id r) hrne
    convert hderiv.deriv using 1
    simp only [id_eq]
    field_simp [hrne]
  simpa only [bridgeMeanDensity, profilePiconeDensity, bridgeOriginFlux, hd,
    hquot]
    using hraw

/-- The exact integral identification used by the abstract quadratic bridge.
`hfluxDiff` includes the origin; it follows from regular profile expansions
for an actual smooth competitor, but is not proved by this algebraic module. -/
theorem bridgeMeanDensity_integral_eq_profilePiconeDensity
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hbR : b R = 0)
    (hh : ∀ r ∈ Set.Ioc 0 R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Set.Ioc 0 R, HasDerivAt b (db r) r)
    (hfluxDiff : ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ (bridgeOriginFlux m f F b) r)
    (hPicInt : IntervalIntegrable
      (profilePiconeDensity m f F b db)
      MeasureTheory.volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b))
      MeasureTheory.volume 0 R) :
    (∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
        (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
      ∫ r in (0 : ℝ)..R, profilePiconeDensity m f F b db r := by
  have hcongr :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
          (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r -
            deriv (bridgeOriginFlux m f F b) r := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hR]
    filter_upwards [] with r hr
    exact bridgeMeanDensity_eq_picone_sub_flux_deriv m f F b db r
      hr.1 (hh r hr) (hb r hr)
  have hFTC :
      (∫ r in (0 : ℝ)..R, deriv (bridgeOriginFlux m f F b) r) =
        bridgeOriginFlux m f F b R - bridgeOriginFlux m f F b 0 :=
    intervalIntegral.integral_deriv_eq_sub hfluxDiff hfluxInt
  have hfluxR : bridgeOriginFlux m f F b R = 0 := by
    simp [bridgeOriginFlux, hbR]
  have hflux0 : bridgeOriginFlux m f F b 0 = 0 := by
    simp [bridgeOriginFlux]
  rw [hcongr, intervalIntegral.integral_sub hPicInt hfluxInt,
    hFTC, hfluxR, hflux0]
  ring

end

end BrezisOP6
