import BrezisOP6.BridgePiconeIdentification
import BrezisOP6.EnergyIBPInterior

/-!
# Zero-mode bridge identification with endpoint continuity

The endpoint flux is only required to be continuous on the closed radius
interval.  Its derivative and the profile identities are needed on the open
interval.  In particular, no two-sided derivative at the outer radius and
no derivative at the singular origin is part of this identity.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

/-- The spherical-mean bridge integral equals the Picone density integral
under interior differentiability and continuity of the endpoint flux. -/
theorem bridgeMeanDensity_integral_eq_profilePiconeDensity_interior
    (m : ℕ) (f F b db : ℝ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hbR : b R = 0)
    (hh : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hfluxCont : ContinuousOn (bridgeOriginFlux m f F b)
      (uIcc (0 : ℝ) R))
    (hPicInt : IntervalIntegrable
      (profilePiconeDensity m f F b db) volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R) :
    (∫ r in (0 : ℝ)..R,
      bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
        (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
      ∫ r in (0 : ℝ)..R,
        profilePiconeDensity m f F b db r := by
  have hcongr :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun x => f x ^ 2 - F x ^ 2)
          (fun x => b x / x) (fun x => deriv (fun s => b s / s) x) r) =
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r -
            deriv (bridgeOriginFlux m f F b) r := by
    apply interval_integral_congr_interior
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := by
      simpa [uIoo_of_le hR] using hr
    exact bridgeMeanDensity_eq_picone_sub_flux_deriv m f F b db r
      hr'.1 (hh r hr') (hb r hr')
  have hFluxDiff : ∀ r ∈ uIoo (0 : ℝ) R,
      DifferentiableAt ℝ (bridgeOriginFlux m f F b) r := by
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := by
      simpa [uIoo_of_le hR] using hr
    have hweight := hh r hr'
    have hbr := hb r hr'
    unfold bridgeOriginFlux
    exact (((hasDerivAt_pow (m + 1) r).mul hweight).mul
      (hbr.pow 2)).differentiableAt
  have hFTC :
      (∫ r in (0 : ℝ)..R,
        deriv (bridgeOriginFlux m f F b) r) =
        bridgeOriginFlux m f F b R -
          bridgeOriginFlux m f F b 0 :=
    intervalIntegral.integral_deriv_eq_sub_uIoo
      hfluxCont hFluxDiff hfluxInt
  have hfluxR : bridgeOriginFlux m f F b R = 0 := by
    simp [bridgeOriginFlux, hbR]
  have hflux0 : bridgeOriginFlux m f F b 0 = 0 := by
    simp [bridgeOriginFlux]
  rw [hcongr, intervalIntegral.integral_sub hPicInt hfluxInt,
    hFTC, hfluxR, hflux0]
  ring

end

end BrezisOP6
