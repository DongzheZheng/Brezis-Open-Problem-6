import BrezisOP6.BridgePiconeIdentificationRightLimit
import BrezisOP6.PhysicalRadialZeroModeAnnular

/-!
# Quantitative transfer from the radial Picone form to the sphere mean

The bridge's scalar mean coefficient is `c=b/r` on positive radii.
The integrated bridge identity identifies its quadratic form with the
Picone density.  Consequently the positive contact estimate controls
the *actual* mean component in the angular bridge.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- A quantitative Picone estimate for the radial mean transfers without
loss to the scalar mean part of the spherical bridge. -/
theorem bridgeMean_integral_ge_picone_annular
    (m : ℕ) (f F b db c dc : ℝ → ℝ) (δ ρ R : ℝ)
    (hR : 0 < R) (hbR : b R = 0)
    (hc : ∀ r ∈ Ioo (0 : ℝ) R, c r = b r / r)
    (hdc : ∀ r ∈ Ioo (0 : ℝ) R,
      dc r = deriv (fun s => b s / s) r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (piconeWeightFromProfiles f F)
        (deriv (piconeWeightFromProfiles f F) r) r)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hfluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (bridgeOriginFlux m f F b) (uIcc ε R))
    (hfluxLim : Tendsto (bridgeOriginFlux m f F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hPicInt : IntervalIntegrable
      (profilePiconeDensity m f F b db) volume 0 R)
    (hfluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m f F b)) volume 0 R)
    (hPicone : ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          profilePiconeDensity m f F b db r) :
    ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          bridgeMeanDensity m (fun r => f r ^ 2 - F r ^ 2)
            c dc r := by
  have hmeanEq :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
          c dc r) =
      ∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => f s ^ 2 - F s ^ 2)
          (fun s => b s / s)
          (fun s => deriv (fun t => b t / t) s) r := by
    apply interval_integral_congr_interior
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := by
      simpa [uIoo_of_le hR.le] using hr
    simp only [bridgeMeanDensity, hc r hr', hdc r hr']
  have hident := bridgeMeanDensity_integral_eq_profilePiconeDensity_rightLimit
    m f F b db R hR hbR hh hb hfluxCont hfluxLim hPicInt hfluxInt
  obtain ⟨lam, hlam, hbound⟩ := hPicone
  refine ⟨lam, hlam, ?_⟩
  rw [hmeanEq, hident]
  exact hbound

/-- For the physical pair of radial profiles, the contact coefficient and
origin Picone factor are already certified.  Only the scalar mean's
ordinary differentiability, endpoint behavior, and flux integrability
remain in the hypotheses. -/
theorem PhysicalRadialData.bridgeMean_annular_l2
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (b db c dc : ℝ → ℝ) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hb : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt b (db r) r)
    (hbR : b R = 0)
    (hc : ∀ r ∈ Ioo (0 : ℝ) R, c r = b r / r)
    (hdc : ∀ r ∈ Ioo (0 : ℝ) R,
      dc r = deriv (fun s => b s / s) r)
    (hDint : IntervalIntegrable
      (profilePiconeDensity m p.f p.F b db) volume 0 R)
    (hBsqInt : IntervalIntegrable (fun r => b r ^ 2) volume δ ρ)
    (hPicFluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (profilePiconeBoundaryFlux m p.f p.F b)
        (uIcc ε R))
    (hPicFluxInt : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      IntervalIntegrable
        (deriv (profilePiconeBoundaryFlux m p.f p.F b))
        volume ε R)
    (hblim : ∃ B : ℝ,
      Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B))
    (hFluxCont : ∀ ε : ℝ, 0 < ε → ε ≤ R →
      ContinuousOn (bridgeOriginFlux m p.f p.F b) (uIcc ε R))
    (hFluxLim : Tendsto (bridgeOriginFlux m p.f p.F b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hFluxInt : IntervalIntegrable
      (deriv (bridgeOriginFlux m p.f p.F b)) volume 0 R) :
    ∃ lam : ℝ, 0 < lam ∧
      lam * (∫ r in δ..ρ, b r ^ 2) ≤
        ∫ r in (0 : ℝ)..R,
          bridgeMeanDensity m (fun r => p.f r ^ 2 - p.F r ^ 2)
            c dc r := by
  have hfDiff : Differentiable ℝ p.f :=
    fun r => (p.hfC2.of_le (by norm_num)).differentiable_one r
  have hFDiff : Differentiable ℝ p.F :=
    fun r => (p.hFC2.of_le (by norm_num)).differentiable_one r
  have hh (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (piconeWeightFromProfiles p.f p.F)
        (deriv (piconeWeightFromProfiles p.f p.F) r) r := by
    have hnum : DifferentiableAt ℝ
        (fun t => p.f t ^ 2 - p.F t ^ 2) r :=
      ((hfDiff r).pow 2).sub ((hFDiff r).pow 2)
    have hden : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) r :=
      differentiableAt_id.pow 2
    have hweightDiff : DifferentiableAt ℝ
        (piconeWeightFromProfiles p.f p.F) r := by
      simpa only [piconeWeightFromProfiles] using
        hnum.div hden (pow_ne_zero 2 (ne_of_gt hr.1))
    exact hweightDiff.hasDerivAt
  have hPicone := p.zero_mode_annular_l2 m R b db δ ρ
    hδ hδρ hρR hb hbR hDint hBsqInt
    hPicFluxCont hPicFluxInt hblim
  exact bridgeMean_integral_ge_picone_annular m p.f p.F b db c dc δ ρ R
    p.hR hbR hc hdc hh hb hFluxCont hFluxLim hDint hFluxInt hPicone

end

end BrezisOP6
