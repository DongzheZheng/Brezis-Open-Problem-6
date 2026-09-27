import BrezisOP6.PhysicalRadialZeroModeFixed
import BrezisOP6.BridgeMeanPiconeQuantitative

/-! Fixed annular contact coefficient for the actual spherical mean. -/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem PhysicalRadialData.bridgeMean_annular_l2_fixed
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (b db c dc : ℝ → ℝ) (δ ρ lam : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρR : ρ < R)
    (hlam : 0 < lam)
    (hLamBound : ∀ r ∈ Icc δ ρ,
      lam ≤ profilePiconeRemainder m p.f p.F (fun _ => 1) r)
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
  have hPicone := p.zero_mode_annular_l2_fixed
    m R b db δ ρ lam hδ hδρ hρR hb hbR hDint hBsqInt
    hPicFluxCont hPicFluxInt hblim hlam hLamBound
  have hmeanEq :
      (∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => p.f s ^ 2 - p.F s ^ 2)
          c dc r) =
      ∫ r in (0 : ℝ)..R,
        bridgeMeanDensity m (fun s => p.f s ^ 2 - p.F s ^ 2)
          (fun s => b s / s)
          (fun s => deriv (fun t => b t / t) s) r := by
    apply interval_integral_congr_interior
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) R := by
      simpa [uIoo_of_le p.hR.le] using hr
    simp only [bridgeMeanDensity, hc r hr', hdc r hr']
  have hident := bridgeMeanDensity_integral_eq_profilePiconeDensity_rightLimit
    m p.f p.F b db R p.hR hbR hh hb hFluxCont hFluxLim hDint hFluxInt
  rw [hmeanEq, hident]
  exact hPicone

end

end BrezisOP6
