import BrezisOP6.EnergyProfileOriginBounds
import BrezisOP6.EnergyQuotientFluxEnvelope

/-!
# Inner flux envelope from regular-origin profile data

The local numerical profile bounds needed for the quotient flux estimate
come from the positive-slope Taylor expansion, and the uniform numerator
bound comes from continuity at the origin.  The final interface exposes
neither the numerical constants nor the desired flux estimate as inputs.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- For every positive sequence converging to zero inside a common
profile/competitor neighborhood, the actual quotient field has a uniform
spherical inner-flux envelope tending to zero.  This directly supplies
`hBzero` and `hInnerBound` of `smooth_positiveBall_singleProfile_identity`.
-/
theorem quotient_inner_flux_envelope_of_localTaylor (m : ℕ)
    (p : ℝ → ℝ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (α A B R : ℝ)
    (hR : 0 < R) (hα : 0 < α)
    (hTaylor : RadialOriginTaylorOn p α A B R)
    (hw : ContinuousAt w 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
      ∀ (ρ : ℕ → ℝ),
        (∀ k, 0 < ρ k) →
        (∀ k, ρ k < δ) →
        Tendsto ρ atTop (𝓝 0) →
        ∃ fluxBound : ℕ → ℝ,
          Tendsto fluxBound atTop (𝓝 0) ∧
            ∀ k,
              ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
                |radialBoundaryFlux m p
                  (energyRaySq (m + 3)
                    (fun x => (p ‖x‖)⁻¹ • w x) ω) (ρ k)| ≤
                  fluxBound k := by
  obtain ⟨δp, Cdp, Cratio, Cp, hδp, hδpR,
      hCdp, hCratio, hCp, hpBounds⟩ :=
    radial_origin_local_flux_bounds_on hR hα hTaylor
  obtain ⟨δw, hδw, hwEnvelope⟩ :=
    quotient_inner_flux_envelope_of_continuity m p w hw
      Cdp Cratio Cp hCdp hCratio hCp
  refine ⟨min δp δw, lt_min hδp hδw,
    le_trans (min_le_left δp δw) hδpR, ?_⟩
  intro ρ hρpos hρsmall hρzero
  have hρp : ∀ k, ρ k < δp :=
    fun k => lt_of_lt_of_le (hρsmall k) (min_le_left δp δw)
  have hρw : ∀ k, ρ k < δw :=
    fun k => lt_of_lt_of_le (hρsmall k) (min_le_right δp δw)
  have hpne : ∀ k, p (ρ k) ≠ 0 :=
    fun k => (hpBounds (ρ k) (hρpos k) (hρp k)).1
  have hdp : ∀ k, |deriv p (ρ k)| ≤ Cdp :=
    fun k => (hpBounds (ρ k) (hρpos k) (hρp k)).2.1
  have hratio : ∀ k, |ρ k / p (ρ k)| ≤ Cratio :=
    fun k => (hpBounds (ρ k) (hρpos k) (hρp k)).2.2.1
  have hp : ∀ k, |p (ρ k)| ≤ Cp :=
    fun k => (hpBounds (ρ k) (hρpos k) (hρp k)).2.2.2
  obtain ⟨hflux, hboundZero⟩ :=
    hwEnvelope ρ hρpos hρw hρzero hpne hdp hratio hp
  exact ⟨quotientFluxEnvelope m w Cdp Cratio Cp ρ,
    hboundZero, hflux⟩

end

end BrezisOP6
