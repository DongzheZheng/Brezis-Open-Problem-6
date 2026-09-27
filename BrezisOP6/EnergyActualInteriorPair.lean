import BrezisOP6.EnergyAnnularFluxRegularity
import BrezisOP6.EnergySharedFluxEnvelope
import BrezisOP6.EnergyRadiusExhaustion
import BrezisOP6.EnergyQuotientPuncturedC1
import BrezisOP6.SphereActualFluxIntegrable

/-!
# Both interior energy identities for one smooth competitor

The two radial profiles act on the same quotient z=u/f.  From the
origin Taylor data and ordinary C¹ regularity, this module chooses one
common punctured-ball exhaustion, obtains both vanishing inner-flux
envelopes, proves annular FTC regularity, and constructs the two complete
interior-energy data records.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

theorem actual_smooth_competitor_has_paired_interior_data
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (f F Hf HF : ℝ → ℝ)
    (β α Af Bf AF BF : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hfTaylor : RadialOriginTaylorOn f β Af Bf R)
    (hFTaylor : RadialOriginTaylorOn F α AF BF R)
    (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (hβ : 0 < β) (hα : 0 < α) (hHf0 : Hf 0 = β)
    (hfC1 : ContDiff ℝ 1 f) (hFC1 : ContDiff ℝ 1 F)
    (hdfC1 : ContDiff ℝ 1 (deriv f))
    (hdFC1 : ContDiff ℝ 1 (deriv F))
    (huC1 : ContDiff ℝ 1 u)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hfPos : ∀ r, 0 < r → r ≤ R → 0 < f r)
    (hFle : ∀ r, 0 < r → r ≤ R →
      0 ≤ F r ∧ F r ≤ f r)
    (hfFactor : ∀ r, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (f r) (deriv f r) (deriv (deriv f) r))
    (hFODE : ∀ r, 0 < r → r < R →
      radialODEAt ((m : ℝ) + 3) r
        (F r) (deriv F r) (deriv (deriv F) r)) :
    ∃ (ρ BfFlux BFFlux : ℕ → ℝ),
      SmoothProfileBallInteriorData m f
        (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
        R ρ BfFlux ∧
      SmoothProfileBallInteriorData m F
        (fun x : GLEuclidean (m + 3) => (f ‖x‖)⁻¹ • u x)
        R ρ BFFlux := by
  obtain ⟨δf, hδf, hδfR, hEnvelopef⟩ :=
    quotient_inner_flux_envelope_of_localTaylor
      m f u β Af Bf R hR hβ hfTaylor huC1.continuous.continuousAt
  obtain ⟨δF, hδF, hδFR, hEnvelopeF⟩ :=
    shared_quotient_inner_flux_envelope_of_localTaylor
      m f F u β α Af Bf AF BF R hR hβ hα
      hfTaylor hFTaylor hfPos hFle huC1.continuous.continuousAt
  let a : ℝ := min δf δF / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have haδf : a < δf := by
    dsimp [a]
    have hmin : 0 < min δf δF := lt_min hδf hδF
    have hle : min δf δF ≤ δf := min_le_left _ _
    linarith
  have haδF : a < δF := by
    dsimp [a]
    have hmin : 0 < min δf δF := lt_min hδf hδF
    have hle : min δf δF ≤ δF := min_le_right _ _
    linarith
  have haR : a ≤ R :=
    (le_of_lt haδf).trans hδfR
  let ρ : ℕ → ℝ := canonicalEnergyRadius a
  have hρpos : ∀ k, 0 < ρ k :=
    canonicalEnergyRadius_pos a ha
  have hρsmallf : ∀ k, ρ k < δf :=
    fun k => lt_of_le_of_lt (canonicalEnergyRadius_le a ha k) haδf
  have hρsmallF : ∀ k, ρ k < δF :=
    fun k => lt_of_le_of_lt (canonicalEnergyRadius_le a ha k) haδF
  have hρle : ∀ k, ρ k ≤ R :=
    fun k => (canonicalEnergyRadius_le a ha k).trans haR
  have hρanti : Antitone ρ :=
    canonicalEnergyRadius_antitone a ha
  have hρzero : Tendsto ρ atTop (𝓝 0) :=
    canonicalEnergyRadius_tendsto_zero a
  obtain ⟨BfFlux, hBf0, hBfBound⟩ :=
    hEnvelopef ρ hρpos hρsmallf hρzero
  obtain ⟨BFFlux, hBF0, hBFBound⟩ :=
    hEnvelopeF ρ hρpos hρsmallF hρzero
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  have hz : ContDiffOn ℝ 1 z
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} :=
    radialQuotient_contDiffOn_puncturedBall
      (m + 3) R f u hfC1 hfPos huC1.contDiffOn
  have hopen : IsOpen {x : GLEuclidean (m + 3) |
      0 < ‖x‖ ∧ ‖x‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hzdiff : ∀ ω : Metric.sphere
      (0 : GLEuclidean (m + 3)) 1,
      ∀ r, 0 < r → r < R →
        DifferentiableAt ℝ z (energySphereRay (m + 3) ω r) := by
    intro ω r hr hrR
    have hx : energySphereRay (m + 3) ω r ∈
        {x : GLEuclidean (m + 3) |
          0 < ‖x‖ ∧ ‖x‖ < R} := by
      simpa only [Set.mem_setOf_eq,
        energySphereRay_norm (m + 3) ω r hr.le] using
        (show 0 < r ∧ r < R from ⟨hr, hrR⟩)
    exact (hz.differentiableOn_one).differentiableAt
      (hopen.mem_nhds hx)
  have hfluxf (k : ℕ)
      (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) :=
    radialBoundaryFlux_shared_quotient_annulus_regular
      m R (ρ k) f f u ω (hρpos k) (hρle k)
      hfC1 hdfC1 hfC1 huC1 hfPos
  have hfluxF (k : ℕ)
      (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1) :=
    radialBoundaryFlux_shared_quotient_annulus_regular
      m R (ρ k) F f u ω (hρpos k) (hρle k)
      hFC1 hdFC1 hfC1 huC1 hfPos
  have hfData : SmoothProfileBallInteriorData m f z R ρ BfFlux :=
    smoothProfileBallInteriorData_of_taylor_C1
      m R hR f Hf β Af Bf u ρ BfFlux
      hρpos hρle hρanti hρzero hBf0
      (fun r _ _ => hdfC1.differentiable_one r)
      hzdiff hfODE
      (fun k ω => (hfluxf k ω).1)
      (fun k ω => (hfluxf k ω).2)
      hBfBound hf0 hβ hfTaylor hfC1 huC1 hfPos hHf hfFactor
  have hFData : SmoothProfileBallInteriorData m F z R ρ BFFlux :=
    smoothProfileBallInteriorData_second_shared_quotient_of_taylor_C1
      m R hR f F Hf HF β Af Bf u ρ BFFlux
      hρpos hρle hρanti hρzero hBF0
      (fun r _ _ => hdFC1.differentiable_one r)
      hFODE
      (fun k ω => (hfluxF k ω).1)
      (fun k ω => (hfluxF k ω).2)
      hBFBound hF0 hβ hHf0 hfTaylor
      hfC1 hFC1 huC1 hfPos hFle hHf hHF hfFactor hFFactor
  exact ⟨ρ, BfFlux, BFFlux, hfData, hFData⟩

end

end BrezisOP6
