import BrezisOP6.EnergyOpenBall
import BrezisOP6.EnergyCompetitorFlux

/-!
# A concrete inner-flux envelope for a smooth competitor

For `z=w/p`, continuity of `w` at the origin supplies one angularly uniform
numerator bound.  Combined with elementary profile bounds at the radii of
an exhaustion, this gives exactly the vanishing numeric envelope required
by the direct single-profile theorem.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

def quotientFluxEnvelope (m : ℕ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (Cdp Cratio Cp : ℝ) (ρ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ρ k ^ (m + 1) * Cdp * Cratio * (‖w 0‖ ^ 2 + 1) +
    ρ k ^ (m + 2) * Cp * Cdp

/-- The concrete competitor/profile data discharge both the uniform
inner-flux bound and its vanishing limit, without postulating any energy
identity or interchange of an angular integral and a pointwise limit. -/
theorem quotient_inner_flux_envelope_of_continuity (m : ℕ)
    (p : ℝ → ℝ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hw : ContinuousAt w 0)
    (Cdp Cratio Cp : ℝ)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio) (hCp : 0 ≤ Cp) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ρ : ℕ → ℝ),
        (∀ k, 0 < ρ k) →
        (∀ k, ρ k < δ) →
        Tendsto ρ atTop (𝓝 0) →
        (∀ k, p (ρ k) ≠ 0) →
        (∀ k, |deriv p (ρ k)| ≤ Cdp) →
        (∀ k, |ρ k / p (ρ k)| ≤ Cratio) →
        (∀ k, |p (ρ k)| ≤ Cp) →
        (∀ k,
          ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
            |radialBoundaryFlux m p
              (energyRaySq (m + 3)
                (fun x => (p ‖x‖)⁻¹ • w x) ω) (ρ k)| ≤
              quotientFluxEnvelope m w Cdp Cratio Cp ρ k) ∧
          Tendsto (quotientFluxEnvelope m w Cdp Cratio Cp ρ)
            atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hwBound⟩ :=
    energyRayNumerator_uniform_bound (m + 3) w hw
  refine ⟨δ, hδ, ?_⟩
  intro ρ hρpos hρsmall hρzero hpne hdp hratio hp
  constructor
  · intro k ω
    rw [radialBoundaryFlux_quotient_eq_origin m p w ω
      (ρ k) (hρpos k).le]
    exact radialOriginFlux_uniform_bound m p
      (fun ω r => ‖w (energySphereRay (m + 3) ω r)‖ ^ 2)
      Cdp Cratio (‖w 0‖ ^ 2 + 1) Cp
      hCdp hCratio hCp (ρ k) (hρpos k).le (hpne k)
      (hdp k) (hratio k)
      (fun ω => hwBound (ρ k) (hρpos k) (hρsmall k) ω)
      (hp k) ω
  · have hcont : ContinuousAt
        (fun r : ℝ =>
          r ^ (m + 1) * Cdp * Cratio * (‖w 0‖ ^ 2 + 1) +
            r ^ (m + 2) * Cp * Cdp) 0 := by fun_prop
    have h := hcont.tendsto.comp hρzero
    simpa [quotientFluxEnvelope,
      zero_pow (by omega : m + 1 ≠ 0),
      zero_pow (by omega : m + 2 ≠ 0)] using h

end

end BrezisOP6
