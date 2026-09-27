import BrezisOP6.EnergyBallIdentity
import BrezisOP6.EnergyUniformOriginFlux

/-!
# A smooth competitor supplies the angular numerator bound

Continuity at the origin bounds the squared norm of a competitor uniformly
along all sufficiently short unit-sphere rays.  The quotient-field flux on
an annulus is then exactly the regularized flux used at the origin.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- A single neighborhood of the origin controls the squared norm of a
competitor on *every* unit-sphere ray.  Only continuity at the origin is
required; no global boundedness or compactness assumption is hidden. -/
theorem energyRayNumerator_uniform_bound (n : ℕ)
    (w : GLEuclidean n → GLEuclidean n)
    (hw : ContinuousAt w 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
          |‖w (energySphereRay n ω r)‖ ^ 2| ≤ ‖w 0‖ ^ 2 + 1 := by
  have hcont : ContinuousAt (fun x : GLEuclidean n => ‖w x‖ ^ 2) 0 :=
    hw.norm.pow 2
  have hlt : ‖w (0 : GLEuclidean n)‖ ^ 2 < ‖w 0‖ ^ 2 + 1 := by linarith
  have hmem : {x : GLEuclidean n | ‖w x‖ ^ 2 < ‖w 0‖ ^ 2 + 1} ∈
      𝓝 (0 : GLEuclidean n) :=
    hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ ω
  have hx : energySphereRay n ω r ∈ Metric.ball (0 : GLEuclidean n) δ := by
    simpa [Metric.mem_ball, energySphereRay_norm n ω r hr.le] using hrδ
  have hbound := hball hx
  simpa [abs_of_nonneg (sq_nonneg (‖w (energySphereRay n ω r)‖))] using
    (le_of_lt hbound)

/-- With `z=w/p`, the annulus boundary flux is definitionally the same
physical term as the regularized origin flux.  The equality uses only
`r≥0`, through `‖rω‖=r`; it does not require the profile ODE. -/
theorem radialBoundaryFlux_quotient_eq_origin (m : ℕ)
    (p : ℝ → ℝ)
    (w : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (r : ℝ) (hr : 0 ≤ r) :
    radialBoundaryFlux m p
      (energyRaySq (m + 3)
        (fun x => (p ‖x‖)⁻¹ • w x) ω) r =
      radialOriginFlux m p
        (fun t => ‖w (energySphereRay (m + 3) ω t)‖ ^ 2) r := by
  have hnorm := energySphereRay_norm (m + 3) ω r hr
  have hsq : ‖(p r)⁻¹ • w (energySphereRay (m + 3) ω r)‖ ^ 2 =
      ‖w (energySphereRay (m + 3) ω r)‖ ^ 2 / p r ^ 2 := by
    simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_eq_mul_inv]
    ring
  simp only [radialBoundaryFlux, radialOriginFlux, energyRaySq, hnorm, hsq]

end

end BrezisOP6
