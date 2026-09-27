import BrezisOP6.EnergyQuotientPuncturedC1

/-!
# The genuine right trace of the rescaled spherical quotient

The totalized finite-ball spherical family is assigned zero at radius
zero.  Its rescaled positive-radius trace has, in general, a nonzero
right limit.  The correct comparison is with the smooth expression
`u(rω)/H(r²)` supplied by the regular radial factor `f(r)=rH(r²)`.
-/

namespace BrezisOP6

open Metric

noncomputable section

/-- The rescaled singular quotient is exactly a smooth radial-factor
quotient on every positive sphere. -/
theorem rescaled_radialQuotient_ray_eq_factor
    (n : ℕ) (R : ℝ) (f H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hf : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s)
    (ω : Metric.sphere (0 : GLEuclidean n) 1) :
    r • ((f ‖energySphereRay n ω r‖)⁻¹ •
      u (energySphereRay n ω r)) =
      (H (r ^ 2))⁻¹ • u (energySphereRay n ω r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hHne : H (r ^ 2) ≠ 0 := by
    intro hzero
    have hfr := hf r hr hrR
    rw [hzero, mul_zero] at hfr
    exact (ne_of_gt (hfpos r hr hrR)) hfr
  rw [energySphereRay_norm n ω r hr.le, hf r hr hrR]
  simp only [smul_smul]
  congr 1
  field_simp [hrne, hHne]

/-- Continuity of the physical numerator at the origin is automatically
uniform over all directions on each sufficiently small Euclidean sphere.
This is the main input for the `L²` and mean right-trace limits. -/
theorem continuousAt_origin_uniform_on_spheres
    (n : ℕ) (u : GLEuclidean n → GLEuclidean n)
    (hu : ContinuousAt u 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 ≤ r → r < δ →
        ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ‖u (energySphereRay n ω r) - u 0‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ :=
    (Metric.continuousAt_iff.mp hu) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ ω
  have hray : ‖energySphereRay n ω r‖ = r :=
    energySphereRay_norm n ω r hr
  have hdist : dist (energySphereRay n ω r) 0 < δ := by
    simpa only [dist_zero_right, hray] using hrδ
  simpa only [dist_eq_norm] using hcont hdist

end

end BrezisOP6
