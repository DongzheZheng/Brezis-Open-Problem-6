import BrezisOP6.EnergyFactorTraceUniform
import BrezisOP6.SphereFiniteFamily

/-!
# Uniform right trace of the actual finite-ball quotient family

The family is totalized at radius zero, but its positive-radius rescaling
has a nontrivial, direction-independent limit determined by the regular
radial factor and the numerator's value at the origin.
-/

namespace BrezisOP6

open Filter Metric
open scoped Topology

noncomputable section

theorem actual_scaled_finiteBallSphereFamily_uniform_origin
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hH : ContinuousAt H 0) (hH0 : H 0 ≠ 0)
    (hu : ContinuousAt u 0)
    (hf : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ‖r • finiteBallSphereFamily n R
              (fun x => (f ‖x‖)⁻¹ • u x) r ω -
            (H 0)⁻¹ • u 0‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ :=
    radial_factor_quotient_uniform_origin n H u hH hH0 hu ε hε
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < min δ R :=
    ((eventually_lt_nhds (lt_min hδ hR)).filter_mono
      nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrsmall
  intro ω
  have hrR : r < R := lt_of_lt_of_le hrsmall (min_le_right _ _)
  have hrδ : r < δ := lt_of_lt_of_le hrsmall (min_le_left _ _)
  have hfamily : finiteBallSphereFamily n R
      (fun x => (f ‖x‖)⁻¹ • u x) r ω =
      (f ‖energySphereRay n ω r‖)⁻¹ •
        u (energySphereRay n ω r) := by
    simpa only [energySphereRay] using
      finiteBallSphereFamily_interior n R
        (fun x => (f ‖x‖)⁻¹ • u x) r ⟨hr, hrR⟩ ω
  rw [hfamily, rescaled_radialQuotient_ray_eq_factor
    n R f H u r hr hrR.le hf hfpos ω]
  exact hnear r hr.le hrδ ω

end

end BrezisOP6
