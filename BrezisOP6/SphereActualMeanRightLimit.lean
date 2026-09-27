import BrezisOP6.SphereMeanUniformRightLimit
import BrezisOP6.EnergyActualScaledSphereUniform

/-!
# The actual finite-ball zero mode has a finite right trace

For a smooth numerator and a regular radial factor `f(r)=rH(r²)`, the
totalized spherical family has zero assigned at radius zero.  Its
regularized mean nevertheless has a finite right limit, determined by
the numerator's origin value.  This is the endpoint input required by
the finite-ball Picone theorem.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

theorem actual_finiteBallSphereRadialMean_right_limit
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f H : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hH : ContinuousAt H 0) (hH0 : H 0 ≠ 0)
    (hu : ContinuousAt u 0)
    (hf : ∀ s : ℝ, 0 < s → s ≤ R →
      f s = s * H (s ^ 2))
    (hfpos : ∀ s : ℝ, 0 < s → s ≤ R → 0 < f s)
    (hz : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (i : Fin n) :
    ∃ B : ℝ,
      Tendsto
        (vectorSphereRadialMean n
          (finiteBallSphereFamily n R
            (fun x => (f ‖x‖)⁻¹ • u x))
          (fun s k => finiteBallSphereFamily_memLp n R
            (fun x => (f ‖x‖)⁻¹ • u x) hz s k) i)
        (𝓝[>] (0 : ℝ)) (𝓝 B) := by
  let z : GLEuclidean n → GLEuclidean n :=
    fun x => (f ‖x‖)⁻¹ • u x
  let g := finiteBallSphereFamily n R z
  let hg := fun s k => finiteBallSphereFamily_memLp n R z hz s k
  let w : GLEuclidean n := (H 0)⁻¹ • u 0
  let g₀ : Metric.sphere (0 : GLEuclidean n) 1 → ℝ := fun _ => w i
  have hg₀ : MemLp g₀ 2 (unitSphereMeasure n) := by
    have hcont : Continuous g₀ := continuous_const
    exact hcont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hvec := actual_scaled_finiteBallSphereFamily_uniform_origin
    n R hR f H u hH hH0 hu hf hfpos
  have huniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ ω : Metric.sphere (0 : GLEuclidean n) 1,
          ‖r • (g r ω) i - g₀ ω‖ < ε := by
    intro ε hε
    filter_upwards [hvec ε hε] with r hr
    intro ω
    have hcoord := PiLp.norm_apply_le
      (r • g r ω - w) i
    have heq : (r • g r ω - w) i =
        r • (g r ω) i - g₀ ω := by simp [g₀]
    rw [heq] at hcoord
    exact lt_of_le_of_lt hcoord (by simpa [g, z, w] using hr ω)
  refine ⟨sphereMeanCoefficient n (hg₀.toLp g₀), ?_⟩
  exact vectorSphereRadialMean_tendsto_of_uniform_scaled
    n g hg i g₀ hg₀ huniform

end

end BrezisOP6
