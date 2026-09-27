import BrezisOP6.EnergyBallLimit

/-!
# Angular integration of a uniform inner-flux bound

The sphere measure is finite.  Consequently, a common scalar envelope that
vanishes at the origin controls the integral of the inner boundary flux.
This is the missing passage from pointwise angular estimates to a genuine
boundary integral limit.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem sphere_integral_uniform_flux_tendsto_zero (n : ℕ)
    (F : ℕ → Metric.sphere (0 : GLEuclidean n) 1 → ℝ)
    (B : ℕ → ℝ)
    (hBzero : Tendsto B atTop (𝓝 0))
    (hbound : ∀ k ω, |F k ω| ≤ B k) :
    Tendsto (fun k => ∫ ω, F k ω ∂(unitSphereMeasure n))
      atTop (𝓝 0) := by
  have hnorm (k : ℕ) :
      ‖∫ ω, F k ω ∂(unitSphereMeasure n)‖ ≤
        B k * (unitSphereMeasure n).real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hbound k ω
  have hscaled : Tendsto
      (fun k => B k * (unitSphereMeasure n).real Set.univ)
      atTop (𝓝 0) := by
    simpa using hBzero.mul_const ((unitSphereMeasure n).real Set.univ)
  have hnormzero : Tendsto
      (fun k => ‖∫ ω, F k ω ∂(unitSphereMeasure n)‖)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hscaled (fun k => norm_nonneg _) hnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormzero

end

end BrezisOP6
