import BrezisOP6.SphereMeanRightLimit

/-!
# Uniform spherical traces converge in finite-measure `L²`

This elementary interface converts an epsilon bound uniform in the
angular variable into convergence of the actual `Lp` representatives.
It is the analytic step linking the regular-origin quotient identity to
the right trace of the spherical mean.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem tendsto_L2_of_uniform_pointwise
    {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ]
    (g : ℝ → S → ℝ) (g₀ : S → ℝ)
    (hg : ∀ r, MemLp (g r) 2 μ)
    (hg₀ : MemLp g₀ 2 μ)
    (huniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ ω : S,
        ‖g r ω - g₀ ω‖ < ε) :
    Tendsto (fun r => (hg r).toLp (g r))
      (𝓝[>] (0 : ℝ))
      (𝓝 (hg₀.toLp g₀)) := by
  let K : NNReal :=
    (measureUnivNNReal μ) ^ (((2 : ENNReal).toReal)⁻¹)
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / ((K : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [huniform η hη] with r hr
  have hAe : ∀ᵐ ω ∂μ,
      ‖((hg r).toLp (g r) - hg₀.toLp g₀) ω‖ ≤ η := by
    filter_upwards [Lp.coeFn_sub ((hg r).toLp (g r))
      (hg₀.toLp g₀), (hg r).coeFn_toLp,
      hg₀.coeFn_toLp] with ω hsub hgr hg0r
    simpa only [hsub, Pi.sub_apply, hgr, hg0r] using
      le_of_lt (hr ω)
  have hBound := Lp.norm_le_of_ae_bound
    (p := (2 : ENNReal)) (μ := μ)
    (f := (hg r).toLp (g r) - hg₀.toLp g₀)
    hη.le hAe
  have hBound' :
      ‖(hg r).toLp (g r) - hg₀.toLp g₀‖ ≤ (K : ℝ) * η := by
    simpa only [K] using hBound
  rw [dist_eq_norm]
  calc
    ‖(hg r).toLp (g r) - hg₀.toLp g₀‖ ≤ (K : ℝ) * η := hBound'
    _ < ε := by
      dsimp [η]
      have hden : 0 < (K : ℝ) + 1 := by positivity
      have hfrac : (K : ℝ) / ((K : ℝ) + 1) < 1 :=
        (div_lt_iff₀ hden).2 (by linarith)
      calc
        (K : ℝ) * (ε / ((K : ℝ) + 1)) =
            ε * ((K : ℝ) / ((K : ℝ) + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := by ring

end

end BrezisOP6
