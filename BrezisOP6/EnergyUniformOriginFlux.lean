import BrezisOP6.EnergyOriginFlux

/-!
# Uniform decay of the inner energy flux

The fixed-ray limit in `EnergyOriginFlux` is insufficient for integration
over the sphere.  Here a single bound on the squared numerator along all
directions gives an angularly uniform estimate.  The estimate is phrased for
an arbitrary index type, so it applies in particular to the unit sphere.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- A common bound for the inner flux on every ray.  In dimension `m+3`,
the envelope is of order `r^(m+1)` and `r^(m+2)` and hence vanishes at the
origin.  The profile and numerator bounds are genuinely independent of the
angular parameter. -/
theorem radialOriginFlux_uniform_bound (m : ℕ) {Ω : Type*}
    (p : ℝ → ℝ) (W : Ω → ℝ → ℝ)
    (Cdp Cratio CW Cp : ℝ)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCp : 0 ≤ Cp)
    (r : ℝ) (hr : 0 ≤ r) (hp_ne : p r ≠ 0)
    (hdp : |deriv p r| ≤ Cdp)
    (hratio : |r / p r| ≤ Cratio)
    (hW : ∀ ω : Ω, |W ω r| ≤ CW)
    (hp : |p r| ≤ Cp) (ω : Ω) :
    |radialOriginFlux m p (W ω) r| ≤
      r ^ (m + 1) * Cdp * Cratio * CW +
        r ^ (m + 2) * Cp * Cdp := by
  rw [radialOriginFlux_eq_regular m p (W ω) r hp_ne]
  have hpow1 : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hpow2 : 0 ≤ r ^ (m + 2) := pow_nonneg hr _
  calc
    |r ^ (m + 1) * deriv p r * (r / p r) * W ω r -
        r ^ (m + 2) * p r * deriv p r| ≤
      |r ^ (m + 1) * deriv p r * (r / p r) * W ω r| +
        |r ^ (m + 2) * p r * deriv p r| := by
      simpa using abs_sub_le
        (r ^ (m + 1) * deriv p r * (r / p r) * W ω r)
        0 (r ^ (m + 2) * p r * deriv p r)
    _ = r ^ (m + 1) * |deriv p r| * |r / p r| * |W ω r| +
          r ^ (m + 2) * |p r| * |deriv p r| := by
      simp only [abs_mul, abs_of_nonneg hpow1, abs_of_nonneg hpow2]
    _ ≤ r ^ (m + 1) * Cdp * Cratio * CW +
          r ^ (m + 2) * Cp * Cdp := by
      gcongr
      exact hW ω

/-- The inner flux tends to zero *uniformly over every angular direction*.
All eventual bounds use the same constants for every index.  In particular,
this can be applied to the actual unit sphere without an unjustified swap of
pointwise limits and a sphere integral. -/
theorem radialOriginFlux_uniform_tendsto_zero (m : ℕ) {Ω : Type*}
    (p : ℝ → ℝ) (W : Ω → ℝ → ℝ)
    (Cdp Cratio CW Cp : ℝ)
    (hCdp : 0 ≤ Cdp) (hCratio : 0 ≤ Cratio)
    (hCp : 0 ≤ Cp)
    (hp_ne : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r ≠ 0)
    (hdp : ∀ᶠ r in 𝓝[>] (0 : ℝ), |deriv p r| ≤ Cdp)
    (hratio : ∀ᶠ r in 𝓝[>] (0 : ℝ), |r / p r| ≤ Cratio)
    (hW : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ ω : Ω, |W ω r| ≤ CW)
    (hp : ∀ᶠ r in 𝓝[>] (0 : ℝ), |p r| ≤ Cp) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ ω : Ω, |radialOriginFlux m p (W ω) r| < ε := by
  let envelope : ℝ → ℝ := fun r =>
    r ^ (m + 1) * Cdp * Cratio * CW +
      r ^ (m + 2) * Cp * Cdp
  have hcont : ContinuousAt envelope 0 := by
    dsimp [envelope]
    fun_prop
  have henv : Tendsto envelope (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto envelope (𝓝[>] (0 : ℝ)) (𝓝 (envelope 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [envelope, zero_pow (by omega : m + 1 ≠ 0),
      zero_pow (by omega : m + 2 ≠ 0)] using h
  intro ε hε
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), envelope r < ε :=
    henv.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hp_ne, hdp, hratio, hW, hp,
    hsmall] with r hr hne hdp' hratio' hW' hp' hsmall' ω
  exact lt_of_le_of_lt
    (radialOriginFlux_uniform_bound m p W Cdp Cratio CW Cp
      hCdp hCratio hCp r hr.le hne hdp' hratio' hW' hp' ω)
    hsmall'

end

end BrezisOP6
