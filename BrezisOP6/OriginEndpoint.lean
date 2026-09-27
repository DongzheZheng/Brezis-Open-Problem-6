import Mathlib

/-!
# Regular radial endpoint terms

The zero-mode integration by parts produces a flux with the factor
`r^(n-2)`. For `n≥3`, this factor vanishes at the origin as soon as the
remaining factors have finite continuous limits. The smooth-profile
expansions needed to obtain those limits are separate obligations.
-/

namespace BrezisOP6

open scoped Topology

/-- A finite one-sided limit for the remaining flux factor suffices at the
regular radial origin.  No value or two-sided continuity at `r=0` is needed. -/
theorem zeroMode_origin_flux_tendsto_of_one_sided
    (m : ℕ) {h b : ℝ → ℝ} {H B : ℝ}
    (hh : Filter.Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 H))
    (hb : Filter.Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Filter.Tendsto (fun r : ℝ => r ^ (m + 1) * h r * b r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hr : Filter.Tendsto (fun r : ℝ => r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  convert ((hr.pow (m + 1)).mul hh).mul (hb.pow 2) using 1
  simp

/-- For `n=m+3`, the zero-mode boundary flux is
`r^(n-2) h(r) b(r)^2`, and vanishes at `r↓0` if `h,b` extend continuously. -/
theorem zeroMode_origin_flux_tendsto (m : ℕ) {h b : ℝ → ℝ}
    (hh : ContinuousAt h 0) (hb : ContinuousAt b 0) :
    Filter.Tendsto (fun r : ℝ => r ^ (m + 1) * h r * b r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hpow : ContinuousAt (fun r : ℝ => r ^ (m + 1)) 0 :=
    continuousAt_id.pow _
  have hflux : ContinuousAt (fun r : ℝ => r ^ (m + 1) * h r * b r ^ 2) 0 :=
    (hpow.mul hh).mul (hb.pow 2)
  have hlim : Filter.Tendsto (fun r : ℝ => r ^ (m + 1) * h r * b r ^ 2)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hflux.tendsto
  exact hlim.mono_left nhdsWithin_le_nhds

/-- A generic Picone endpoint flux. The paper's `psi` is `phi'/phi` and
has a continuous extension at zero. -/
theorem picone_origin_flux_tendsto (m : ℕ) {h b psi : ℝ → ℝ}
    (hh : ContinuousAt h 0) (hb : ContinuousAt b 0)
    (hpsi : ContinuousAt psi 0) :
    Filter.Tendsto (fun r : ℝ => r ^ (m + 2) * h r * psi r * b r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hpow : ContinuousAt (fun r : ℝ => r ^ (m + 2)) 0 :=
    continuousAt_id.pow _
  have hflux : ContinuousAt
      (fun r : ℝ => r ^ (m + 2) * h r * psi r * b r ^ 2) 0 :=
    (((hpow.mul hh).mul hpsi).mul (hb.pow 2))
  have hlim : Filter.Tendsto
      (fun r : ℝ => r ^ (m + 2) * h r * psi r * b r ^ 2)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hflux.tendsto
  exact hlim.mono_left nhdsWithin_le_nhds

end BrezisOP6
