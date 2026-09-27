import Mathlib

/-!
# Vanishing of the radial inner-boundary flux in dimension at least three

The apparent singularity in `|z|²=|w|²/p²` is treated algebraically before
taking a limit.  Writing the dimension as `m+3` exposes the vanishing factor
`r^(m+1)`.  The hypotheses are exactly finite one-sided limits of `r/p`,
`p'`, `p`, and the squared norm of `w` along a fixed ray.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- The inner flux after substituting `s=|w|²/p²`; `W` stands for `|w|²`
along a fixed ray. -/
def radialOriginFlux (m : ℕ) (p W : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (m + 2) * p r * deriv p r * (W r / p r ^ 2 - 1)

/-- The singular quotient cancels one power of `p`; this is the algebraic
reason why the inner surface flux is `O(r^(n-2))`. -/
theorem radialOriginFlux_eq_regular (m : ℕ) (p W : ℝ → ℝ)
    (r : ℝ) (hp : p r ≠ 0) :
    radialOriginFlux m p W r =
      r ^ (m + 1) * deriv p r * (r / p r) * W r -
        r ^ (m + 2) * p r * deriv p r := by
  unfold radialOriginFlux
  have hrpow : r ^ (m + 2) = r ^ (m + 1) * r := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
  rw [hrpow]
  field_simp [hp]

/-- Along every fixed ray, the inner flux tends to zero at the origin for
all dimensions `m+3 ≥ 3`.  No boundedness of `w/p` is assumed. -/
theorem radialOriginFlux_tendsto_zero (m : ℕ) (p W : ℝ → ℝ)
    (A B C : ℝ)
    (hp_ne : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r ≠ 0)
    (h_ratio : Tendsto (fun r : ℝ => r / p r) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (h_dp : Tendsto (deriv p) (𝓝[>] (0 : ℝ)) (𝓝 B))
    (h_p : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_W : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    Tendsto (radialOriginFlux m p W) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hm1 : m + 1 ≠ 0 := by omega
  have hm2 : m + 2 ≠ 0 := by omega
  have hpow1 : Tendsto (fun r : ℝ => r ^ (m + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_pow hm1] using hr0.pow (m + 1)
  have hpow2 : Tendsto (fun r : ℝ => r ^ (m + 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_pow hm2] using hr0.pow (m + 2)
  have h_regular : Tendsto
      (fun r : ℝ =>
        r ^ (m + 1) * deriv p r * (r / p r) * W r -
          r ^ (m + 2) * p r * deriv p r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (((hpow1.mul h_dp).mul h_ratio).mul h_W).sub
      ((hpow2.mul h_p).mul h_dp) using 1 <;> simp
  apply Tendsto.congr' _ h_regular
  filter_upwards [hp_ne] with r hpr
  exact (radialOriginFlux_eq_regular m p W r hpr).symm

end

end BrezisOP6
