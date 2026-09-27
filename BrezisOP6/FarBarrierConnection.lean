import BrezisOP6.InfinitySign
import BrezisOP6.ProfileBarrierFromODE

/-!
# Feeding the far-field expansion into the global profile barrier

The expansion of the entire-space profile is an analytic input.  Its exact
leading coefficient is already checked in `InfinitySign`; this file converts
eventual positivity into the half-line endpoint hypothesis of
`profile_barrier_from_radial_ODE`.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

theorem profile_far_sign_from_scaled_expansion
    (n : ℕ) {F y : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hyMatch : ∀ r : ℝ, 0 < r → y r = profileY F r)
    (hU : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (F r - 1))
      Filter.atTop (𝓝 (-infinityCoeff2 n)))
    (hV : Filter.Tendsto
      (fun r : ℝ => r ^ 4 * (F r - 1) +
        infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (infinityCoeff4 n)))
    (hQ : Filter.Tendsto
      (fun r : ℝ => r ^ 5 * deriv F r -
        2 * infinityCoeff2 n * r ^ 2)
      Filter.atTop (𝓝 (-4 * infinityCoeff4 n))) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → 0 < F r ^ 2 - y r := by
  have hpos := infinityW_eventually_pos n hn hU hV hQ
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hpos
  refine ⟨max R₀ 1, ?_⟩
  intro r hr
  have hrpos : 0 < r := by
    have h1 : (1 : ℝ) ≤ r := (le_max_right R₀ 1).trans hr
    linarith
  have hR₀r : R₀ ≤ r := (le_max_left R₀ 1).trans hr
  have hW : 0 < infinityW F r := hR₀ r hR₀r
  simpa only [infinityW, hyMatch r hrpos] using hW

end

end BrezisOP6
