import BrezisOP6.InfinityDerivative
import BrezisOP6.ProfileBarrierFromODE

/-!
# The whole-space profile barrier with its far-field sign derived from the ODE

The far endpoint hypothesis of `profile_barrier_from_radial_ODE` is now
discharged by the unit-interval derivative estimate and the resulting
eventual positivity of `infinityW`.  The regular-origin start sign and the
ordinary profile regularity/positivity conditions remain explicit here.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

theorem profile_barrier_from_ode_with_origin_start
    (n : ℕ) {F y : ℝ → ℝ}
    (hn : 3 ≤ n)
    (hFone : Filter.Tendsto F Filter.atTop (𝓝 (1 : ℝ)))
    (hFdiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r : ℝ, 0 < r → y r = profileY F r)
    (hnear : ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → 0 < F r ^ 2 - y r)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hFlt : ∀ r : ℝ, 0 < r → F r < 1)
    (hFode : ∀ r, 0 < r →
      radialODEAt (n : ℝ) r (F r) (deriv F r)
        (deriv (deriv F) r)) :
    ∀ r : ℝ, 0 < r → 0 ≤ F r ^ 2 - y r := by
  have hW := infinityW_eventually_pos_from_radial_ode
    n hn hFone hFdiff hF2diff hFode
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hW
  have hfar : ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      0 < F r ^ 2 - y r := by
    refine ⟨max R₀ 1, ?_⟩
    intro r hr
    have hrpos : 0 < r := by
      have h1 : (1 : ℝ) ≤ r := (le_max_right R₀ 1).trans hr
      linarith
    have hR₀r : R₀ ≤ r := (le_max_left R₀ 1).trans hr
    simpa only [infinityW, hyMatch r hrpos] using hR₀ r hR₀r
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact profile_barrier_from_radial_ODE hnreal hFdiff hyDiff
    hyMatch hnear hfar hFpos hFlt
    (fun r hr => ⟨deriv (deriv F) r,
      (hF2diff r hr).hasDerivAt, hFode r hr⟩)

end

end BrezisOP6
