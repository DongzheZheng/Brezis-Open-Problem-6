import BrezisOP6.ProfileFlow
import BrezisOP6.ProfileGlobal

/-!
# Global whole-space profile barrier

The local `J` crossing certificate is combined with the negative-component
exclusion to prove `rho ≥ y` globally.  The only nonlocal inputs are positive
signs of `rho-y` near the origin and at large radii; these arise from the
profile's asymptotic expansions.  The flow equations and contact derivative
are not assumed as conclusions.
-/

namespace BrezisOP6

noncomputable section

/-- Whole-space profile inequality `rho≥y` from the two profile flows and
the endpoint signs.  In the paper, `rho=F²` and `y=1-rF'/F`. -/
theorem profile_barrier_global
    {rho y : ℝ → ℝ} {n : ℝ}
    (hn : 3 ≤ n)
    (hrhoDiff : Differentiable ℝ rho)
    (hyDiff : Differentiable ℝ y)
    (hnear : ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → 0 < profileW rho y r)
    (hfar : ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      0 < profileW rho y r)
    (hrho0 : ∀ r : ℝ, 0 < r → 0 < rho r)
    (hrho1 : ∀ r : ℝ, 0 < r → rho r < 1)
    (hrhoFlow : ∀ r : ℝ, 0 < r →
      r * deriv rho r = 2 * rho r * (1 - y r))
    (hyFlow : ∀ r : ℝ, 0 < r →
      r * deriv y r = y r ^ 2 - n * y r +
        r ^ 2 - r ^ 2 * rho r) :
    ∀ r : ℝ, 0 < r → 0 ≤ profileW rho y r := by
  let W : ℝ → ℝ := profileW rho y
  let J : ℝ → ℝ := fun r => profileJ n (rho r) r
  have hWdiff : Differentiable ℝ W := by
    intro r
    exact (hrhoDiff r).sub (hyDiff r)
  have hJdiff : Differentiable ℝ J := by
    intro r
    unfold J profileJ
    fun_prop
  have hWflow : ∀ r : ℝ, 0 < r → W r = 0 →
      r * deriv W r = -J r := by
    intro r hr hzero
    exact profileW_flow_at_zero
      (hrhoDiff r).hasDerivAt (hyDiff r).hasDerivAt
      (hrhoFlow r hr) (hyFlow r hr) hzero
  have hJbarrier : ∀ r : ℝ, 0 < r → J r = 0 →
      W r ≤ 0 → 0 < deriv J r := by
    intro r hr hzero hWle
    have hroy : rho r ≤ y r := by
      unfold W profileW at hWle
      linarith
    exact profileJ_deriv_pos_at_zero hn hr
      (hrhoDiff r).hasDerivAt (hrhoFlow r hr)
      (hrho0 r hr) (hrho1 r hr) hroy hzero
  exact nonnegative_of_profile_contact_flow_global
    hWdiff hJdiff hnear hfar hWflow hJbarrier

end

end BrezisOP6
