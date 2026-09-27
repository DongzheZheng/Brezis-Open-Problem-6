import BrezisOP6.ProfileBarrierGlobal
import BrezisOP6.FlowFromProfiles

/-!
# The profile barrier from the original radial ODE

The logarithmic slope `1-rF'/F` is singular as a literal quotient at
`r=0`.  We therefore use a differentiable extension `y` which agrees with
that quotient for positive radii.  The near-origin and far-field signs of
`F²-y` are the explicit asymptotic inputs; both flow equations are derived
from the original radial ODE.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- The radial identity for `rho=F²` follows from the definition of `y`. -/
theorem profileRho_flow_from_F
    (F : ℝ → ℝ) (r F₁ : ℝ)
    (hFpos : 0 < F r) (hF : HasDerivAt F F₁ r) :
    r * deriv (fun x => F x ^ 2) r =
      2 * F r ^ 2 * (1 - profileY F r) := by
  have hsq : HasDerivAt (fun x => F x ^ 2) (2 * F r * F₁) r := by
    simpa using hF.pow 2
  rw [hsq.deriv]
  unfold profileY
  rw [hF.deriv]
  field_simp [ne_of_gt hFpos]
  ring

/-- The whole-space bound `F²≥1-rF'/F` on every positive radius.  The
external inputs are regularity/positivity of the profile and the two endpoint
signs; the internal crossing argument is the verified `ProfileBarrierGlobal`
theorem. -/
theorem profile_barrier_from_radial_ODE
    {F y : ℝ → ℝ} {n : ℝ}
    (hn : 3 ≤ n)
    (hFdiff : Differentiable ℝ F)
    (hyDiff : Differentiable ℝ y)
    (hyMatch : ∀ r : ℝ, 0 < r → y r = profileY F r)
    (hnear : ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → 0 < F r ^ 2 - y r)
    (hfar : ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      0 < F r ^ 2 - y r)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hFlt : ∀ r : ℝ, 0 < r → F r < 1)
    (hODE : ∀ r : ℝ, 0 < r →
      ∃ F₂ : ℝ,
        HasDerivAt (deriv F) F₂ r ∧
        radialODEAt n r (F r) (deriv F r) F₂) :
    ∀ r : ℝ, 0 < r → 0 ≤ F r ^ 2 - y r := by
  let rho : ℝ → ℝ := fun r => F r ^ 2
  have hrhoDiff : Differentiable ℝ rho := by
    intro r
    exact (hFdiff r).pow 2
  have hrho0 : ∀ r : ℝ, 0 < r → 0 < rho r := by
    intro r hr
    exact sq_pos_of_pos (hFpos r hr)
  have hrho1 : ∀ r : ℝ, 0 < r → rho r < 1 := by
    intro r hr
    dsimp [rho]
    have hp := hFpos r hr
    have hl := hFlt r hr
    nlinarith
  have hrhoFlow : ∀ r : ℝ, 0 < r →
      r * deriv rho r = 2 * rho r * (1 - y r) := by
    intro r hr
    simpa only [rho, ← hyMatch r hr] using
      profileRho_flow_from_F F r (deriv F r)
        (hFpos r hr) (hFdiff r).hasDerivAt
  have hyFlow : ∀ r : ℝ, 0 < r →
      r * deriv y r = y r ^ 2 - n * y r +
        r ^ 2 - r ^ 2 * rho r := by
    intro r hr
    obtain ⟨F₂, hF₂, hode⟩ := hODE r hr
    have hevent : y =ᶠ[𝓝 r] profileY F := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact hyMatch x hx
    have hdy : deriv y r = deriv (profileY F) r :=
      hevent.deriv_eq
    have hflow := profileY_flow n F r (deriv F r) F₂
      (hFpos r hr) (hFdiff r).hasDerivAt hF₂ hode
    rw [hdy]
    rw [hyMatch r hr]
    dsimp [rho]
    unfold profileT at hflow
    convert hflow using 1
    ring
  have hbarrier := profile_barrier_global
    (rho := rho) (y := y) hn hrhoDiff hyDiff
    (by simpa only [profileW, rho] using hnear)
    (by simpa only [profileW, rho] using hfar)
    hrho0 hrho1 hrhoFlow hyFlow
  intro r hr
  simpa only [profileW, rho] using hbarrier r hr

end

end BrezisOP6
