import BrezisOP6.ProfileBarrierAlgebra

/-!
# Differential identities for the whole-space profile barrier

With `rho = F²` and `W = rho-y`, the paper's first-order flow gives the
derivatives of `J` and `W`.  The algebraic positivity certificate from
`ProfileBarrierAlgebra` then forces `J` to cross upward at any zero in the
region `rho ≤ y < 1`.
-/

namespace BrezisOP6

noncomputable section

/-- The discrepancy whose nonnegativity is the profile bound `F² ≥ y`. -/
def profileW (rho y : ℝ → ℝ) (r : ℝ) : ℝ := rho r - y r

/-- The raw derivative of the auxiliary `J`.  The radial ODE enters only
in the subsequent flow substitution. -/
theorem profileJ_hasDerivAt {n r rho₁ : ℝ} {rho : ℝ → ℝ}
    (hrho : HasDerivAt rho rho₁ r) :
    HasDerivAt (fun s => profileJ n (rho s) s)
      (2 * r * (1 - rho r) -
        (r ^ 2 + n + 2 - 6 * rho r) * rho₁) r := by
  have hleft : HasDerivAt (fun s => s ^ 2 * (1 - rho s))
      (2 * r * (1 - rho r) - r ^ 2 * rho₁) r := by
    convert ((hasDerivAt_id r).pow 2).mul
      ((hasDerivAt_const r (1 : ℝ)).sub hrho) using 1
    simp
    ring
  have hlin : HasDerivAt (fun s => n + 2 - 3 * rho s)
      (-3 * rho₁) r := by
    convert (hasDerivAt_const r (n + 2)).sub
      ((hasDerivAt_const r (3 : ℝ)).mul hrho) using 1
    ring
  have hright : HasDerivAt (fun s => rho s * (n + 2 - 3 * rho s))
      (rho₁ * (n + 2 - 6 * rho r)) r := by
    convert hrho.mul hlin using 1
    ring
  unfold profileJ
  convert hleft.sub hright using 1
  ring

/-- Substitution of `r rho' = 2 rho (1-y)` into the raw derivative of `J`.
The conclusion uses the exact `profileJRate` already certified in
`ProfileBarrierAlgebra`. -/
theorem profileJ_flow_rate {n r rho₁ y : ℝ} {rho : ℝ → ℝ}
    (hrho : HasDerivAt rho rho₁ r)
    (hrho_flow : r * rho₁ = 2 * rho r * (1 - y)) :
    r * deriv (fun s => profileJ n (rho s) s) r =
      profileJRate n (rho r) y r := by
  rw [(profileJ_hasDerivAt hrho).deriv]
  unfold profileJRate
  calc
    r * (2 * r * (1 - rho r) -
      (r ^ 2 + n + 2 - 6 * rho r) * rho₁) =
      2 * r ^ 2 * (1 - rho r) -
        (r ^ 2 + n + 2 - 6 * rho r) * (r * rho₁) := by ring
    _ = 2 * r ^ 2 * (1 - rho r) -
        (r ^ 2 + n + 2 - 6 * rho r) *
          (2 * rho r * (1 - y)) := by rw [hrho_flow]

/-- The discrepancy `W=rho-y` has derivative `rho'-y'`. -/
theorem profileW_hasDerivAt {r rho₁ y₁ : ℝ}
    {rho y : ℝ → ℝ}
    (hrho : HasDerivAt rho rho₁ r)
    (hy : HasDerivAt y y₁ r) :
    HasDerivAt (profileW rho y) (rho₁ - y₁) r := by
  unfold profileW
  exact hrho.sub hy

/-- At a zero of `W`, the two profile flows identify its derivative with
`-J`.  The `y` flow is `r y'=y²-n y+r²-r² rho`. -/
theorem profileW_flow_at_zero {n r rho₁ y₁ : ℝ}
    {rho y : ℝ → ℝ}
    (hrho : HasDerivAt rho rho₁ r)
    (hy : HasDerivAt y y₁ r)
    (hrho_flow : r * rho₁ = 2 * rho r * (1 - y r))
    (hy_flow : r * y₁ = (y r) ^ 2 - n * y r +
      r ^ 2 - r ^ 2 * rho r)
    (hW : profileW rho y r = 0) :
    r * deriv (profileW rho y) r = -profileJ n (rho r) r := by
  have hyρ : y r = rho r := by
    unfold profileW at hW
    linarith
  rw [(profileW_hasDerivAt hrho hy).deriv]
  rw [hyρ] at hrho_flow hy_flow
  calc
    r * (rho₁ - y₁) = r * rho₁ - r * y₁ := by ring
    _ = 2 * rho r * (1 - rho r) -
      ((rho r) ^ 2 - n * rho r + r ^ 2 - r ^ 2 * rho r) := by
        rw [hrho_flow, hy_flow]
    _ = -profileJ n (rho r) r := by unfold profileJ; ring

/-- At any putative critical zero of `J` in the barrier region, its
ordinary radial derivative is strictly positive: `J` crosses upward. -/
theorem profileJ_deriv_pos_at_zero {n r rho₁ : ℝ}
    {rho y : ℝ → ℝ}
    (hn : 3 ≤ n) (hr : 0 < r)
    (hrho : HasDerivAt rho rho₁ r)
    (hrho_flow : r * rho₁ = 2 * rho r * (1 - y r))
    (hrho0 : 0 < rho r) (hrho1 : rho r < 1)
    (hroy : rho r ≤ y r)
    (hJ : profileJ n (rho r) r = 0) :
    0 < deriv (fun s => profileJ n (rho s) s) r := by
  have hrate : 0 < profileJRate n (rho r) (y r) r :=
    profileJRate_pos_at_zero hn hrho0 hrho1 hroy hJ
  have hflow := profileJ_flow_rate (n := n) (y := y r) hrho hrho_flow
  nlinarith

end

end BrezisOP6
