import BrezisOP6.Contact
import BrezisOP6.FirstContact

/-!
# From the profile flow to a forbidden first contact

The contact polynomial controls an algebraic drift. This file identifies that
drift with the derivative of the actual residual along the logarithmic-radius
profile flow, derives M = k² - 1 from k, and rules out a first zero approached
through positive residual values. The small-radius positivity from the
profile expansion is a separate analytic input.
-/

namespace BrezisOP6

noncomputable section

/-- The residual along a trajectory of the four primary profile variables. -/
def residualAlong (r t y k eta : ℝ → ℝ) (s : ℝ) : ℝ :=
  contactResidual (r s) (t s) (y s) ((k s) ^ 2 - 1) (eta s)

/-- Equation (3.5) implies the exact contact derivative formula.
Here s is logarithmic radius, so d/ds equals r d/dr. The evolution of
M = k² - 1 follows from the evolution of k rather than being postulated. -/
theorem residualAlong_hasDerivAt_of_flow
    {r t y k eta : ℝ → ℝ} {s n : ℝ}
    (hr : HasDerivAt r (r s) s)
    (ht : HasDerivAt t (t s * (2 - y s)) s)
    (hy : HasDerivAt y
      (y s ^ 2 - n * y s + r s ^ 2 - t s ^ 2) s)
    (hk : HasDerivAt k (((k s) ^ 2 - 1) * eta s) s)
    (heta : HasDerivAt eta
      (k s * t s ^ 2 - (n - 2 * y s) * eta s -
        2 * k s * eta s ^ 2) s) :
    HasDerivAt (residualAlong r t y k eta)
      (2 * contactDrift n (r s) (t s) (y s) (k s)
        ((k s) ^ 2 - 1) (eta s)) s := by
  have hM : HasDerivAt (fun z => (k z) ^ 2 - 1)
      (2 * k s * ((k s) ^ 2 - 1) * eta s) s := by
    convert (hk.pow 2).sub_const 1 using 1
    dsimp
    ring
  exact contactResidual_hasDerivAt_logRadius hr ht hy hM heta

/-- On the auxiliary domain of the paper, every zero of the residual
along a profile-flow trajectory has strictly positive derivative. -/
theorem residualAlong_deriv_pos_at_zero
    {r t y k eta : ℝ → ℝ} {s n X q : ℝ}
    (hr : HasDerivAt r (r s) s)
    (ht : HasDerivAt t (t s * (2 - y s)) s)
    (hy : HasDerivAt y
      (y s ^ 2 - n * y s + r s ^ 2 - t s ^ 2) s)
    (hk : HasDerivAt k (((k s) ^ 2 - 1) * eta s) s)
    (heta : HasDerivAt eta
      (k s * t s ^ 2 - (n - 2 * y s) * eta s -
        2 * k s * eta s ^ 2) s)
    (hn : 2 < n)
    (hzero : residualAlong r t y k eta s = 0)
    (hM : 0 < (k s) ^ 2 - 1)
    (hy0 : 0 < y s) (hy1 : y s < 1)
    (hk0 : 0 < k s) (heta0 : 0 < eta s)
    (hetaSmall : (eta s) ^ 2 < (r s) ^ 2 / 2)
    (hX0 : 0 < X) (hX1 : X < 1)
    (hchi : ((k s) ^ 2 - 1) * eta s = k s * X * y s)
    (hq : y s ≤ q) (htrel : (t s) ^ 2 = (r s) ^ 2 * q) :
    0 < deriv (residualAlong r t y k eta) s := by
  have hflow :=
    residualAlong_hasDerivAt_of_flow hr ht hy hk heta
  have hS : contactResidual (r s) (t s) (y s)
      ((k s) ^ 2 - 1) (eta s) = 0 := hzero
  have hk2 : (k s) ^ 2 = 1 + ((k s) ^ 2 - 1) := by ring
  have hpositive :=
    contactDrift_pos_from_bounds hn hS hM hy0 hy1 hk0 heta0
      hk2 hetaSmall hX0 hX1 hchi hq htrel
  rw [hflow.deriv]
  positivity

/-- A first zero cannot occur once the profile flow and auxiliary
inequalities hold at that zero. Positivity to its left is an explicit
hypothesis, supplied in the paper by the origin expansion and the
definition of the first contact. -/
theorem residualAlong_no_first_zero
    {r t y k eta : ℝ → ℝ} {a s n X q : ℝ}
    (ha : a < s)
    (hleft : ∀ z, a < z → z < s →
      0 < residualAlong r t y k eta z)
    (hr : HasDerivAt r (r s) s)
    (ht : HasDerivAt t (t s * (2 - y s)) s)
    (hy : HasDerivAt y
      (y s ^ 2 - n * y s + r s ^ 2 - t s ^ 2) s)
    (hk : HasDerivAt k (((k s) ^ 2 - 1) * eta s) s)
    (heta : HasDerivAt eta
      (k s * t s ^ 2 - (n - 2 * y s) * eta s -
        2 * k s * eta s ^ 2) s)
    (hn : 2 < n)
    (hzero : residualAlong r t y k eta s = 0)
    (hM : 0 < (k s) ^ 2 - 1)
    (hy0 : 0 < y s) (hy1 : y s < 1)
    (hk0 : 0 < k s) (heta0 : 0 < eta s)
    (hetaSmall : (eta s) ^ 2 < (r s) ^ 2 / 2)
    (hX0 : 0 < X) (hX1 : X < 1)
    (hchi : ((k s) ^ 2 - 1) * eta s = k s * X * y s)
    (hq : y s ≤ q) (htrel : (t s) ^ 2 = (r s) ^ 2 * q) :
    False := by
  have hflow :=
    residualAlong_hasDerivAt_of_flow hr ht hy hk heta
  have hpos : 0 < deriv (residualAlong r t y k eta) s :=
    residualAlong_deriv_pos_at_zero hr ht hy hk heta hn hzero hM
      hy0 hy1 hk0 heta0 hetaSmall hX0 hX1 hchi hq htrel
  have hderiv_pos :
      0 < 2 * contactDrift n (r s) (t s) (y s) (k s)
        ((k s) ^ 2 - 1) (eta s) := by
    rwa [hflow.deriv] at hpos
  exact no_positive_derivative_at_first_zero ha hzero hleft
    hflow hderiv_pos

end

end BrezisOP6
