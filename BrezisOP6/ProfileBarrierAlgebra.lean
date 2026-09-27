import Mathlib

/-!
# Algebra at a possible failure of the whole-space profile bound

The paper proves `F² ≥ y` by tracking `W = F²-y` and an auxiliary quantity
`J`. This file checks the key crossing calculation without treating the
global ODE barrier or asymptotic argument as an axiom.
-/

namespace BrezisOP6

/-- The auxiliary quantity `J` in the proof of `F² ≥ y` (paper §4). Here
`rho=F²` and `r` is the radial variable. -/
def profileJ (n rho r : ℝ) : ℝ :=
  r ^ 2 * (1 - rho) - rho * (n + 2 - 3 * rho)

/-- The value of `r J'` after substituting `r rho'=2 rho (1-y)`.
No differentiability is encoded in this algebraic definition. -/
def profileJRate (n rho y r : ℝ) : ℝ :=
  2 * r ^ 2 * (1 - rho) -
    (r ^ 2 + n + 2 - 6 * rho) * (2 * rho * (1 - y))

/-- A polynomial certificate for the crossing calculation. Its right-hand
side vanishes when `J=0`, leaving a product of nonnegative factors if
`0<rho≤y<1` and `n≥3`. -/
theorem profileJ_cross_certificate (n rho y r : ℝ) :
    (profileJRate n rho y r - 6 * rho ^ 2 * (1 - rho)) * (1 - rho) -
      2 * rho * (y - rho) * (n + 2 - 6 * rho + 3 * rho ^ 2) =
      2 * ((1 - rho) - rho * (1 - y)) * profileJ n rho r := by
  unfold profileJRate profileJ
  ring

/-- The strict sign needed to prohibit `J` from crossing downward at a
point where `J=0` and `F²≤y`. The dimension is a real parameter here; the
paper applies this with an integer `n≥3`. -/
theorem profileJRate_pos_at_zero {n rho y r : ℝ}
    (hn : 3 ≤ n) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hroy : rho ≤ y)
    (hJ : profileJ n rho r = 0) :
    0 < profileJRate n rho y r := by
  have hdelta : 0 < 1 - rho := by linarith
  have hB : 0 < n + 2 - 6 * rho + 3 * rho ^ 2 := by
    have hn1 : 0 < n - 1 := by linarith
    have hid : n + 2 - 6 * rho + 3 * rho ^ 2 =
        (n - 1) + 3 * (1 - rho) ^ 2 := by ring
    rw [hid]
    positivity
  have hYrho : 0 ≤ y - rho := by linarith
  have hRhs : 0 ≤ 2 * rho * (y - rho) *
      (n + 2 - 6 * rho + 3 * rho ^ 2) := by positivity
  have hcert := profileJ_cross_certificate n rho y r
  rw [hJ, mul_zero] at hcert
  have hlower : 0 ≤ profileJRate n rho y r - 6 * rho ^ 2 * (1 - rho) := by
    by_contra hneg
    have hlt : profileJRate n rho y r - 6 * rho ^ 2 * (1 - rho) < 0 :=
      lt_of_not_ge hneg
    have hprod :
        (profileJRate n rho y r - 6 * rho ^ 2 * (1 - rho)) *
          (1 - rho) < 0 := mul_neg_of_neg_of_pos hlt hdelta
    linarith
  have hbase : 0 < 6 * rho ^ 2 * (1 - rho) := by positivity
  linarith

end BrezisOP6
