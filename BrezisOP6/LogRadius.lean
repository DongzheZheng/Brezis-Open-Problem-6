import Mathlib

/-!
# Logarithmic radial parameter

The contact calculation uses `s = log r`.  This module records the exact
chain-rule passage from an ordinary radial equation `r g'(r)=V(r)` to the
equation for `g(exp s)` in logarithmic radius.  No ODE existence statement is
used.
-/

namespace BrezisOP6

noncomputable section

/-- A radial flow equation transported to logarithmic radius. -/
theorem hasDerivAt_exp_comp_of_radial_flow
    {g : ℝ → ℝ} {s V : ℝ}
    (hg : DifferentiableAt ℝ g (Real.exp s))
    (hflow : Real.exp s * deriv g (Real.exp s) = V) :
    HasDerivAt (fun x => g (Real.exp x)) V s := by
  have hcomp := hg.hasDerivAt.comp s (Real.hasDerivAt_exp s)
  convert hcomp using 1
  simpa [mul_comm] using hflow.symm

/-- A parameterized version in which the flow value is a function of
the radial position. -/
theorem hasDerivAt_exp_comp_of_radial_flow_fun
    {g V : ℝ → ℝ} {s : ℝ}
    (hg : DifferentiableAt ℝ g (Real.exp s))
    (hflow : Real.exp s * deriv g (Real.exp s) = V (Real.exp s)) :
    HasDerivAt (fun x => g (Real.exp x)) (V (Real.exp s)) s :=
  hasDerivAt_exp_comp_of_radial_flow hg hflow

end

end BrezisOP6
