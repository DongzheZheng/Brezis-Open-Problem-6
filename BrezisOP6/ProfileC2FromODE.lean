import BrezisOP6.FlowFromProfiles

/-!
# Second-order regularity from the radial profile equation

The first derivative is continuously differentiable away from the origin once
it is differentiable there and the radial ODE holds pointwise: the ODE
expresses its derivative as a continuous function of the radius, the profile,
and the first derivative. Thus the separate `C²` input in the slope comparison
is a consequence of the weaker profile hypotheses already used downstream.
-/

namespace BrezisOP6

noncomputable section

open Set

/-- A pointwise radial ODE upgrades a twice-differentiable positive-radius
profile to `C²` on the positive half-line. No endpoint regularity is used. -/
theorem radial_profile_contDiffOn_two_of_ode
    (n : ℝ) (F : ℝ → ℝ)
    (hFDiff : Differentiable ℝ F)
    (hF2diff : ∀ r, 0 < r → DifferentiableAt ℝ (deriv F) r)
    (hODE : ∀ r, 0 < r →
      radialODEAt n r (F r) (deriv F r) (deriv (deriv F) r)) :
    ContDiffOn ℝ 2 F (Ioi 0) := by
  let rhs : ℝ → ℝ := fun r =>
    (n - 1) / r ^ 2 * F r - (n - 1) / r * deriv F r -
      (1 - F r ^ 2) * F r
  have hEq : EqOn (deriv (deriv F)) rhs (Ioi 0) := by
    intro r hr
    have hdiv := (radialODEAt_iff_divided n r
      (F r) (deriv F r) (deriv (deriv F) r) hr).mp
      (hODE r hr)
    dsimp [rhs]
    linarith
  have hrhs : ContinuousOn rhs (Ioi 0) := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hFc : ContinuousAt F r := (hFDiff r).continuousAt
    have hDFc : ContinuousAt (deriv F) r :=
      (hF2diff r hr).continuousAt
    have hc : ContinuousAt rhs r := by
      dsimp [rhs]
      fun_prop (disch := positivity)
    exact hc.continuousWithinAt
  have hF2cont : ContinuousOn (deriv (deriv F)) (Ioi 0) :=
    hrhs.congr hEq
  have hDFdiff : DifferentiableOn ℝ (deriv F) (Ioi 0) := by
    intro r hr
    exact (hF2diff r hr).differentiableWithinAt
  have hDFc1 : ContDiffOn ℝ 1 (deriv F) (Ioi 0) := by
    change ContDiffOn ℝ (0 + 1) (deriv F) (Ioi 0)
    apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
    refine ⟨hDFdiff, ?_, ?_⟩
    · simp
    · exact contDiffOn_zero.mpr hF2cont
  have hFdiffOn : DifferentiableOn ℝ F (Ioi 0) :=
    hFDiff.differentiableOn
  change ContDiffOn ℝ (1 + 1) F (Ioi 0)
  apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
  exact ⟨hFdiffOn, by simp, hDFc1⟩

end

end BrezisOP6
