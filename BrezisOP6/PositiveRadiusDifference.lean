import BrezisOP6.FlowFromProfiles

/-!
# The nonsingular difference equation at positive radius

Two radial Ginzburg--Landau profiles differ by a linear second-order
equation.  Its coefficients depend on the two given profiles, not on the
difference as an unknown.  On every compact interval bounded away from
zero these coefficients are bounded, so ordinary linear-ODE uniqueness
applies after the independently verified origin-germ argument.
-/

namespace BrezisOP6

noncomputable section

def radialDifferenceCoefficient (n r p q : ℝ) : ℝ :=
  (n - 1) / r ^ 2 - 1 + p ^ 2 + p * q + q ^ 2

theorem radialODE_difference_linear
    (n r p q p₁ q₁ p₂ q₂ : ℝ)
    (hr : 0 < r)
    (hp : radialODEAt n r p p₁ p₂)
    (hq : radialODEAt n r q q₁ q₂) :
    p₂ - q₂ =
      radialDifferenceCoefficient n r p q * (p - q) -
        ((n - 1) / r) * (p₁ - q₁) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hpd := (radialODEAt_iff_divided n r p p₁ p₂ hr).mp hp
  have hqd := (radialODEAt_iff_divided n r q q₁ q₂ hr).mp hq
  have hcubic : p ^ 3 - q ^ 3 =
      (p - q) * (p ^ 2 + p * q + q ^ 2) := by ring
  unfold radialDifferenceCoefficient
  field_simp [hrne] at hpd hqd ⊢
  nlinarith [hcubic]

end

end BrezisOP6
