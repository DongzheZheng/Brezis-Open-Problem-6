import Mathlib

/-!
# Explicit slope barrier for the entire radial vortex

For n ≥ 3, the paper compares the entire profile with
G(r) = r / sqrt(r²+n+2). This file verifies the exact GL ODE
residual and its strict sign, then records the pointwise
quotient-ODE obstruction at an interior minimum below one.
-/

namespace BrezisOP6

noncomputable section

/-- The explicit comparison profile. -/
def slopeBarrier (n r : ℝ) : ℝ :=
  r / Real.sqrt (r ^ 2 + n + 2)

/-- The first derivative claimed for the explicit profile. -/
def slopeBarrierPrime (n r : ℝ) : ℝ :=
  (n + 2) / (Real.sqrt (r ^ 2 + n + 2)) ^ 3

/-- The second derivative claimed for the explicit profile. -/
def slopeBarrierSecond (n r : ℝ) : ℝ :=
  -3 * (n + 2) * r / (Real.sqrt (r ^ 2 + n + 2)) ^ 5

/-- The displayed first-derivative formula is the actual derivative
of the explicit comparison profile. -/
theorem slopeBarrier_hasDerivAt {n r : ℝ}
    (hn : 3 ≤ n) :
    HasDerivAt (slopeBarrier n) (slopeBarrierPrime n r) r := by
  have hDpos : 0 < r ^ 2 + n + 2 := by
    nlinarith [sq_nonneg r]
  have hspos : 0 < Real.sqrt (r ^ 2 + n + 2) :=
    Real.sqrt_pos.2 hDpos
  have hsne : Real.sqrt (r ^ 2 + n + 2) ≠ 0 := ne_of_gt hspos
  have hsq : (Real.sqrt (r ^ 2 + n + 2)) ^ 2 =
      r ^ 2 + n + 2 := Real.sq_sqrt (le_of_lt hDpos)
  have hD : HasDerivAt (fun x : ℝ => x ^ 2 + n + 2) (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).add_const (n + 2) using 1
    · funext x
      dsimp
      ring
    · dsimp
      ring
  have hs := hD.sqrt (ne_of_gt hDpos)
  have hdiv := (hasDerivAt_id r).div hs hsne
  convert hdiv using 1
  dsimp [slopeBarrierPrime, slopeBarrier]
  field_simp
  nlinarith [hsq]

/-- The displayed second-derivative formula is the derivative
of the explicit first-derivative expression. -/
theorem slopeBarrierPrime_hasDerivAt {n r : ℝ}
    (hn : 3 ≤ n) :
    HasDerivAt (slopeBarrierPrime n) (slopeBarrierSecond n r) r := by
  have hDpos : 0 < r ^ 2 + n + 2 := by
    nlinarith [sq_nonneg r]
  have hspos : 0 < Real.sqrt (r ^ 2 + n + 2) :=
    Real.sqrt_pos.2 hDpos
  have hsne : Real.sqrt (r ^ 2 + n + 2) ≠ 0 := ne_of_gt hspos
  have hD : HasDerivAt (fun x : ℝ => x ^ 2 + n + 2) (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).add_const (n + 2) using 1
    · funext x
      dsimp
      ring
    · dsimp
      ring
  have hs := hD.sqrt (ne_of_gt hDpos)
  have hdiv :=
    (hasDerivAt_const r (n + 2)).div (hs.pow 3) (pow_ne_zero 3 hsne)
  convert hdiv using 1
  dsimp [slopeBarrierPrime, slopeBarrierSecond]
  field_simp
  ring

/-- The degree-one Ginzburg–Landau radial ODE residual. The arguments
p, p₁, p₂ stand for a profile and its first two derivatives. -/
def radialGLResidual (n r p p₁ p₂ : ℝ) : ℝ :=
  p₂ + (n - 1) / r * p₁ - (n - 1) / r ^ 2 * p +
    (1 - p ^ 2) * p

private theorem slopeBarrier_algebra (n r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hsq : s ^ 2 = r ^ 2 + n + 2) :
    radialGLResidual n r (r / s)
      ((n + 2) / s ^ 3) (-3 * (n + 2) * r / s ^ 5) =
      3 * r ^ 3 / s ^ 5 := by
  have hA : n + 2 = s ^ 2 - r ^ 2 := by linarith
  have hN : n - 1 = s ^ 2 - r ^ 2 - 3 := by linarith
  unfold radialGLResidual
  rw [hA, hN]
  field_simp
  ring

/-- Equation (4.2): the residual is exactly
\(3r^3/(r^2+n+2)^{5/2}\), written with a fifth power of the square
root to keep the denominator algebraic in Lean. -/
theorem slopeBarrier_residual {n r : ℝ}
    (hn : 3 ≤ n) (hr : 0 < r) :
    radialGLResidual n r (slopeBarrier n r)
      (slopeBarrierPrime n r) (slopeBarrierSecond n r) =
      3 * r ^ 3 / (Real.sqrt (r ^ 2 + n + 2)) ^ 5 := by
  have hDpos : 0 < r ^ 2 + n + 2 := by
    nlinarith [sq_nonneg r]
  have hspos : 0 < Real.sqrt (r ^ 2 + n + 2) :=
    Real.sqrt_pos.2 hDpos
  have hsq : (Real.sqrt (r ^ 2 + n + 2)) ^ 2 =
      r ^ 2 + n + 2 := Real.sq_sqrt (le_of_lt hDpos)
  unfold slopeBarrier slopeBarrierPrime slopeBarrierSecond
  exact slopeBarrier_algebra n r _ (ne_of_gt hr) (ne_of_gt hspos) hsq

/-- The same residual formula with the paper's fractional-power notation. -/
theorem slopeBarrier_residual_rpow {n r : ℝ}
    (hn : 3 ≤ n) (hr : 0 < r) :
    radialGLResidual n r (slopeBarrier n r)
      (slopeBarrierPrime n r) (slopeBarrierSecond n r) =
      3 * r ^ 3 / (r ^ 2 + n + 2) ^ ((5 : ℝ) / 2) := by
  rw [slopeBarrier_residual hn hr]
  have hDpos : 0 < r ^ 2 + n + 2 := by
    nlinarith [sq_nonneg r]
  have hpow :
      (Real.sqrt (r ^ 2 + n + 2)) ^ 5 =
        (r ^ 2 + n + 2) ^ ((5 : ℝ) / 2) := by
    simpa [Real.rpow_natCast] using
      (Real.rpow_div_two_eq_sqrt (5 : ℝ) (le_of_lt hDpos)).symm
  rw [hpow]

/-- The explicit barrier is a strict subsolution for all r>0 and n≥3. -/
theorem slopeBarrier_residual_pos {n r : ℝ}
    (hn : 3 ≤ n) (hr : 0 < r) :
    0 < radialGLResidual n r (slopeBarrier n r)
      (slopeBarrierPrime n r) (slopeBarrierSecond n r) := by
  rw [slopeBarrier_residual hn hr]
  have hDpos : 0 < r ^ 2 + n + 2 := by
    nlinarith [sq_nonneg r]
  have hspos : 0 < Real.sqrt (r ^ 2 + n + 2) :=
    Real.sqrt_pos.2 hDpos
  positivity

/-- Product-rule identity for \(F=GZ\). The variables \(g_1,g_2,z_1,z_2\)
stand for first and second derivatives, but this lemma is entirely
algebraic and does not assume differentiability. -/
theorem radialGLResidual_product (n r g g₁ g₂ z z₁ z₂ : ℝ) :
    radialGLResidual n r (g * z) (g₁ * z + g * z₁)
      (g₂ * z + 2 * g₁ * z₁ + g * z₂) =
      g * z₂ + (2 * g₁ + (n - 1) / r * g) * z₁ +
        radialGLResidual n r g g₁ g₂ * z +
        g ^ 3 * z * (1 - z ^ 2) := by
  unfold radialGLResidual
  ring

/-- The pointwise contradiction at an interior minimum of
\(Z=F/G\) with \(0<Z<1\): there \(Z'=0\), \(Z''\ge0\), while the
explicit barrier has positive ODE residual and \(F\) has zero residual. -/
theorem quotient_minimum_obstruction
    {n r g g₁ g₂ z z₂ : ℝ}
    (hg : 0 < g) (hz : 0 < z) (hz1 : z < 1)
    (hz2 : 0 ≤ z₂)
    (hgres : 0 < radialGLResidual n r g g₁ g₂)
    (hF : radialGLResidual n r (g * z) (g₁ * z)
      (g₂ * z + g * z₂) = 0) : False := by
  have hexp := radialGLResidual_product n r g g₁ g₂ z 0 z₂
  simp only [mul_zero, add_zero] at hexp
  rw [hF] at hexp
  have hfirst : 0 ≤ g * z₂ := mul_nonneg (le_of_lt hg) hz2
  have hsecond : 0 < radialGLResidual n r g g₁ g₂ * z :=
    mul_pos hgres hz
  have hzsq : 0 < 1 - z ^ 2 := by nlinarith
  have hthird : 0 < g ^ 3 * z * (1 - z ^ 2) := by positivity
  linarith

/-- Specialization to the explicit comparison profile. -/
theorem slopeBarrier_no_minimum_below_one
    {n r z z₂ : ℝ} (hn : 3 ≤ n) (hr : 0 < r)
    (hz : 0 < z) (hz1 : z < 1) (hz2 : 0 ≤ z₂)
    (hF : radialGLResidual n r
      (slopeBarrier n r * z) (slopeBarrierPrime n r * z)
      (slopeBarrierSecond n r * z + slopeBarrier n r * z₂) = 0) :
    False :=
  quotient_minimum_obstruction
    (by
      unfold slopeBarrier
      have hDpos : 0 < r ^ 2 + n + 2 := by
        nlinarith [sq_nonneg r]
      exact div_pos hr (Real.sqrt_pos.2 hDpos))
    hz hz1 hz2 (slopeBarrier_residual_pos hn hr) hF

end

end BrezisOP6
