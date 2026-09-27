import BrezisOP6.Contact

/-!
# The Picone residual from the profile flow

This file verifies the local calculation in the zero-mode Picone lemma.  It
starts with the logarithmic derivatives of the weight and positive multiplier,
and proves that the resulting differential expression is exactly the contact
residual `S`.  Positivity and endpoint integration are handled in separate
modules.
-/

namespace BrezisOP6

noncomputable section

/-- `r h'/h` for `h=(f²-F²)/r²`, expressed in profile variables. -/
def piconeWeightLogSlope (y k eta : ℝ) : ℝ :=
  2 * (k * eta - y)

/-- `r φ'/φ` for `φ=F/(r√(k²-1))`, expressed in profile variables. -/
def piconeMultiplierLogSlope (y k eta : ℝ) : ℝ :=
  -(y + k * eta)

/-- The logarithmic radial derivative of `r φ'/φ` obtained from the
profile flow.  The variables `dy`, `dk`, and `deta` denote `r` times the
ordinary radial derivatives. -/
def piconeMultiplierLogRate (dy dk deta k eta : ℝ) : ℝ :=
  -(dy + dk * eta + k * deta)

/-- The flow equations for `y`, `k`, and `η` give the derivative of the
Picone multiplier's logarithmic slope along logarithmic radius. -/
theorem piconeMultiplierLogSlope_hasDerivAt
    {y k eta : ℝ → ℝ} {s n r t : ℝ}
    (hy : HasDerivAt y
      (y s ^ 2 - n * y s + r ^ 2 - t ^ 2) s)
    (hk : HasDerivAt k (((k s) ^ 2 - 1) * eta s) s)
    (heta : HasDerivAt eta
      (k s * t ^ 2 - (n - 2 * y s) * eta s -
        2 * k s * eta s ^ 2) s) :
    HasDerivAt
      (fun z => piconeMultiplierLogSlope (y z) (k z) (eta z))
      (piconeMultiplierLogRate
        (y s ^ 2 - n * y s + r ^ 2 - t ^ 2)
        (((k s) ^ 2 - 1) * eta s)
        (k s * t ^ 2 - (n - 2 * y s) * eta s -
          2 * k s * eta s ^ 2) (k s) (eta s)) s := by
  convert ((hy.add (hk.mul heta)).neg) using 1
  dsimp [piconeMultiplierLogSlope, piconeMultiplierLogRate]
  ring

/-- The scalar differential expression produced by the Picone transform,
written in terms of logarithmic slopes. -/
def piconeLogResidual (n piH piPhi piPhiRate : ℝ) : ℝ :=
  piH - piPhiRate - (n - 2 + piH) * piPhi - piPhi ^ 2

/-- Exact algebraic identification of the Picone differential expression
with `S = r² + (k²-1)t² - 4y - 2y² - η²`.  This is the crucial
calculation in the zero-mode identity; it requires no sign assumptions. -/
theorem piconeLogResidual_eq_contactResidual
    (n r t y k eta : ℝ) :
    piconeLogResidual n
      (piconeWeightLogSlope y k eta)
      (piconeMultiplierLogSlope y k eta)
      (piconeMultiplierLogRate
        (y ^ 2 - n * y + r ^ 2 - t ^ 2)
        ((k ^ 2 - 1) * eta)
        (k * t ^ 2 - (n - 2 * y) * eta - 2 * k * eta ^ 2)
        k eta) =
      contactResidual r t y (k ^ 2 - 1) eta := by
  unfold piconeLogResidual piconeWeightLogSlope
    piconeMultiplierLogSlope piconeMultiplierLogRate contactResidual
  ring

end

end BrezisOP6
