import Mathlib

/-!
# Pointwise algebra for the finite-ball / entire-space energy bridge

These identities are the algebraic part of the paper's equations (2.5)–(2.7).
The integration-by-parts and Sobolev statements are separate obligations.
-/

namespace BrezisOP6

/-- Polarization of the quartic potential around a radial profile. This is
the pointwise cancellation used before radial integration by parts. -/
theorem quartic_potential_polarization (p s : ℝ) :
    (1 - p ^ 2 * s) ^ 2 - (1 - p ^ 2) ^ 2 =
      -2 * p ^ 2 * (1 - p ^ 2) * (s - 1) +
        p ^ 4 * (s - 1) ^ 2 := by
  ring

/-- The nonnegative quartic remainder written in the original competitor
variable. This is equation (2.7) in the paper. -/
theorem bridge_quartic_rewrite (f F s : ℝ) (hf : f ≠ 0) :
    (f ^ 4 - F ^ 4) * (s - 1) ^ 2 =
      (1 - (F / f) ^ 4) * (f ^ 2 * s - f ^ 2) ^ 2 := by
  field_simp

theorem bridge_quartic_nonneg {f F s : ℝ} (hF : 0 ≤ F) (hFf : F ≤ f) :
    0 ≤ (f ^ 4 - F ^ 4) * (s - 1) ^ 2 := by
  have hdiff : 0 ≤ f - F := by linarith
  have hsum : 0 ≤ f + F := by linarith
  have hid : f ^ 4 - F ^ 4 = (f - F) * (f + F) * (f ^ 2 + F ^ 2) := by ring
  rw [hid]
  positivity

theorem bridge_quartic_pos {f F s : ℝ} (hF : 0 ≤ F) (hFf : F < f)
    (hs : s ≠ 1) :
    0 < (f ^ 4 - F ^ 4) * (s - 1) ^ 2 := by
  have hdiff : 0 < f - F := by linarith
  have hsum : 0 < f + F := by linarith
  have hfpos : 0 < f := lt_of_le_of_lt hF hFf
  have hsq : 0 < f ^ 2 + F ^ 2 := by positivity
  have hdsq : 0 < (s - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hs)
  have hid : f ^ 4 - F ^ 4 = (f - F) * (f + F) * (f ^ 2 + F ^ 2) := by ring
  rw [hid]
  positivity

end BrezisOP6
