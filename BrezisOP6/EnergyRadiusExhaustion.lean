import BrezisOP6.EnergySmoothBallBridgeInterior

/-!
# A canonical punctured-ball exhaustion

The interior energy identity is applied on annuli with inner radii tending
to zero.  This module provides one explicit decreasing sequence of radii,
so its existence does not remain an implicit analytic hypothesis.
-/

namespace BrezisOP6

open Filter
open scoped Topology

noncomputable section

/-- The inner radius at stage `k` of a ball of radius `R`. -/
def canonicalEnergyRadius (R : ℝ) (k : ℕ) : ℝ :=
  R / ((k + 1 : ℕ) : ℝ)

theorem canonicalEnergyRadius_pos (R : ℝ) (hR : 0 < R) (k : ℕ) :
    0 < canonicalEnergyRadius R k := by
  unfold canonicalEnergyRadius
  positivity

theorem canonicalEnergyRadius_le (R : ℝ) (hR : 0 < R) (k : ℕ) :
    canonicalEnergyRadius R k ≤ R := by
  unfold canonicalEnergyRadius
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  exact (div_le_iff₀ (by positivity : 0 < ((k + 1 : ℕ) : ℝ))).mpr
    (by nlinarith)

theorem canonicalEnergyRadius_antitone (R : ℝ) (hR : 0 < R) :
    Antitone (canonicalEnergyRadius R) := by
  intro i j hij
  unfold canonicalEnergyRadius
  have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hden : (((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hij 1
  apply (div_le_div_iff₀ hj hi).mpr
  nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hden)]

theorem canonicalEnergyRadius_tendsto_zero (R : ℝ) :
    Tendsto (canonicalEnergyRadius R) atTop (𝓝 0) := by
  have hInv : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  simpa only [canonicalEnergyRadius, div_eq_mul_inv, mul_zero] using
    hInv.const_mul R

end

end BrezisOP6
