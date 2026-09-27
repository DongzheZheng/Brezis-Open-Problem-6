import BrezisOP6.EnergyIBP

/-!
# Radial projection onto the closed unit ball

This is the pointwise geometric step in the manuscript's equality proof.
Projection onto the closed unit ball preserves vectors already inside,
decreases the quartic potential, and is nonexpansive in Euclidean space.
The Sobolev chain rule and elliptic regularity are separate analytic steps.
-/

namespace BrezisOP6

open Real

noncomputable section

/-- Radial projection of a Euclidean vector onto the closed unit ball. -/
def radialUnitBallProjection {n : ℕ} (x : GLEuclidean n) :
    GLEuclidean n := (max 1 ‖x‖)⁻¹ • x

theorem radialUnitBallProjection_of_norm_le {n : ℕ}
    (x : GLEuclidean n) (hx : ‖x‖ ≤ 1) :
    radialUnitBallProjection x = x := by
  simp [radialUnitBallProjection, max_eq_left hx]

theorem radialUnitBallProjection_norm_of_one_lt {n : ℕ}
    (x : GLEuclidean n) (hx : 1 < ‖x‖) :
    ‖radialUnitBallProjection x‖ = 1 := by
  rw [radialUnitBallProjection, max_eq_right hx.le, norm_smul]
  simp only [Real.norm_eq_abs, abs_inv,
    abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hx)]
  exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx))

theorem radialUnitBallProjection_smul {n : ℕ}
    (x : GLEuclidean n) :
    (max 1 ‖x‖) • radialUnitBallProjection x = x := by
  have hmax : 0 < max 1 ‖x‖ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  simp [radialUnitBallProjection, smul_smul, hmax.ne']

/-- The pointwise quartic potential does not increase under the radial
projection.  This does not use any weak chain rule. -/
theorem radialUnitBallProjection_quartic_potential_le {n : ℕ}
    (x : GLEuclidean n) :
    (1 - ‖radialUnitBallProjection x‖ ^ 2) ^ 2 ≤
      (1 - ‖x‖ ^ 2) ^ 2 := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [radialUnitBallProjection_of_norm_le x hx]
  · rw [radialUnitBallProjection_norm_of_one_lt x (lt_of_not_ge hx)]
    norm_num
    exact sq_nonneg _

/-- Outside the unit ball the quartic potential strictly decreases. -/
theorem radialUnitBallProjection_quartic_potential_lt {n : ℕ}
    (x : GLEuclidean n) (hx : 1 < ‖x‖) :
    (1 - ‖radialUnitBallProjection x‖ ^ 2) ^ 2 <
      (1 - ‖x‖ ^ 2) ^ 2 := by
  rw [radialUnitBallProjection_norm_of_one_lt x hx]
  have hsq : 1 < ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  nlinarith [sq_pos_of_ne_zero (by linarith : 1 - ‖x‖ ^ 2 ≠ 0)]

private theorem projection_norm_sub_le_inside_outside {n : ℕ}
    (x y : GLEuclidean n) (hx : ‖x‖ ≤ 1) (hy : 1 < ‖y‖) :
    ‖radialUnitBallProjection x - radialUnitBallProjection y‖ ≤
      ‖x - y‖ := by
  let v := radialUnitBallProjection y
  have hv : ‖v‖ = 1 := radialUnitBallProjection_norm_of_one_lt y hy
  have hyScale : y = ‖y‖ • v := by
    change y = ‖y‖ • radialUnitBallProjection y
    rw [← max_eq_right hy.le]
    exact (radialUnitBallProjection_smul y).symm
  have hz : inner ℝ x v ≤ 1 := by
    calc
      inner ℝ x v ≤ ‖x‖ * ‖v‖ := real_inner_le_norm x v
      _ = ‖x‖ := by rw [hv]; ring
      _ ≤ 1 := hx
  have hleft : ‖x - v‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x v + 1 := by
    rw [norm_sub_sq_real, hv]
    ring
  have hright : ‖x - y‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * ‖y‖ * inner ℝ x v + ‖y‖ ^ 2 := by
    rw [hyScale, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (y : GLEuclidean n)), hv]
    ring
  have hgap : 0 ≤ (‖y‖ - 1) * (1 - inner ℝ x v) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ (‖y‖ - 1) ^ 2 := sq_nonneg _
  rw [radialUnitBallProjection_of_norm_le x hx]
  change ‖x - v‖ ≤ ‖x - y‖
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  nlinarith [hleft, hright, hgap, hsq]

private theorem projection_norm_sub_le_outside_outside {n : ℕ}
    (x y : GLEuclidean n) (hx : 1 < ‖x‖) (hy : 1 < ‖y‖) :
    ‖radialUnitBallProjection x - radialUnitBallProjection y‖ ≤
      ‖x - y‖ := by
  let u := radialUnitBallProjection x
  let v := radialUnitBallProjection y
  have hu : ‖u‖ = 1 := radialUnitBallProjection_norm_of_one_lt x hx
  have hv : ‖v‖ = 1 := radialUnitBallProjection_norm_of_one_lt y hy
  have hxScale : x = ‖x‖ • u := by
    change x = ‖x‖ • radialUnitBallProjection x
    rw [← max_eq_right hx.le]
    exact (radialUnitBallProjection_smul x).symm
  have hyScale : y = ‖y‖ • v := by
    change y = ‖y‖ • radialUnitBallProjection y
    rw [← max_eq_right hy.le]
    exact (radialUnitBallProjection_smul y).symm
  have hz : inner ℝ u v ≤ 1 := by
    calc
      inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      _ = 1 := by rw [hu, hv]; ring
  have hleft : ‖u - v‖ ^ 2 = 2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real, hu, hv]
    ring
  have hright : ‖x - y‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * (‖x‖ * ‖y‖) * inner ℝ u v + ‖y‖ ^ 2 := by
    rw [hxScale, hyScale, norm_sub_sq_real,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial,
      norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (x : GLEuclidean n)),
      abs_of_nonneg (norm_nonneg (y : GLEuclidean n)), hu, hv]
    ring
  have hab : 1 ≤ ‖x‖ * ‖y‖ := by
    nlinarith [mul_nonneg
      (show 0 ≤ ‖x‖ - 1 by linarith)
      (show 0 ≤ ‖y‖ - 1 by linarith)]
  have hgap : 0 ≤ (‖x‖ * ‖y‖ - 1) * (1 - inner ℝ u v) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ (‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  change ‖u - v‖ ≤ ‖x - y‖
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  nlinarith [hleft, hright, hgap, hsq]

/-- Radial projection onto the Euclidean closed unit ball is
`1`-Lipschitz. -/
theorem radialUnitBallProjection_lipschitzWith_one (n : ℕ) :
    LipschitzWith 1 (radialUnitBallProjection : GLEuclidean n → GLEuclidean n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  by_cases hx : ‖x‖ ≤ 1
  · by_cases hy : ‖y‖ ≤ 1
    · rw [radialUnitBallProjection_of_norm_le x hx,
        radialUnitBallProjection_of_norm_le y hy]
    · exact projection_norm_sub_le_inside_outside x y hx (lt_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ 1
    · calc
        ‖radialUnitBallProjection x - radialUnitBallProjection y‖ =
            ‖radialUnitBallProjection y - radialUnitBallProjection x‖ :=
          norm_sub_rev _ _
        _ ≤ ‖y - x‖ :=
          projection_norm_sub_le_inside_outside y x hy (lt_of_not_ge hx)
        _ = ‖x - y‖ := norm_sub_rev _ _
    · exact projection_norm_sub_le_outside_outside x y
        (lt_of_not_ge hx) (lt_of_not_ge hy)

end

end BrezisOP6
