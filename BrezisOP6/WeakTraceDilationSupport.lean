import BrezisOP6.WeakDilationBasics
import BrezisOP6.WeakDilationGradient
import BrezisOP6.WeakBallEnergy

/-!
# The support gain of a zero-trace difference under inward dilation

The zero-extension definition makes the support statement exact.  This is
the geometric clearance needed before convolution with a compact mollifier.
-/

namespace BrezisOP6

open Metric

noncomputable section

theorem zeroExtendedDifference_zero_outside (n : ℕ) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n) (x : GLEuclidean n)
    (hx : R ≤ ‖x‖) :
    zeroExtendedDifference n R u v x = 0 := by
  have hnot : x ∉ Metric.ball (0 : GLEuclidean n) R := by
    simpa [Metric.mem_ball, dist_zero_left, dist_zero_right] using (not_lt.mpr hx)
  simp [zeroExtendedDifference, hnot]

theorem zeroExtendedGradientDifference_zero_outside (n : ℕ) (R : ℝ)
    (G H : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) (hx : R ≤ ‖x‖) :
    zeroExtendedGradientDifference n R G H x = 0 := by
  have hnot : x ∉ Metric.ball (0 : GLEuclidean n) R := by
    simpa [Metric.mem_ball, dist_zero_left, dist_zero_right] using (not_lt.mpr hx)
  simp [zeroExtendedGradientDifference, hnot]

theorem inward_zeroExtendedDifference_zero_outside (n : ℕ) (R a : ℝ)
    (ha : 0 < a) (u v : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) (hx : a * R ≤ ‖x‖) :
    inwardDilation n a (zeroExtendedDifference n R u v) x = 0 :=
  inwardDilation_zero_outside n R a ha
    (zeroExtendedDifference n R u v)
    (zeroExtendedDifference_zero_outside n R u v) x hx

theorem inward_zeroExtendedGradientDifference_zero_outside
    (n : ℕ) (R a : ℝ) (ha : 0 < a)
    (G H : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) (hx : a * R ≤ ‖x‖) :
    inwardGradient n a (zeroExtendedGradientDifference n R G H) x = 0 := by
  have hinv : 0 < a⁻¹ := inv_pos.mpr ha
  have hnorm : ‖a⁻¹ • x‖ = a⁻¹ * ‖x‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  have hscaled : R ≤ ‖a⁻¹ • x‖ := by
    rw [hnorm]
    have h : R ≤ ‖x‖ * a⁻¹ :=
      (le_mul_inv_iff₀ ha).2 (by simpa only [mul_comm] using hx)
    simpa only [mul_comm] using h
  change a⁻¹ • zeroExtendedGradientDifference n R G H (a⁻¹ • x) = 0
  rw [zeroExtendedGradientDifference_zero_outside n R G H (a⁻¹ • x) hscaled]
  ext y
  simp [ContinuousLinearMap.smul_apply]

/-- The inward pullback of a zero extension has compact support inside the
    shrunken closed ball. -/
theorem inward_zeroExtendedDifference_tsupport_subset_closedBall
    (n : ℕ) (R a : ℝ) (ha : 0 < a)
    (u v : GLEuclidean n → GLEuclidean n) :
    tsupport (inwardDilation n a (zeroExtendedDifference n R u v)) ⊆
      Metric.closedBall (0 : GLEuclidean n) (a * R) := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    by_contra hnot
    have hgt : a * R < ‖x‖ := by
      have hnot' : ¬ ‖x‖ ≤ a * R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hnot
      exact lt_of_not_ge hnot'
    exact (Function.mem_support.mp hx)
      (inward_zeroExtendedDifference_zero_outside n R a ha u v x hgt.le)
  · exact isClosed_closedBall

theorem inward_zeroExtendedDifference_hasCompactSupport
    (n : ℕ) (R a : ℝ) (ha : 0 < a)
    (u v : GLEuclidean n → GLEuclidean n) :
    HasCompactSupport (inwardDilation n a (zeroExtendedDifference n R u v)) := by
  apply HasCompactSupport.intro'
    (K := Metric.closedBall (0 : GLEuclidean n) (a * R))
    (isCompact_closedBall (0 : GLEuclidean n) (a * R)) isClosed_closedBall
  intro x hx
  have hnot : ¬ ‖x‖ ≤ a * R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  exact inward_zeroExtendedDifference_zero_outside n R a ha u v x
    (lt_of_not_ge hnot).le

/-- For `0<a<1`, the shrunken difference is supported a positive distance
    from the original spherical boundary. -/
theorem inward_zeroExtendedDifference_tsupport_subset_ball
    (n : ℕ) (R a : ℝ) (hR : 0 < R) (ha : 0 < a) (ha1 : a < 1)
    (u v : GLEuclidean n → GLEuclidean n) :
    tsupport (inwardDilation n a (zeroExtendedDifference n R u v)) ⊆
      Metric.ball (0 : GLEuclidean n) R := by
  intro x hx
  have hnorm : ‖x‖ ≤ a * R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using
      inward_zeroExtendedDifference_tsupport_subset_closedBall n R a ha u v hx
  have hstrict : a * R < R := by
    have hgap := mul_pos (sub_pos.mpr ha1) hR
    nlinarith
  simpa [Metric.mem_ball, dist_zero_right] using hnorm.trans_lt hstrict

end

end BrezisOP6
