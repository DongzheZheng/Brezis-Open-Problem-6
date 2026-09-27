import BrezisOP6.EnergyActualSphereMinimum

/-!
# Profile ordering in the form needed by the energy bridge

The ratio-flux comparison gives `0 < F(r) < f(r)` for `0 < r ≤ R`.
This elementary transfer records all pointwise bridge signs, including
the origin where both profiles vanish.
-/

namespace BrezisOP6

open Metric Set

noncomputable section

theorem bridge_signs_of_strict_profile_order
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (hFpos : ∀ r ∈ Ioc (0 : ℝ) R, 0 < F r)
    (horder : ∀ r ∈ Ioc (0 : ℝ) R, F r < f r) :
    (∀ r ∈ Icc (0 : ℝ) R, 0 ≤ f r ^ 2 - F r ^ 2) ∧
    (∀ r ∈ Ioo (0 : ℝ) R, 0 < f r ^ 2 - F r ^ 2) ∧
    (∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      0 ≤ F ‖x‖) ∧
    (∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      F ‖x‖ ≤ f ‖x‖) ∧
    (∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 → F ‖x‖ < f ‖x‖) := by
  have hpoint (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) R) :
      0 < F r ∧ F r < f r := ⟨hFpos r hr, horder r hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases eq_or_lt_of_le hr.1 with hzero | hpos
    · subst r
      simp [hf0, hF0]
    · obtain ⟨hFp, hlt⟩ := hpoint r ⟨hpos, hr.2⟩
      nlinarith
  · intro r hr
    obtain ⟨hFp, hlt⟩ := hpoint r ⟨hr.1, hr.2.le⟩
    nlinarith
  · intro x hx
    have hrR : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rcases eq_or_lt_of_le (norm_nonneg x) with hzero | hpos
    · rw [← hzero, hF0]
    · exact (hFpos ‖x‖ ⟨hpos, hrR.le⟩).le
  · intro x hx
    have hrR : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rcases eq_or_lt_of_le (norm_nonneg x) with hzero | hpos
    · rw [← hzero, hf0, hF0]
    · exact (horder ‖x‖ ⟨hpos, hrR.le⟩).le
  · intro x hx hx0
    have hrR : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact horder ‖x‖ ⟨norm_pos_iff.mpr hx0, hrR.le⟩

end

end BrezisOP6
