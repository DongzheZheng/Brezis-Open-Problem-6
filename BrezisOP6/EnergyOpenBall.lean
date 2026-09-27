import BrezisOP6.EnergySingleProfileTheorem

/-!
# Punctured closed balls and ordinary open balls have the same volume

The origin and outer sphere have zero Euclidean volume.  Thus every spatial
integral and restricted GL energy in the direct single-profile theorem can
be read on the ordinary open ball without changing its value.
-/

namespace BrezisOP6

open MeasureTheory Set Metric

noncomputable section

theorem energyPositiveClosedBall_ae_eq_ball (m : ℕ) (R : ℝ) :
    energyPositiveClosedBall (m + 3) R =ᵐ[(volume :
      Measure (GLEuclidean (m + 3)))]
      Metric.ball (0 : GLEuclidean (m + 3)) R := by
  letI : NeZero (m + 3) := ⟨by omega⟩
  have hSphere : (volume : Measure (GLEuclidean (m + 3)))
      (Metric.sphere (0 : GLEuclidean (m + 3)) R) = 0 :=
    Measure.addHaar_sphere (volume : Measure (GLEuclidean (m + 3))) 0 R
  have hOrigin : (volume : Measure (GLEuclidean (m + 3)))
      ({0} : Set (GLEuclidean (m + 3))) = 0 := by simp
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _ hSphere
    intro x hx
    have hxpos : 0 < ‖x‖ := hx.1.1
    have hxle : ‖x‖ ≤ R := hx.1.2
    have hxnot : ¬ ‖x‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hx.2
    change dist x 0 = R
    rw [dist_zero_right]
    exact le_antisymm hxle (le_of_not_gt hxnot)
  · apply measure_mono_null _ hOrigin
    intro x hx
    by_contra hx0
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxr : ‖x‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hx.1
    exact hx.2 ⟨hxnorm, hxr.le⟩

theorem energyPositiveClosedBall_integral_eq_ball (m : ℕ)
    (R : ℝ) (f : GLEuclidean (m + 3) → ℝ) :
    (∫ x in energyPositiveClosedBall (m + 3) R, f x) =
      ∫ x in Metric.ball (0 : GLEuclidean (m + 3)) R, f x :=
  setIntegral_congr_set (energyPositiveClosedBall_ae_eq_ball m R)

theorem energyPositiveClosedBall_restrict_eq_ball (m : ℕ) (R : ℝ) :
    (volume : Measure (GLEuclidean (m + 3))).restrict
      (energyPositiveClosedBall (m + 3) R) =
    (volume : Measure (GLEuclidean (m + 3))).restrict
      (Metric.ball (0 : GLEuclidean (m + 3)) R) :=
  Measure.restrict_congr_set (energyPositiveClosedBall_ae_eq_ball m R)

end

end BrezisOP6
