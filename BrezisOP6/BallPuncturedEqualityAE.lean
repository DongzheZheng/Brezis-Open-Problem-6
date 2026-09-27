import BrezisOP6.EnergyVortexPointwise

/-!
# A punctured-ball equality is equality almost everywhere

The origin is negligible for Euclidean volume. This form of equality is the
natural uniqueness statement for finite-energy Sobolev maps.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

theorem ae_eq_on_ball_of_eq_punctured
    (m : ℕ) (R : ℝ)
    (u v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (h : ∀ x : GLEuclidean (m + 3),
      x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R →
        x ≠ 0 → u x = v x) :
    u =ᵐ[volume.restrict (Metric.ball
      (0 : GLEuclidean (m + 3)) R)] v := by
  have hnull : ∀ᵐ x : GLEuclidean (m + 3) ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      (measure_singleton (0 : GLEuclidean (m + 3)) :
        volume ({0} : Set (GLEuclidean (m + 3))) = 0)
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hnull] with x hx hx0
  exact h x hx hx0

end

end BrezisOP6
