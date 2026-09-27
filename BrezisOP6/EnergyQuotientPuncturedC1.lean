import BrezisOP6.EnergyRegularNumeratorC1

/-!
# Ordinary smoothness of the quotient away from the radial origin

The quotient field `u(x)/f(|x|)` is an ordinary `C¹` field on the
punctured open ball.  This supplies the spherical Hilbert-trace
construction with its actual smooth competitor rather than an assumed
quotient-regularity predicate.
-/

namespace BrezisOP6

open Metric

noncomputable section

theorem radialQuotient_contDiffOn_puncturedBall
    (n : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (hfC1 : ContDiff ℝ 1 f)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean n) R)) :
    ContDiffOn ℝ 1
      (fun x : GLEuclidean n => (f ‖x‖)⁻¹ • u x)
      {x | 0 < ‖x‖ ∧ ‖x‖ < R} := by
  let s : Set (GLEuclidean n) := {x | 0 < ‖x‖ ∧ ‖x‖ < R}
  have hsClosed : s ⊆ Metric.closedBall
      (0 : GLEuclidean n) R := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      le_of_lt hx.2
  have huOn : ContDiffOn ℝ 1 u s := huC1.mono hsClosed
  have hn : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => ‖x‖) s := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hx.1
    exact (contDiffAt_norm ℝ hx0).contDiffWithinAt
  have hfOn : ContDiffOn ℝ 1
      (fun x : GLEuclidean n => f ‖x‖) s :=
    hfC1.comp_contDiffOn hn
  have hfNe : ∀ x ∈ s, f ‖x‖ ≠ 0 := by
    intro x hx
    exact ne_of_gt (hfpos ‖x‖ hx.1 (le_of_lt hx.2))
  exact (hfOn.inv hfNe).smul huOn

end

end BrezisOP6
