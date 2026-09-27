import BrezisOP6.EnergyQuadraticIntegrability
import BrezisOP6.EnergyRegularBallBridge

/-!
# Quartic bridge integrability for the actual smooth competitor

The quartic term is a difference of two ordinary bounded potential
densities.  The transformed field is represented at the origin by its
regular radial-factor quotient, so no integrability of the totalized
singular quotient is required.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- The quartic bridge for the actual quotient `u/f` is integrable on a
finite ball.  Its only inputs are regular radial factors, profile
continuity, and `C¹` regularity of the physical competitor. -/
theorem euclideanQuarticBridgeDensity_actual_quotient_integrable
    (m : ℕ) (R : ℝ)
    (f F Hf HF : ℝ → ℝ) (α β : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hβ : 0 < β)
    (hHf0 : Hf 0 = β) (hHF0 : HF 0 = α)
    (hfFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      f r = r * Hf (r ^ 2))
    (hFFactor : ∀ r : ℝ, 0 < r → r ≤ R →
      F r = r * HF (r ^ 2))
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hHf : ContDiff ℝ 1 Hf) (hHF : ContDiff ℝ 1 HF)
    (hfC0 : Continuous f) (hFC0 : Continuous F)
    (huC1 : ContDiffOn ℝ 1 u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R)) :
    Integrable
      (euclideanQuarticBridgeDensity m f F
        (fun x : GLEuclidean (m + 3) =>
          (f ‖x‖)⁻¹ • u x))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
  let z : GLEuclidean (m + 3) → GLEuclidean (m + 3) :=
    fun x => (f ‖x‖)⁻¹ • u x
  let v := energyQuotientNumerator (m + 3) f F α β u
  have hHfNe : ∀ x ∈ Metric.closedBall
      (0 : GLEuclidean (m + 3)) R,
      Hf (‖x‖ ^ 2) ≠ 0 :=
    radial_factor_ne_zero_on_closedBall (m + 3) R f Hf β
      hβ hHf0 hfFactor hfpos
  have hvC1 : ContDiffOn ℝ 1 v
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    energyQuotientNumerator_contDiffOn_of_radial_factors
      (m + 3) R f F Hf HF α β u hHf hHF
      hHf0 hHF0 hHfNe hfFactor hFFactor huC1
  have huOff : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, x ≠ 0 →
      u x = f ‖x‖ • z x := by
    intro x hx hx0
    exact (energyQuotient_product_eq_on_ball_of_profile_pos
      (m + 3) R f u hfpos x hx hx0).symm
  have hvOff : ∀ x ∈ Metric.ball
      (0 : GLEuclidean (m + 3)) R, x ≠ 0 →
      v x = F ‖x‖ • z x := by
    intro x _ hx0
    exact energyQuotientNumerator_eq_profile_quotient_off_origin
      (m + 3) f F α β u x hx0
  exact euclideanQuarticBridgeDensity_integrable_of_C0_representatives
    m R f F z u v huC1.continuousOn hvC1.continuousOn
    (hfC0.comp continuous_norm).continuousOn
    (hFC0.comp continuous_norm).continuousOn huOff hvOff

end

end BrezisOP6
