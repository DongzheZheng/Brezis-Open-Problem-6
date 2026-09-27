import BrezisOP6.BridgeDecomposition

/-!
# The coercive remainder in the angular bridge

The nonnegative bridge estimate also has an exact remainder.  Recording the
identity separately makes its equality case available for uniqueness of a
minimizer, without invoking a harmonic expansion at this algebraic stage.
-/

namespace BrezisOP6

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem bridgeQuadraticDensity_sub_mean_eq_remainder
    (m : ℕ) (e v dv : H) (r d c dc angular : ℝ)
    (he : ‖e‖ = 1)
    (hv : inner ℝ (v - c • e) e = 0)
    (hdv : inner ℝ (dv - dc • e) e = 0) :
    r ^ (m + 2) * d * ‖dv‖ ^ 2 +
        r ^ m * d * (angular - (m + 2 : ℝ) * ‖v‖ ^ 2) -
      (r ^ (m + 2) * d * dc ^ 2 -
        (m + 2 : ℝ) * r ^ m * d * c ^ 2) =
      r ^ (m + 2) * d * ‖dv - dc • e‖ ^ 2 +
        r ^ m * d *
          (angular - (m + 2 : ℝ) * ‖v - c • e‖ ^ 2) := by
  have hvnorm := norm_sq_eq_mean_sq_add_orthogonal e v c he hv
  have hdvnorm := norm_sq_eq_mean_sq_add_orthogonal e dv dc he hdv
  rw [hvnorm, hdvnorm]
  ring

end

end BrezisOP6
