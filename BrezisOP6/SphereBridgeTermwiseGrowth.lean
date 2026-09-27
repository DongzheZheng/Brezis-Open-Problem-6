import BrezisOP6.SphereRadialGrowthIntegrability
import BrezisOP6.SphereRealization
import BrezisOP6.BridgeDecomposition

/-!
# Polynomial bounds for Hilbert spherical bridge terms

The profile contrast is controlled by the square of the larger profile.
Weighted gradient and quotient bounds then control the radial and
zeroth-order pieces.  The tangential piece is kept as a separate
nonnegative-energy estimate, so no cancellation between signed terms
is used to infer absolute integrability.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory

theorem bridgeQuadraticDensity_abs_le_power_of_termwise
    (m : ℕ) (r f d angular A B C D : ℝ)
    (v dv : UnitSphereL2 (m + 3))
    (hr : 0 < r) (hd0 : 0 ≤ d) (hdle : d ≤ f ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hG : f ^ 2 * ‖dv‖ ^ 2 ≤ A + B * r⁻¹ ^ 2)
    (hZ : f ^ 2 * ‖v‖ ^ 2 ≤ C)
    (hAngular : |d * angular| ≤ D) :
    |r ^ (m + 2) * d * ‖dv‖ ^ 2 +
      r ^ m * d * (angular - (m + 2 : ℝ) * ‖v‖ ^ 2)| ≤
      r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C + D) := by
  have hcore := radial_bridge_termwise_abs_bound
    m r f d (‖dv‖ ^ 2) (‖v‖ ^ 2) A B C
    hr hd0 hdle (sq_nonneg _) (sq_nonneg _)
    hA hB hC hG hZ
  have hrm : 0 ≤ r ^ m := pow_nonneg hr.le _
  have hAngularScaled :
      |r ^ m * d * angular| ≤ r ^ m * D := by
    rw [mul_assoc]
    rw [abs_mul, abs_of_nonneg hrm]
    exact mul_le_mul_of_nonneg_left hAngular hrm
  calc
    |r ^ (m + 2) * d * ‖dv‖ ^ 2 +
      r ^ m * d * (angular - (m + 2 : ℝ) * ‖v‖ ^ 2)| =
        |(r ^ (m + 2) * d * ‖dv‖ ^ 2 -
          (m + 2 : ℝ) * r ^ m * d * ‖v‖ ^ 2) +
          r ^ m * d * angular| := by congr 1 <;> ring
    _ ≤ |r ^ (m + 2) * d * ‖dv‖ ^ 2 -
          (m + 2 : ℝ) * r ^ m * d * ‖v‖ ^ 2| +
          |r ^ m * d * angular| := abs_add_le _ _
    _ ≤ r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C) +
          r ^ m * D := add_le_add hcore hAngularScaled
    _ = r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C + D) := by ring

theorem bridgeMeanDensity_abs_le_power_of_termwise
    (m : ℕ) (r f d dc c A B C : ℝ)
    (hr : 0 < r) (hd0 : 0 ≤ d) (hdle : d ≤ f ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hG : f ^ 2 * dc ^ 2 ≤ A + B * r⁻¹ ^ 2)
    (hZ : f ^ 2 * c ^ 2 ≤ C) :
    |r ^ (m + 2) * d * dc ^ 2 -
      (m + 2 : ℝ) * r ^ m * d * c ^ 2| ≤
      r ^ m * (A * r ^ 2 + B + (m + 2 : ℝ) * C) := by
  exact radial_bridge_termwise_abs_bound m r f d (dc ^ 2)
    (c ^ 2) A B C hr hd0 hdle (sq_nonneg _) (sq_nonneg _)
    hA hB hC hG hZ

end

end BrezisOP6
