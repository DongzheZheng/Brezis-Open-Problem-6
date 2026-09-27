import BrezisOP6.SpherePolarIntegration
import BrezisOP6.EnergyBallIdentity

/-!
# The radial Jacobian as an ordinary interval integral

`SpherePolarIntegration` gives the actual Euclidean polar measure with radial
factor `volumeIoiPow`.  This module identifies integration against that
measure with the familiar `r^(n-1) dr` integral, first on the positive axis
and then on a positive-radius annulus.
-/

namespace BrezisOP6

open MeasureTheory Set Metric

noncomputable section

/-- Integrating against mathlib's polar radius measure is ordinary Lebesgue
integration with the Euclidean radial Jacobian. -/
theorem radius_integral_eq_weighted (n : ℕ) (f : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), f r.1 ∂(unitSphereRadiusMeasure n)) =
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r := by
  simp only [unitSphereRadiusMeasure, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => Real.toNNReal (a ^ (n - 1)) • f a),
    setIntegral_congr_fun measurableSet_Ioi]
  · intro r hr
    change Real.toNNReal (r ^ (n - 1)) • f r = r ^ (n - 1) * f r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.out.le _)]
    simp only [smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- The same conversion on a compact positive radial interval.  The choice
of `Ioc` matches mathlib's oriented interval integral exactly. -/
theorem radius_integral_annulus_eq_interval (n : ℕ)
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R) (f : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ),
        (Ioc ρ R).indicator f r.1 ∂(unitSphereRadiusMeasure n)) =
      ∫ r in ρ..R, r ^ (n - 1) * f r := by
  rw [radius_integral_eq_weighted]
  have hsub : Ioc ρ R ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact lt_trans hρ hr.1
  calc
    (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (Ioc ρ R).indicator f r) =
        ∫ r in Ioi (0 : ℝ),
          (Ioc ρ R).indicator (fun t => t ^ (n - 1) * f t) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      by_cases h : r ∈ Ioc ρ R <;> simp [Set.indicator, h]
    _ = ∫ r in Ioc ρ R, r ^ (n - 1) * f r := by
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.mpr hsub]
    _ = ∫ r in ρ..R, r ^ (n - 1) * f r :=
      (intervalIntegral.integral_of_le hρR).symm

end

end BrezisOP6
