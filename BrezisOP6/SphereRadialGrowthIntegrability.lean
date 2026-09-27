import BrezisOP6.EnergyRadialTermwiseBound

/-!
# Integrability of radial bridge densities from polynomial growth

The singular quotient may have a first-order pole, but in dimension
`m + 3` the spherical Jacobian makes each bridge term `O(r^m)`.
This lemma records the final measure-theoretic step separately from the
pointwise quotient estimates.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set

theorem intervalIntegrable_of_abs_le_power
    (m : ℕ) (R C : ℝ) (h : ℝ → ℝ)
    (hR : 0 ≤ R)
    (hC : 0 ≤ C)
    (hMeas : AEStronglyMeasurable h
      (volume.restrict (Ioc (0 : ℝ) R)))
    (hbound : ∀ r ∈ Ioc (0 : ℝ) R,
      |h r| ≤ C * r ^ m) :
    IntervalIntegrable h volume 0 R := by
  have hmajor : IntervalIntegrable
      (fun r : ℝ => C * r ^ m) volume 0 R :=
    (continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 R
  have hMeas' : AEStronglyMeasurable h
      (volume.restrict (uIoc (0 : ℝ) R)) := by
    simpa only [uIoc_of_le hR] using hMeas
  apply IntervalIntegrable.mono_fun' hmajor hMeas'
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hR] at hr
  simpa only [Real.norm_eq_abs] using hbound r hr

/-- The value at the outer endpoint is irrelevant to interval
integrability, so a bound holding almost everywhere is sufficient. -/
theorem intervalIntegrable_of_ae_abs_le_power
    (m : ℕ) (R C : ℝ) (h : ℝ → ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hMeas : AEStronglyMeasurable h
      (volume.restrict (Ioc (0 : ℝ) R)))
    (hbound : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) R)),
      |h r| ≤ C * r ^ m) :
    IntervalIntegrable h volume 0 R := by
  have hmajor : IntervalIntegrable
      (fun r : ℝ => C * r ^ m) volume 0 R :=
    (continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 R
  have hMeas' : AEStronglyMeasurable h
      (volume.restrict (uIoc (0 : ℝ) R)) := by
    simpa only [uIoc_of_le hR] using hMeas
  apply IntervalIntegrable.mono_fun' hmajor hMeas'
  simpa only [uIoc_of_le hR, Real.norm_eq_abs] using hbound

end

end BrezisOP6
