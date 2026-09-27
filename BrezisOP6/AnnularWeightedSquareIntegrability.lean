import BrezisOP6.BridgeAnnularLocalIntegrability

/-!
# Removing compact-annulus derivative integrability assumptions

On a compact annulus a continuous positive weight has a uniform lower
bound.  Integrability of its product with a square therefore implies
integrability of the square.  Finite interval measure then gives
integrability of the absolute value as well.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem annular_square_intervalIntegrable_of_weighted
    (w g : ℝ → ℝ) (δ R κ : ℝ)
    (hδR : δ ≤ R) (hκ : 0 < κ)
    (hw : ∀ r ∈ Icc δ R, κ ≤ w r)
    (hweighted : IntervalIntegrable
      (fun r => w r * g r ^ 2) volume δ R)
    (hSqMeas : AEStronglyMeasurable (fun r => g r ^ 2)
      (volume.restrict (Ioc δ R))) :
    IntervalIntegrable (fun r => g r ^ 2) volume δ R := by
  have hMaj : Integrable
      (fun r => κ⁻¹ * (w r * g r ^ 2))
      (volume.restrict (Ioc δ R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mp
      (hweighted.const_mul κ⁻¹)
  have hSqOn : Integrable (fun r => g r ^ 2)
      (volume.restrict (Ioc δ R)) := by
    apply Integrable.mono' hMaj hSqMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r ∈ Icc δ R := ⟨hr.1.le, hr.2⟩
    have hκg : κ * g r ^ 2 ≤ w r * g r ^ 2 :=
      mul_le_mul_of_nonneg_right (hw r hr') (sq_nonneg _)
    have hbound : g r ^ 2 ≤ κ⁻¹ * (w r * g r ^ 2) := by
      have h := (le_div_iff₀ hκ).2 (by
        simpa only [mul_comm] using hκg)
      simpa only [div_eq_mul_inv, mul_comm] using h
    calc
      ‖g r ^ 2‖ = g r ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g r))]
      _ ≤ κ⁻¹ * (w r * g r ^ 2) := hbound
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mpr hSqOn

theorem annular_abs_intervalIntegrable_of_square
    (g : ℝ → ℝ) (δ R : ℝ) (hδR : δ ≤ R)
    (hSq : IntervalIntegrable (fun r => g r ^ 2) volume δ R)
    (hAbsMeas : AEStronglyMeasurable (fun r => |g r|)
      (volume.restrict (Ioc δ R))) :
    IntervalIntegrable (fun r => |g r|) volume δ R := by
  have hMaj : Integrable (fun r => 1 + g r ^ 2)
      (volume.restrict (Ioc δ R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mp
      ((intervalIntegrable_const).add hSq)
  have hAbsOn : Integrable (fun r => |g r|)
      (volume.restrict (Ioc δ R)) := by
    apply Integrable.mono' hMaj hAbsMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have h0 : 0 ≤ |g r| := abs_nonneg _
    have hBound : |g r| ≤ 1 + g r ^ 2 := by
      nlinarith [sq_nonneg (|g r| - 1), sq_abs (g r)]
    have hMaj0 : 0 ≤ 1 + g r ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hMaj0]
      using hBound
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mpr hAbsOn

end

end BrezisOP6
