import BrezisOP6.ProfilePiconeIntervalInterior

/-!
# Nonnegative splitting of an integrable Picone density

Once the Picone density and boundary-flux derivative are integrable on a
positive annulus, the exact pointwise identity makes the sum of square
and remainder integrable.  Their nonnegativity then makes each summand
integrable separately.  This avoids separate quantitative bounds on the
two positive terms.
-/

namespace BrezisOP6

open MeasureTheory Set

noncomputable section

theorem annulus_nonnegative_parts_integrable_of_density_flux
    (D V S T : ℝ → ℝ) (δ R : ℝ) (hδR : δ ≤ R)
    (hD : IntervalIntegrable D volume δ R)
    (hV : IntervalIntegrable V volume δ R)
    (hEq : D =ᵐ[volume.restrict (Ioc δ R)]
      fun r => S r + V r + T r)
    (hSmeas : AEStronglyMeasurable S
      (volume.restrict (Ioc δ R)))
    (hTmeas : AEStronglyMeasurable T
      (volume.restrict (Ioc δ R)))
    (hSnonneg : ∀ᵐ r ∂volume.restrict (Ioc δ R), 0 ≤ S r)
    (hTnonneg : ∀ᵐ r ∂volume.restrict (Ioc δ R), 0 ≤ T r) :
    IntervalIntegrable S volume δ R ∧
      IntervalIntegrable T volume δ R := by
  have hSTeq : (fun r => D r - V r) =ᵐ[volume.restrict (Ioc δ R)]
      fun r => S r + T r := by
    filter_upwards [hEq] with r hr
    rw [hr]
    ring
  have hST : IntervalIntegrable (fun r => S r + T r) volume δ R := by
    apply (hD.sub hV).congr_ae
    simpa only [uIoc_of_le hδR] using hSTeq
  have hSTon : Integrable (fun r => S r + T r)
      (volume.restrict (Ioc δ R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mp hST
  have hSon : Integrable S (volume.restrict (Ioc δ R)) := by
    apply Integrable.mono' hSTon hSmeas
    filter_upwards [hSnonneg, hTnonneg] with r hs ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs] using
      (le_add_of_nonneg_right ht : S r ≤ S r + T r)
  have hTon : Integrable T (volume.restrict (Ioc δ R)) := by
    apply Integrable.mono' hSTon hTmeas
    filter_upwards [hSnonneg, hTnonneg] with r hs ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using
      (le_add_of_nonneg_left hs : T r ≤ S r + T r)
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mpr hSon,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδR).mpr hTon⟩

end

end BrezisOP6
