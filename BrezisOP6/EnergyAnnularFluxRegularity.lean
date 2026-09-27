import BrezisOP6.EnergyConcreteSecondInteriorData

/-!
# Annular regularity of the actual quotient flux

On each positive-radius closed annulus, the radial flux of a `C¹`
numerator and a nonvanishing quotient denominator is itself `C¹`,
provided the profile and its first derivative are `C¹`.  This supplies
both the endpoint continuity and interval-integrability fields used by
the radial fundamental theorem of calculus.
-/

namespace BrezisOP6

open MeasureTheory Metric Set

noncomputable section

theorem radialBoundaryFlux_shared_quotient_contDiffOn_positive
    (m : ℕ) (p f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (hpC1 : ContDiff ℝ 1 p)
    (hdpC1 : ContDiff ℝ 1 (deriv p))
    (hfC1 : ContDiff ℝ 1 f)
    (huC1 : ContDiff ℝ 1 u) :
    ContDiffOn ℝ 1
      (radialBoundaryFlux m p
        (energyRaySq (m + 3)
          (fun x => (f ‖x‖)⁻¹ • u x) ω))
      {r : ℝ | 0 < r ∧ f r ≠ 0} := by
  let s : Set ℝ := {r | 0 < r ∧ f r ≠ 0}
  have hsOpen : IsOpen s :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_ne_fun hfC1.continuous continuous_const)
  have hRay : ContDiff ℝ 1
      (fun r : ℝ => energySphereRay (m + 3) ω r) := by
    simpa only [energySphereRay] using
      (contDiff_id : ContDiff ℝ 1 (fun r : ℝ => r)).smul
        (contDiff_const : ContDiff ℝ 1
          (fun _ : ℝ => (ω : GLEuclidean (m + 3))))
  have huRay : ContDiff ℝ 1
      (fun r : ℝ => u (energySphereRay (m + 3) ω r)) :=
    huC1.comp hRay
  have hfInv : ContDiffOn ℝ 1 (fun r : ℝ => (f r)⁻¹) s :=
    hfC1.contDiffOn.inv (fun r hr => hr.2)
  have hzRay : ContDiffOn ℝ 1
      (fun r : ℝ => (f r)⁻¹ •
        u (energySphereRay (m + 3) ω r)) s :=
    hfInv.smul huRay.contDiffOn
  have hNormSq : ContDiff ℝ 1
      (fun y : GLEuclidean (m + 3) => ‖y‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hWRay : ContDiffOn ℝ 1
      (fun r : ℝ => ‖(f r)⁻¹ •
        u (energySphereRay (m + 3) ω r)‖ ^ 2) s :=
    hNormSq.comp_contDiffOn hzRay
  have hReg : ContDiffOn ℝ 1
      (fun r : ℝ => r ^ (m + 2) * p r * deriv p r *
        (‖(f r)⁻¹ • u (energySphereRay (m + 3) ω r)‖ ^ 2 - 1))
      s := by
    exact (((contDiff_id.pow (m + 2)).contDiffOn.mul
      hpC1.contDiffOn).mul hdpC1.contDiffOn).mul
        (hWRay.sub contDiffOn_const)
  apply hReg.congr
  intro r hr
  simp only [radialBoundaryFlux, energyRaySq]
  rw [energySphereRay_norm (m + 3) ω r hr.1.le]

theorem radialBoundaryFlux_shared_quotient_annulus_regular
    (m : ℕ) (R ρ : ℝ) (p f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1)
    (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hpC1 : ContDiff ℝ 1 p)
    (hdpC1 : ContDiff ℝ 1 (deriv p))
    (hfC1 : ContDiff ℝ 1 f)
    (huC1 : ContDiff ℝ 1 u)
    (hfpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r) :
    ContinuousOn
      (radialBoundaryFlux m p
        (energyRaySq (m + 3)
          (fun x => (f ‖x‖)⁻¹ • u x) ω))
      (uIcc ρ R) ∧
    IntervalIntegrable
      (deriv (radialBoundaryFlux m p
        (energyRaySq (m + 3)
          (fun x => (f ‖x‖)⁻¹ • u x) ω)))
      volume ρ R := by
  let s : Set ℝ := {r | 0 < r ∧ f r ≠ 0}
  have hsOpen : IsOpen s :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_ne_fun hfC1.continuous continuous_const)
  have hFlux : ContDiffOn ℝ 1
      (radialBoundaryFlux m p
        (energyRaySq (m + 3)
          (fun x => (f ‖x‖)⁻¹ • u x) ω)) s :=
    radialBoundaryFlux_shared_quotient_contDiffOn_positive
      m p f u ω hpC1 hdpC1 hfC1 huC1
  have hsub : uIcc ρ R ⊆ s := by
    rw [uIcc_of_le hρR]
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hρ hr.1
    exact ⟨hrpos, ne_of_gt (hfpos r hrpos hr.2)⟩
  constructor
  · exact hFlux.continuousOn.mono hsub
  · exact ((hFlux.continuousOn_deriv_of_isOpen hsOpen
      (by norm_num)).mono hsub).intervalIntegrable

end

end BrezisOP6
