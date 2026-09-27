import BrezisOP6.EnergyAnnulusIntegral

/-!
# Integrability under the polar-coordinate homeomorphism

The annular polar-integrability hypothesis follows from ordinary
Lebesgue integrability of the spatial density on that annulus.  The
homeomorphism preserves the product of the concrete sphere measure and
the weighted radius measure.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem annulus_polar_indicator_integrable_of_integrableOn
    (n : ℕ) (hn : 1 ≤ n) (ρ R : ℝ)
    (hρR : ρ ≤ R) (h : GLEuclidean n → ℝ)
    (hAnnInt : IntegrableOn h
      (energyPositiveAnnulus n ρ R) volume) :
    Integrable
      (fun q : Metric.sphere (0 : GLEuclidean n) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean n) (R + 1)).indicator
          ((energyPositiveAnnulus n ρ R).indicator h)
          (unitSpherePolarPoint n q))
      ((unitSphereMeasure n).prod (unitSphereRadiusMeasure n)) := by
  letI : NeZero n := ⟨by omega⟩
  let E := GLEuclidean n
  let μ : Measure E := volume
  let A : Set E := energyPositiveAnnulus n ρ R
  let B : Set E := Metric.ball 0 (R + 1)
  let d : E → ℝ := B.indicator (A.indicator h)
  have hAB : A ⊆ B := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hx.2
    simp only [B, Metric.mem_ball, dist_zero_right]
    linarith
  have hAInt : Integrable (A.indicator h) μ :=
    (integrable_indicator_iff
      (measurableSet_energyPositiveAnnulus n ρ R)).mpr hAnnInt
  have hInd : d = A.indicator h := by
    funext x
    by_cases hx : x ∈ A
    · simp [d, Set.indicator, hx, hAB hx]
    · simp [d, Set.indicator, hx]
  have hdInt : Integrable d μ := by rw [hInd]; exact hAInt
  have hSub : Integrable
      (fun x : ({(0 : E)}ᶜ : Set E) => d x.1)
      (μ.comap (↑)) := by
    simpa only [Function.comp_def] using
      ((integrableOn_iff_comap_subtypeVal
        (measurableSet_singleton (0 : E)).compl).mp
        hdInt.integrableOn)
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
    |>.integrable_comp_emb
      (Homeomorph.measurableEmbedding _)
      (g := fun q => d ((homeomorphUnitSphereProd E).symm q : E))
  have hpolar : Integrable
      (fun q : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) =>
        d ((homeomorphUnitSphereProd E).symm q : E))
      (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    apply hmp.mp
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hSub
  have hmeasure :
      μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
      (unitSphereMeasure n).prod (unitSphereRadiusMeasure n) := by
    simp [μ, E, unitSphereMeasure, unitSphereRadiusMeasure]
  rw [hmeasure] at hpolar
  simpa only [d, A, B, unitSpherePolarPoint,
    homeomorphUnitSphereProd_symm_apply_coe] using hpolar

end

end BrezisOP6
