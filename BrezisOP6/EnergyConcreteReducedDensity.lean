import BrezisOP6.EnergyC1Integrability
import BrezisOP6.EnergyQuotientDensityBound
import BrezisOP6.EnergyProfileOriginBounds

/-!
# Reduced density from the regular-origin profile and a smooth numerator

The actual quotient may grow like `r⁻¹` at a scalar collision, and its
gradient like `r⁻²`.  The profile-weighted density nevertheless has only
an inverse-square pole.  This file combines that pointwise estimate with
the three-dimensional critical integrability theorem and compact `C¹`
bounds for the original field.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- The quotient density is ordinarily continuous at every positive radius
when the profile is `C¹` and stays positive on the ball.  This supplies
the outer-annulus input of the inverse-square argument. -/
theorem singleProfileDensity_quotient_continuousOn_positiveBall
    (m : ℕ) (R : ℝ) (p : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hpC1 : ContDiff ℝ 1 p) (huC1 : ContDiff ℝ 1 u)
    (hpPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < p r) :
    ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • u y))
        (fun y => ‖(p ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (energyPositiveClosedBall (m + 3) R) := by
  let E := GLEuclidean (m + 3)
  let s : Set E := {x | 0 < ‖x‖ ∧ p ‖x‖ ≠ 0}
  have hsOpen : IsOpen s := by
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_ne_fun (hpC1.continuous.comp continuous_norm) continuous_const)
  have hn : ContDiffOn ℝ 1 (fun x : E => ‖x‖) s := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp hx.1
    exact (contDiffAt_norm ℝ hx0).contDiffWithinAt
  have hpOn : ContDiffOn ℝ 1 (fun x : E => p ‖x‖) s :=
    hpC1.comp_contDiffOn hn
  have hz : ContDiffOn ℝ 1
      (fun x : E => (p ‖x‖)⁻¹ • u x) s :=
    (hpOn.inv (fun x hx => hx.2)).smul huC1.contDiffOn
  have hsub : energyPositiveClosedBall (m + 3) R ⊆ s := by
    intro x hx
    exact ⟨hx.1, ne_of_gt (hpPos ‖x‖ hx.1 hx.2)⟩
  have hD := singleProfileDensity_continuousOn m p
    (fun x : E => (p ‖x‖)⁻¹ • u x) s
    (fun x hx => norm_pos_iff.mp hx.1)
    hpOn.continuousOn hz.continuousOn
    (hz.continuousOn_fderiv_of_isOpen hsOpen (by norm_num))
  exact hD.mono hsub

/-- A regular-origin Taylor profile and a globally `C¹` numerator make
the reduced density integrable on the punctured ball.  Only ordinary
continuity of the density on the outer annulus remains an input. -/
theorem energyReducedSpatialDensity_quotient_integrableOn_of_taylor_C1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (p : ℝ → ℝ) (α A B : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hp0 : p 0 = 0)
    (hα : 0 < α)
    (hTaylor : RadialOriginTaylorOn p α A B R)
    (hpDiff : ∀ r, 0 < r → r < R → DifferentiableAt ℝ p r)
    (hpMeas : Measurable p)
    (huC1 : ContDiff ℝ 1 u)
    (houter : ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • u y))
        (fun y => ‖(p ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (energyPositiveClosedBall (m + 3) R)) :
    IntegrableOn
      (energyReducedSpatialDensity m p
        (fun y : GLEuclidean (m + 3) =>
          (p ‖y‖)⁻¹ • u y))
      (energyPositiveClosedBall (m + 3) R) volume := by
  obtain ⟨δ, Cdp, Cratio, Cp, hδpos, hδR,
    hCdp, hCratio, hCp, hpBounds⟩ :=
    radial_origin_local_flux_bounds_on hR hα hTaylor
  have hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    huC1.continuous.continuousOn
  have hdu : ContinuousOn (fderiv ℝ u)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R) :=
    (huC1.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨Cw, Cg, hCw, hCg, hwBounds⟩ :=
    euclideanC1_closedBall_bounds (m + 3) R u hu hdu
  have hInner : IntegrableOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • u y))
        (fun y => ‖(p ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.ball (0 : GLEuclidean (m + 3)) δ) volume := by
    apply singleProfileDensity_quotient_integrableOn_ball m δ p u
      Cdp Cratio Cw Cg Cp hp0 hCdp hCratio hCw hCg hCp
    · intro r hrpos hrδ
      have hrR : r < R := lt_of_lt_of_le hrδ hδR
      obtain ⟨hpne, hdp, hratio, hpb⟩ :=
        hpBounds r hrpos hrδ
      exact ⟨(hpDiff r hrpos hrR).hasDerivAt,
        hpne, hdp, hratio, hpb⟩
    · intro x hx
      have hxR : x ∈ Metric.closedBall
          (0 : GLEuclidean (m + 3)) R := by
        have hxδ : ‖x‖ < δ := by
          simpa only [Metric.mem_ball, dist_zero_right] using hx
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          le_trans (le_of_lt hxδ) hδR
      obtain ⟨hval, hgrad⟩ := hwBounds x hxR
      exact ⟨huC1.differentiable_one x, hval, hgrad⟩
    · exact hpMeas
    · exact huC1.continuous.measurable
  have hOuter : ContinuousOn
      (singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3)
          (fun y => (p ‖y‖)⁻¹ • u y))
        (fun y => ‖(p ‖y‖)⁻¹ • u y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R \
        Metric.ball (0 : GLEuclidean (m + 3)) δ) := by
    apply houter.mono
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
    have hxδ : δ ≤ ‖x‖ := by
      by_contra hnot
      have hlt : ‖x‖ < δ := lt_of_not_ge hnot
      exact hx.2 (by simpa only [Metric.mem_ball, dist_zero_right] using hlt)
    exact ⟨lt_of_lt_of_le hδpos hxδ, hxR⟩
  exact energyReducedSpatialDensity_quotient_integrableOn_of_inner_outer
    m R δ p u hInner hOuter

/-- In the globally `C¹` profile setting the outer-annulus continuity
follows automatically, leaving only the regular-origin Taylor data and
positivity of the profile. -/
theorem energyReducedSpatialDensity_quotient_integrableOn_of_taylor_globalC1
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (p : ℝ → ℝ) (α A B : ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hp0 : p 0 = 0) (hα : 0 < α)
    (hTaylor : RadialOriginTaylorOn p α A B R)
    (hpC1 : ContDiff ℝ 1 p) (huC1 : ContDiff ℝ 1 u)
    (hpPos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < p r) :
    IntegrableOn
      (energyReducedSpatialDensity m p
        (fun y : GLEuclidean (m + 3) =>
          (p ‖y‖)⁻¹ • u y))
      (energyPositiveClosedBall (m + 3) R) volume := by
  exact energyReducedSpatialDensity_quotient_integrableOn_of_taylor_C1
    m R hR p α A B u hp0 hα hTaylor
    (fun r _ _ => hpC1.differentiable_one r)
    hpC1.continuous.measurable huC1
    (singleProfileDensity_quotient_continuousOn_positiveBall
      m R p u hpC1 huC1 hpPos)

end

end BrezisOP6
