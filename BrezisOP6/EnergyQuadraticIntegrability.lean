import BrezisOP6.EnergyBridgeNonnegative

/-!
# Quadratic bridge integrability from the exact energy decomposition

The angular/Picone comparison requires integrability of the quadratic
bridge itself.  It follows from the two single-profile densities once the
nonnegative quartic term is integrable; no independent assumption on the
quadratic density is necessary.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The exact bridge decomposition transfers integrability to its
quadratic component. -/
theorem euclideanQuadraticBridgeDensity_integrable_of_bridge_quartic
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hbridge : Integrable
      (bridgeEnergyDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => f ‖y‖)
        (fun y : GLEuclidean (m + 3) => F ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2))
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hquartic : Integrable
      (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R))) :
    Integrable (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
  let b : GLEuclidean (m + 3) → ℝ :=
    bridgeEnergyDensity (m + 3)
      (fun y => f ‖y‖) (fun y => F ‖y‖)
      (euclideanGradientSq (m + 3) z)
      (fun y => ‖z y‖ ^ 2) (fun y => ‖y‖⁻¹ ^ 2)
  let q := euclideanQuadraticBridgeDensity m f F z
  let t := euclideanQuarticBridgeDensity m f F z
  have hpoint : q = fun x => 2 * b x - t x / 2 := by
    funext x
    have h := bridgeEnergyDensity_eq_quadratic_add_quartic m f F z x
    dsimp only [b, q, t]
    linarith
  change Integrable q (volume.restrict (Metric.ball
    (0 : GLEuclidean (m + 3)) R))
  rw [hpoint]
  exact (hbridge.const_mul 2).sub (hquartic.div_const 2)

/-- The quartic bridge is the difference of two ordinary bounded-field
potential densities wherever the profile products agree with the original
and transformed competitors.  The pointwise formula needs no division. -/
theorem euclideanQuarticBridgeDensity_eq_potential_contrast
    (m : ℕ) (f F : ℝ → ℝ)
    (z u v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3))
    (hu : u x = f ‖x‖ • z x)
    (hv : v x = F ‖x‖ • z x) :
    euclideanQuarticBridgeDensity m f F z x =
      (‖u x‖ ^ 2 - f ‖x‖ ^ 2) ^ 2 -
        (‖v x‖ ^ 2 - F ‖x‖ ^ 2) ^ 2 := by
  have hUnorm : ‖u x‖ ^ 2 = f ‖x‖ ^ 2 * ‖z x‖ ^ 2 := by
    rw [hu]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hVnorm : ‖v x‖ ^ 2 = F ‖x‖ ^ 2 * ‖z x‖ ^ 2 := by
    rw [hv]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hUnorm, hVnorm]
  unfold euclideanQuarticBridgeDensity
  ring

/-- For actual `C¹` competitors, the quartic bridge is integrable without
any separate growth estimate for the singular quotient.  Both potential
densities on the right are continuous on a compact ball; agreement away
from the origin suffices because a singleton has zero volume. -/
theorem euclideanQuarticBridgeDensity_integrable_of_C0_representatives
    (m : ℕ) (R : ℝ) (f F : ℝ → ℝ)
    (z u v : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hu : ContinuousOn u
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hv : ContinuousOn v
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hf : ContinuousOn
      (fun x : GLEuclidean (m + 3) => f ‖x‖)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (hF : ContinuousOn
      (fun x : GLEuclidean (m + 3) => F ‖x‖)
      (Metric.closedBall (0 : GLEuclidean (m + 3)) R))
    (huOff : ∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 →
      u x = f ‖x‖ • z x)
    (hvOff : ∀ x ∈ Metric.ball (0 : GLEuclidean (m + 3)) R,
      x ≠ 0 →
      v x = F ‖x‖ • z x) :
    Integrable (euclideanQuarticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
  let s : Set (GLEuclidean (m + 3)) := Metric.closedBall 0 R
  let a : GLEuclidean (m + 3) → ℝ := fun x =>
    (‖u x‖ ^ 2 - f ‖x‖ ^ 2) ^ 2 -
      (‖v x‖ ^ 2 - F ‖x‖ ^ 2) ^ 2
  have ha : ContinuousOn a s := by
    dsimp only [a]
    exact ((hu.norm.pow 2 |>.sub (hf.pow 2)).pow 2).sub
      ((hv.norm.pow 2 |>.sub (hF.pow 2)).pow 2)
  have haInt : Integrable a
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)) := by
    apply (ha.integrableOn_compact (isCompact_closedBall _ _)).mono_set
    intro x hx
    have hr : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using le_of_lt hr
  letI : NeZero (m + 3) := ⟨by omega⟩
  have hne : ∀ᵐ x : GLEuclidean (m + 3)
      ∂(volume : Measure (GLEuclidean (m + 3))), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hEq : (euclideanQuarticBridgeDensity m f F z) =ᵐ[
      volume.restrict (Metric.ball (0 : GLEuclidean (m + 3)) R)] a := by
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_ball]
      with x hx hxBall
    exact euclideanQuarticBridgeDensity_eq_potential_contrast
      m f F z u v x (huOff x hxBall hx) (hvOff x hxBall hx)
  exact haInt.congr hEq.symm

end

end BrezisOP6
