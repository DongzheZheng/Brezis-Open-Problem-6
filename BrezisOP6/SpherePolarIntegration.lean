import BrezisOP6.SphereRealization

/-!
# Polar integration on the actual Euclidean ball

The polar-coordinate measure-preserving homeomorphism in mathlib sends
Lebesgue measure away from the origin to the product of `volume.toSphere`
and the radius measure `volumeIoiPow`.  The first theorem applies this
identity to an arbitrary scalar density restricted to a ball.  The
integrability assumption of the second theorem permits Fubini, separating
the angular and radial integrals.

This file only changes variables.  It makes no claim about gradients of a
quotient field, which belong to the separate PDE energy calculation.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

/-- Radius measure in the polar coordinate formula for `ℝⁿ`. -/
def unitSphereRadiusMeasure (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  Measure.volumeIoiPow (n - 1)

instance (n : ℕ) : SigmaFinite (unitSphereRadiusMeasure n) := by
  unfold unitSphereRadiusMeasure
  infer_instance

/-- The actual inverse polar-coordinate map `(ω,r) ↦ rω`. -/
def unitSpherePolarPoint (n : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin n) :=
  (p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))

/-- Exact ball polar change of variables.  `volume.toSphere` includes the
usual surface-area normalization, while `volumeIoiPow (n-1)` contributes
the radial density `r^(n-1)`.  The formula is valid for any scalar density
with the Bochner integral convention of mathlib. -/
theorem ball_integral_eq_polar_product
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, h x) =
      ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ),
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator h
          (unitSpherePolarPoint n p)
        ∂((unitSphereMeasure n).prod (unitSphereRadiusMeasure n)) := by
  letI : NeZero n := ⟨by omega⟩
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := MeasureTheory.volume
  have hsub :
      (∫ x : E, (Metric.ball (0 : E) R).indicator h x ∂μ) =
        ∫ x : ({(0 : E)}ᶜ : Set E),
          (Metric.ball (0 : E) R).indicator h x.1 ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton (0 : E)).compl
      (fun x : E => (Metric.ball (0 : E) R).indicator h x),
      restrict_compl_singleton]
  have hpolar :
      (∫ x : ({(0 : E)}ᶜ : Set E),
          (Metric.ball (0 : E) R).indicator h x.1 ∂(μ.comap (↑))) =
        ∫ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ),
          (Metric.ball (0 : E) R).indicator h
            (unitSpherePolarPoint n p)
          ∂((unitSphereMeasure n).prod (unitSphereRadiusMeasure n)) := by
    have hmeasure :
        μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) =
          (unitSphereMeasure n).prod (unitSphereRadiusMeasure n) := by
      simp [μ, E, unitSphereMeasure, unitSphereRadiusMeasure]
    have hpoint (p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ)) :
        ((homeomorphUnitSphereProd E).symm p : E) =
          unitSpherePolarPoint n p := by
      simp [unitSpherePolarPoint, homeomorphUnitSphereProd_symm_apply_coe]
    calc
      _ = ∫ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ),
            (Metric.ball (0 : E) R).indicator h
              ((homeomorphUnitSphereProd E).symm p : E)
            ∂(μ.toSphere.prod
              (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
          simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
            μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
              (Homeomorph.measurableEmbedding _)
              ((Metric.ball (0 : E) R).indicator h ∘ Subtype.val ∘
                (homeomorphUnitSphereProd E).symm)
      _ = _ := by
          rw [hmeasure]
          apply integral_congr_ae
          filter_upwards [] with p
          rw [hpoint p]
  calc
    _ = ∫ x : E, (Metric.ball (0 : E) R).indicator h x ∂μ := by
          rw [integral_indicator measurableSet_ball]
    _ = _ := hsub.trans hpolar

/-- Fubini's theorem turns the polar product integral into a genuine
surface integral of radial integrals.  Integrability is written on the
transformed density so the theorem also covers signed energy differences. -/
theorem ball_integral_eq_sphere_integral_radius_integral
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hPolarInt : Integrable
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
          Ioi (0 : ℝ) =>
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator h
          (unitSpherePolarPoint n p))
      ((unitSphereMeasure n).prod (unitSphereRadiusMeasure n))) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, h x) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ r : Ioi (0 : ℝ),
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator h
            (unitSpherePolarPoint n (ω, r))
          ∂(unitSphereRadiusMeasure n)
        ∂(unitSphereMeasure n) := by
  rw [ball_integral_eq_polar_product n hn R h]
  exact integral_prod _ hPolarInt

end

end BrezisOP6
