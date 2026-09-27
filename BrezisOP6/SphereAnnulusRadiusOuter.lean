import BrezisOP6.SpherePolarAnnulusIntegrability

/-!
# Annular polar formula with radius as the outer variable

The signed polar integrand is integrable by hypothesis.  Fubini is applied
in the original product measure `sphere × volumeIoiPow`; conversion of the
weighted radius measure to a Lebesgue interval is performed afterwards.
This avoids a separate integrability premise on a swapped, reweighted
product space.
-/

namespace BrezisOP6

noncomputable section

open MeasureTheory Set Metric

theorem annulus_integral_eq_interval_sphere_integral
    (n : ℕ) (hn : 1 ≤ n) (ρ R : ℝ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (h : GLEuclidean n → ℝ)
    (hPolarInt : Integrable
      (fun q : Metric.sphere (0 : GLEuclidean n) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean n) (R + 1)).indicator
          ((energyPositiveAnnulus n ρ R).indicator h)
          (unitSpherePolarPoint n q))
      ((unitSphereMeasure n).prod (unitSphereRadiusMeasure n))) :
    (∫ x in energyPositiveAnnulus n ρ R, h x) =
      ∫ r in ρ..R,
        r ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
            h (energySphereRay n ω r) ∂(unitSphereMeasure n))
        ∂volume := by
  let A : Set (GLEuclidean n) := energyPositiveAnnulus n ρ R
  let B : Set (GLEuclidean n) := Metric.ball 0 (R + 1)
  have hAB : A ⊆ B := by
    intro x hx
    have hxR : ‖x‖ ≤ R := hx.2
    simp only [B, Metric.mem_ball, dist_zero_right]
    linarith
  have hpoint (ω : Metric.sphere (0 : GLEuclidean n) 1)
      (r : Ioi (0 : ℝ)) :
      B.indicator (A.indicator h) (unitSpherePolarPoint n (ω, r)) =
      (Ioc ρ R).indicator
        (fun t : ℝ => h (energySphereRay n ω t)) r.1 := by
    have hray : unitSpherePolarPoint n (ω, r) =
        energySphereRay n ω r.1 := rfl
    have hnorm : ‖unitSpherePolarPoint n (ω, r)‖ = r.1 := by
      rw [hray]
      exact energySphereRay_norm n ω r.1 r.2.le
    have hann : unitSpherePolarPoint n (ω, r) ∈ A ↔
        r.1 ∈ Ioc ρ R := by
      simp [A, energyPositiveAnnulus, hnorm]
    by_cases hr : r.1 ∈ Ioc ρ R
    · have ha := hann.mpr hr
      have hb := hAB ha
      simp [Set.indicator, ha, hb, hr]
      exact congrArg h hray
    · have ha : unitSpherePolarPoint n (ω, r) ∉ A :=
        fun hx => hr (hann.mp hx)
      simp [Set.indicator, ha, hr]
  have hpolar := ball_integral_eq_polar_product n hn (R + 1)
    (A.indicator h)
  calc
    (∫ x in A, h x) = ∫ x in B, A.indicator h x := by
      rw [setIntegral_indicator (measurableSet_energyPositiveAnnulus n ρ R),
        Set.inter_eq_right.mpr hAB]
    _ = ∫ q : Metric.sphere (0 : GLEuclidean n) 1 × Ioi (0 : ℝ),
          B.indicator (A.indicator h) (unitSpherePolarPoint n q)
            ∂((unitSphereMeasure n).prod (unitSphereRadiusMeasure n)) :=
      hpolar
    _ = ∫ r : Ioi (0 : ℝ),
          (∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
            B.indicator (A.indicator h)
              (unitSpherePolarPoint n (ω, r))
              ∂(unitSphereMeasure n))
            ∂(unitSphereRadiusMeasure n) :=
      integral_prod_symm _ hPolarInt
    _ = ∫ r : Ioi (0 : ℝ),
          (Ioc ρ R).indicator
            (fun t : ℝ =>
              ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
                h (energySphereRay n ω t) ∂(unitSphereMeasure n)) r.1
            ∂(unitSphereRadiusMeasure n) := by
      apply integral_congr_ae
      filter_upwards [] with r
      calc
        _ = ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
              (Ioc ρ R).indicator
                (fun t : ℝ => h (energySphereRay n ω t)) r.1
                ∂(unitSphereMeasure n) := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact hpoint ω r
        _ = _ := by
          by_cases hr : r.1 ∈ Ioc ρ R <;>
            simp [Set.indicator, hr]
    _ = _ := radius_integral_annulus_eq_interval
      n ρ R hρ hρR
      (fun t : ℝ =>
        ∫ ω : Metric.sphere (0 : GLEuclidean n) 1,
          h (energySphereRay n ω t) ∂(unitSphereMeasure n))

end

end BrezisOP6
