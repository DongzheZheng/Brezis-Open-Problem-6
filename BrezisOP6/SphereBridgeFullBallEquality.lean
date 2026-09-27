import BrezisOP6.SphereBridgeFullBall

/-! # Exact spatial/spherical quadratic bridge integral identity. -/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology

theorem euclideanQuadraticBridge_ball_integral_eq_finiteFamily
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hQuadInt : Integrable
      (euclideanQuadraticBridgeDensity m f F z)
      (volume.restrict (Metric.ball
        (0 : GLEuclidean (m + 3)) R)))
    (hBridgeInt : IntervalIntegrable
      (vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz))
      volume 0 R)
    :
    (∫ x,
      euclideanQuadraticBridgeDensity m f F z x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R))) =
      ∫ r in (0 : ℝ)..R,
        vectorSphereBridgeDensity m f F
          (finiteBallSphereFamily (m + 3) R z)
          (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r := by
  let ρ := canonicalEnergyRadius R
  let q := euclideanQuadraticBridgeDensity m f F z
  let B := vectorSphereBridgeDensity m f F
    (finiteBallSphereFamily (m + 3) R z)
    (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
    (finiteBallSphereFamilyRadialL2 (m + 3) R z hz)
  have hqPos : IntegrableOn q (energyPositiveClosedBall (m + 3) R)
      volume := by
    change Integrable q (volume.restrict (energyPositiveClosedBall
      (m + 3) R))
    rw [energyPositiveClosedBall_restrict_eq_ball m R]
    exact hQuadInt
  have hPolarInt (j : ℕ) : Integrable
      (fun p : Metric.sphere
          (0 : GLEuclidean (m + 3)) 1 × Ioi (0 : ℝ) =>
        (Metric.ball (0 : GLEuclidean (m + 3)) (R + 1)).indicator
          ((energyPositiveAnnulus (m + 3) (ρ j) R).indicator q)
          (unitSpherePolarPoint (m + 3) p))
      ((unitSphereMeasure (m + 3)).prod
        (unitSphereRadiusMeasure (m + 3))) := by
    have hAnnInt : IntegrableOn q
        (energyPositiveAnnulus (m + 3) (ρ j) R) volume := by
      apply hqPos.mono_set
      intro x hx
      exact ⟨lt_trans (canonicalEnergyRadius_pos R hR j) hx.1,
        hx.2⟩
    exact annulus_polar_indicator_integrable_of_integrableOn
      (m + 3) (by omega) (ρ j) R
      (canonicalEnergyRadius_le R hR j) q hAnnInt
  have hspace : Tendsto
      (fun j => ∫ x in energyPositiveAnnulus (m + 3) (ρ j) R,
        q x) atTop
      (𝓝 (∫ x in energyPositiveClosedBall (m + 3) R, q x)) :=
    annulus_integral_tendsto_positiveBall (m + 3) R ρ
      (canonicalEnergyRadius_pos R hR)
      (canonicalEnergyRadius_antitone R hR)
      (canonicalEnergyRadius_tendsto_zero R) q hqPos
  have hrad : Tendsto (fun j => ∫ r in ρ j..R, B r) atTop
      (𝓝 (∫ r in (0 : ℝ)..R, B r)) :=
    finiteBallBridge_interval_tendsto m f F R hR z hz hBridgeInt
  have hEq (j : ℕ) :
      (∫ x in energyPositiveAnnulus (m + 3) (ρ j) R, q x) =
      ∫ r in ρ j..R, B r :=
    euclideanQuadraticBridge_annulus_eq_finiteFamily_interval
      m f F z (ρ j) R
      (canonicalEnergyRadius_pos R hR j)
      (canonicalEnergyRadius_le R hR j)
      hz (hPolarInt j)
  have hFun :
      (fun j => ∫ x in energyPositiveAnnulus (m + 3) (ρ j) R,
        q x) =
      (fun j => ∫ r in ρ j..R, B r) := funext hEq
  rw [hFun] at hspace
  have hIntegralEq :
      (∫ x in energyPositiveClosedBall (m + 3) R, q x) =
      ∫ r in (0 : ℝ)..R, B r :=
    tendsto_nhds_unique hspace hrad
  change (∫ x in Metric.ball (0 : GLEuclidean (m + 3)) R, q x) =
    ∫ r in (0 : ℝ)..R, B r
  rw [← energyPositiveClosedBall_integral_eq_ball m R q]
  exact hIntegralEq


end

end BrezisOP6
