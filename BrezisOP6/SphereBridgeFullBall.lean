import BrezisOP6.SphereBridgeAnnulusFinite
import BrezisOP6.EnergyRadiusExhaustion
import BrezisOP6.EnergyOpenBall

/-!
# The quadratic bridge on the actual open ball

Annular polar integration, Fubini, and the canonical monotone exhaustion
identify the signed Euclidean quadratic bridge with the interval integral
of the finite-ball Hilbert bridge.  The only analytic hypotheses are the
ordinary integrability conditions for these signed integrals.
-/

namespace BrezisOP6

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology

theorem finiteBallBridge_interval_tendsto
    (m : ℕ) (f F : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hz : ContDiffOn ℝ 1 z {x | 0 < ‖x‖ ∧ ‖x‖ < R})
    (hBridgeInt : IntervalIntegrable
      (vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz))
      volume 0 R) :
    Tendsto (fun j : ℕ =>
      ∫ r in canonicalEnergyRadius R j..R,
        vectorSphereBridgeDensity m f F
          (finiteBallSphereFamily (m + 3) R z)
          (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r)
      atTop
      (𝓝 (∫ r in (0 : ℝ)..R,
        vectorSphereBridgeDensity m f F
          (finiteBallSphereFamily (m + 3) R z)
          (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
          (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r)) := by
  let ρ := canonicalEnergyRadius R
  let q := vectorSphereBridgeDensity m f F
    (finiteBallSphereFamily (m + 3) R z)
    (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
    (finiteBallSphereFamilyRadialL2 (m + 3) R z hz)
  have hρpos : ∀ j, 0 < ρ j := canonicalEnergyRadius_pos R hR
  have hρR : ∀ j, ρ j ≤ R := canonicalEnergyRadius_le R hR
  have hρanti : Antitone ρ := canonicalEnergyRadius_antitone R hR
  have hρzero : Tendsto ρ atTop (𝓝 0) :=
    canonicalEnergyRadius_tendsto_zero R
  have hmono : Monotone (fun j => Ioc (ρ j) R) := by
    intro i j hij r hr
    exact ⟨lt_of_le_of_lt (hρanti hij) hr.1, hr.2⟩
  have hunion : (⋃ j, Ioc (ρ j) R) = Ioc (0 : ℝ) R := by
    ext r
    constructor
    · intro hr
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hr
      exact ⟨lt_trans (hρpos j) hj.1, hj.2⟩
    · intro hr
      have hlt : Iio r ∈ 𝓝 (0 : ℝ) :=
        isOpen_Iio.mem_nhds hr.1
      obtain ⟨j, hj⟩ := (hρzero.eventually hlt).exists
      exact Set.mem_iUnion.mpr ⟨j, hj, hr.2⟩
  have hInt : IntegrableOn q (Ioc (0 : ℝ) R) volume := by
    simpa only [q] using hBridgeInt.1
  have ht : Tendsto
      (fun j => ∫ r in Ioc (ρ j) R, q r)
      atTop (𝓝 (∫ r in Ioc (0 : ℝ) R, q r)) := by
    have h := tendsto_setIntegral_of_monotone
      (fun j => measurableSet_Ioc) hmono
      (by simpa only [hunion] using hInt)
    simpa only [hunion] using h
  have heq (j : ℕ) :
      (∫ r in ρ j..R, q r) = ∫ r in Ioc (ρ j) R, q r :=
    intervalIntegral.integral_of_le (hρR j)
  have hzero : (∫ r in (0 : ℝ)..R, q r) =
      ∫ r in Ioc (0 : ℝ) R, q r :=
    intervalIntegral.integral_of_le hR.le
  change Tendsto (fun j => ∫ r in ρ j..R, q r) atTop
    (𝓝 (∫ r in (0 : ℝ)..R, q r))
  simpa only [heq, hzero] using ht

/-- Concrete open-ball quadratic bridge nonnegativity from the proved
finite-ball spherical bridge.  The displayed product conditions are the
standard Fubini hypotheses; no sign is assumed for the spatial density. -/
theorem euclideanQuadraticBridge_ball_nonneg_of_finiteFamily
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
    (hBridgeNonneg : 0 ≤ ∫ r in (0 : ℝ)..R,
      vectorSphereBridgeDensity m f F
        (finiteBallSphereFamily (m + 3) R z)
        (fun s k => finiteBallSphereFamily_memLp (m + 3) R z hz s k)
        (finiteBallSphereFamilyRadialL2 (m + 3) R z hz) r) :
    0 ≤ ∫ x,
      euclideanQuadraticBridgeDensity m f F z x
        ∂(volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)) := by
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
  change 0 ≤ ∫ x in Metric.ball (0 : GLEuclidean (m + 3)) R, q x
  rw [← energyPositiveClosedBall_integral_eq_ball m R q, hIntegralEq]
  exact hBridgeNonneg

end

end BrezisOP6
