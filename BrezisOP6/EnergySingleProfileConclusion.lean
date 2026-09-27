import BrezisOP6.EnergyWholeBallIdentity

/-!
# Reading the punctured-ball identity as the manuscript's energy identity

These lemmas identify the left-hand side of the proved spatial identity
with the usual difference of Euclidean GL energies and show that unit
boundary trace eliminates the outer flux.  They add no new PDE hypothesis.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The generic energy interface is exactly the integral of the concrete
Fréchet-gradient GL density in the Euclidean application. -/
theorem glEnergy_euclidean_eq_density (n : ℕ)
    (s : Set (GLEuclidean n))
    (u : GLEuclidean n → GLEuclidean n) :
    glEnergy (volume.restrict s) (euclideanGradientSq n) u =
      ∫ x in s, euclideanGLDensity n u x := rfl

/-- Under individual integrability, the proved spatial gap density is the
difference of the two actual GL energies minus the reduced integral. -/
theorem energySpatialGapDensity_integral_split (m : ℕ)
    (R : ℝ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (huInt : IntegrableOn
      (euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hvInt : IntegrableOn
      (euclideanGLDensity (m + 3) (radialVortex (m + 3) p))
      (energyPositiveClosedBall (m + 3) R) volume)
    (hredInt : IntegrableOn (energyReducedSpatialDensity m p z)
      (energyPositiveClosedBall (m + 3) R) volume) :
    (∫ x in energyPositiveClosedBall (m + 3) R,
      energySpatialGapDensity m p z x) =
      2 * ((∫ x in energyPositiveClosedBall (m + 3) R,
          euclideanGLDensity (m + 3)
            (fun y => p ‖y‖ • z y) x) -
        (∫ x in energyPositiveClosedBall (m + 3) R,
          euclideanGLDensity (m + 3)
            (radialVortex (m + 3) p) x) -
        (∫ x in energyPositiveClosedBall (m + 3) R,
          singleProfileDensity (m + 3)
            (fun y : GLEuclidean (m + 3) => p ‖y‖)
            (euclideanGradientSq (m + 3) z)
            (fun y => ‖z y‖ ^ 2)
            (fun y => ‖y‖⁻¹ ^ 2) x)) := by
  have hred := energyReducedSpatialDensity_integral_eq_singleProfileDensity
    m R p z
  unfold energySpatialGapDensity
  rw [integral_const_mul]
  calc
    2 * (∫ x in energyPositiveClosedBall (m + 3) R,
      euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
        euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x -
        energyReducedSpatialDensity m p z x) =
        2 * ((∫ x in energyPositiveClosedBall (m + 3) R,
          euclideanGLDensity (m + 3) (fun y => p ‖y‖ • z y) x -
            euclideanGLDensity (m + 3) (radialVortex (m + 3) p) x) -
          ∫ x in energyPositiveClosedBall (m + 3) R,
            energyReducedSpatialDensity m p z x) := by
      exact congrArg (2 * ·) (integral_sub (huInt.sub hvInt) hredInt)
    _ = _ := by rw [integral_sub huInt hvInt, hred]

/-- Unit norm of the quotient field on the outer sphere makes the remaining
boundary flux vanish identically, hence also after sphere integration. -/
theorem energyOuterFlux_integral_zero (m : ℕ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (R : ℝ)
    (hunit : ∀ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      ‖z (energySphereRay (m + 3) ω R)‖ ^ 2 = 1) :
    (∫ ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1,
      radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R
      ∂(unitSphereMeasure (m + 3))) = 0 := by
  have hzero : (fun ω : Metric.sphere (0 : GLEuclidean (m + 3)) 1 =>
      radialBoundaryFlux m p (energyRaySq (m + 3) z ω) R) =
      fun _ => 0 := by
    funext ω
    simp [radialBoundaryFlux, energyRaySq, hunit ω]
  rw [hzero]
  simp

end

end BrezisOP6
