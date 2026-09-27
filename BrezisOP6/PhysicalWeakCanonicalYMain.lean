import BrezisOP6.PhysicalProfileYExtension
import BrezisOP6.PhysicalWeakEpsilonMain
import BrezisOP6.PublishedC1TraceBridge

/-!
# The weak OP6 endpoints with a constructed profile-flow variable

These public statements take `PhysicalRadialDataCore`, which contains the
cited radial profiles and their regular-origin factorization but no
independent `y`, `hyDiff`, or `hyMatch` fields.  The profile slope defect is
constructed by `PhysicalRadialDataCore.toPhysicalRadialData`; all contact,
Picone, bridge, annular-stability, weak-closure, and scale-transfer steps
are the previously proved theorems.  The published entire-vortex minimum
and the standard zero-trace/extension bridge appear as separate inputs.
-/

namespace BrezisOP6

open MeasureTheory Metric

noncomputable section

/-- Finite-ball minimum and weak equality from the paper's profile inputs,
the published compact-perturbation minimum, and standard trace theory.
The auxiliary slope-defect function is constructed internally. -/
theorem physical_weak_ball_minimum_and_ae_equality_from_core
    (m : ℕ) (R : ℝ) (p : PhysicalRadialDataCore m R)
    (hPublished : PublishedC1VortexMinimality (m + 3)
      (radialVortex (m + 3) p.F))
    (hTrace : StandardC1FixedTraceZeroExtensionBridge (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor
      (WeakH1L4BallField.ofGlobalC1 (m + 3) R
        (radialRegularField (m + 3) p.Hf)
        (radialRegularField_contDiff_one (m + 3) p.Hf
          (p.hHf.of_le (by norm_num))))) :
    let base := WeakH1L4BallField.ofGlobalC1 (m + 3) R
      (radialRegularField (m + 3) p.Hf)
      (radialRegularField_contDiff_one (m + 3) p.Hf
        (p.hHf.of_le (by norm_num)))
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  exact physical_weak_ball_minimum_and_ae_equality
    m R p.toPhysicalRadialData
      (publishedC1_and_standardTrace_to_ballMinimality
        (m + 3) (radialVortex (m + 3) p.F) hPublished hTrace)
      hLocal U

/-- The unit-ball theorem at every positive coherence length.  The
published compact-perturbation theorem and the standard trace bridge
remain separate; no auxiliary `y` is supplied. -/
theorem physical_weak_unit_epsilon_minimum_and_ae_equality_from_core
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialDataCore m (1 / ε))
    (hPublished : PublishedC1VortexMinimality (m + 3)
      (radialVortex (m + 3) p.F))
    (hTrace : StandardC1FixedTraceZeroExtensionBridge (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor
      (physicalWeakUnitBase m ε p.toPhysicalRadialData)) :
    weakBallEnergyEpsilon (m + 3) 1 ε
        (physicalWeakUnitBase m ε p.toPhysicalRadialData).u
        (physicalWeakUnitBase m ε p.toPhysicalRadialData).grad ≤
      weakBallEnergyEpsilon (m + 3) 1 ε U.field.u U.field.grad ∧
    (weakBallEnergyEpsilon (m + 3) 1 ε U.field.u U.field.grad =
      weakBallEnergyEpsilon (m + 3) 1 ε
        (physicalWeakUnitBase m ε p.toPhysicalRadialData).u
        (physicalWeakUnitBase m ε p.toPhysicalRadialData).grad →
      U.field.u =ᵐ[weakBallMeasure (m + 3) 1]
        (physicalWeakUnitBase m ε p.toPhysicalRadialData).u) := by
  exact physical_weak_unit_epsilon_minimum_and_ae_equality
    m ε hε p.toPhysicalRadialData
      (publishedC1_and_standardTrace_to_ballMinimality
        (m + 3) (radialVortex (m + 3) p.F) hPublished hTrace)
      hLocal U

/-- The base field in the preceding unit-ball theorem is the manuscript's
rescaled radial vortex almost everywhere, including the centre convention. -/
theorem physical_weak_unit_base_from_core_ae_eq_vortex
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p : PhysicalRadialDataCore m (1 / ε)) :
    (physicalWeakUnitBase m ε p.toPhysicalRadialData).u
      =ᵐ[weakBallMeasure (m + 3) 1]
        radialVortex (m + 3) (fun r => p.f (r / ε)) := by
  exact physicalWeakUnitBase_ae_eq_vortex
    m ε hε p.toPhysicalRadialData

end

end BrezisOP6
