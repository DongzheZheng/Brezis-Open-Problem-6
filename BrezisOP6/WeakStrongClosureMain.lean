import BrezisOP6.WeakBallClosureMain
import BrezisOP6.WeakEnergyStrongConvergence

/-!
# From strong fixed-trace approximation to weak energy closure

The only approximation hypothesis in this module is the existence of
fixed-trace smooth fields converging in the actual `H¹∩L⁴` norms.  Energy
convergence is now a proved consequence of polynomial continuity on the
finite ball, rather than an independent assumption.
-/

namespace BrezisOP6

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The paper's fixed-trace density statement, expressed as a concrete
strong `H¹∩L⁴` sequence in the weak-gradient certificate model.  Its
existence is an external Sobolev density obligation. -/
def WeakSmoothFixedTraceStrongClosure (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (U : WeakH1L4BallField (m + 3) R) : Prop :=
  ∃ V : ℕ → WeakH1L4BallField (m + 3) R,
    (∀ j, SmoothBallCompetitor m R f (V j).u ∧
      (V j).grad = fderiv ℝ (V j).u) ∧
    Tendsto (fun j => lpNorm ((V j).u - U.u) 4
      (weakBallMeasure (m + 3) R)) atTop (𝓝 0) ∧
    ∀ i : Fin (m + 3), Tendsto
      (fun j => lpNorm
        (fun x => (V j).grad x (EuclideanSpace.single i (1 : ℝ)) -
          U.grad x (EuclideanSpace.single i (1 : ℝ)))
        2 (weakBallMeasure (m + 3) R)) atTop (𝓝 0)

/-- Strong `H¹∩L⁴` approximation implies the energy-convergent closure
previously used by the conditional weak comparison. -/
theorem WeakSmoothFixedTraceStrongClosure.toEnergyClosure
    {m : ℕ} {R : ℝ} {f : ℝ → ℝ}
    {U : WeakH1L4BallField (m + 3) R}
    (h : WeakSmoothFixedTraceStrongClosure m R f U) :
    WeakSmoothFixedTraceClosure m R f U := by
  obtain ⟨V, hSmooth, hu4, hgrad⟩ := h
  exact ⟨V, hSmooth,
    weakBallEnergy_tendsto_of_strongH1L4 V U hu4 hgrad⟩

/-- Fixed-trace weak minimum and a.e. equality from strong
`H¹∩L⁴` approximation, with the remaining equality-case regularity
assumption visible in the statement. -/
theorem physical_weak_ball_minimum_of_strong_closure
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (base : WeakH1L4BallField (m + 3) R)
    (hBaseEnergy : base.energy =
      euclideanBallEnergy (m + 3) R
        (radialVortex (m + 3) p.f))
    (hBaseU : base.u =ᵐ[weakBallMeasure (m + 3) R]
      radialVortex (m + 3) p.f)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor base)
    (hClosure : WeakSmoothFixedTraceStrongClosure m R p.f U.field)
    (hRegularity : WeakEqualitySmoothRepresentative m R p.f
      base U.field) :
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) :=
  physical_weak_ball_minimum_and_ae_equality_of_base_energy
    m R p base hBaseEnergy hBaseU hPublished hLocal U
      hClosure.toEnergyClosure hRegularity

end

end BrezisOP6
