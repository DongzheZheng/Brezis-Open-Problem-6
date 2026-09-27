import BrezisOP6.WeakBallEnergy
import BrezisOP6.ActualSobolevClosureMain

/-!
# Conditional passage from the smooth comparison to the weak Sobolev energy

The competitor in the paper belongs to `H¹(B_R; ℝⁿ) ∩ L⁴(B_R; ℝⁿ)` and
has the fixed radial-vortex trace.  Here that class is represented by a
distributional-gradient certificate and the zero-extension characterization
of the fixed trace (`WeakFixedTraceCompetitor`).  Its energy is computed from
the certified weak gradient, never from a totalized pointwise `fderiv`.

The smooth-to-weak theorem below separates the unformalized analytic inputs:
trace-preserving `H¹∩L⁴` approximation, the resulting energy convergence,
and regularity of an equality-case minimizer.  It does not infer any of them
from the existence of a weak-gradient certificate.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

/-- A precise energy-convergent smooth approximation of a weak field with
the manuscript's prescribed radial boundary values.  Each approximant is
itself a certified weak field, and its certified gradient is the classical
Fréchet derivative.  Existence of this sequence is the density obligation,
not a definition of weak `H¹`. -/
def WeakSmoothFixedTraceClosure (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (U : WeakH1L4BallField (m + 3) R) : Prop :=
  ∃ V : ℕ → WeakH1L4BallField (m + 3) R,
    (∀ j, SmoothBallCompetitor m R f (V j).u ∧
      (V j).grad = fderiv ℝ (V j).u) ∧
    Tendsto (fun j => (V j).energy) atTop (𝓝 U.energy)

/-- Equality-case regularization for the weak-energy formulation.  The
representative has the same weak energy, the fixed boundary values, and
the classical derivative as its certified gradient.  Proving this from
the Euler--Lagrange equation and elliptic regularity remains an analytic
obligation. -/
def WeakEqualitySmoothRepresentative (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (base U : WeakH1L4BallField (m + 3) R) : Prop :=
  U.energy = base.energy →
    ∃ V : WeakH1L4BallField (m + 3) R,
      SmoothBallCompetitor m R f V.u ∧
      V.grad = fderiv ℝ V.u ∧
      V.energy = U.energy ∧
      U.u =ᵐ[weakBallMeasure (m + 3) R] V.u

/-- The paper's fixed-trace finite-ball minimum and equality statement for
an `H¹∩L⁴` competitor, conditional exactly on the external radial/spherical
inputs and the still-unproved Sobolev density/regularity steps.  In
particular, the energy on this conclusion is the weak-gradient energy. -/
theorem physical_weak_ball_minimum_and_ae_equality_of_closure
    (m : ℕ) (R : ℝ) (p : PhysicalRadialData m R)
    (base : WeakH1L4BallField (m + 3) R)
    (hBaseU : base.u = radialVortex (m + 3) p.f)
    (hBaseGrad : base.grad = fderiv ℝ base.u)
    (hPublished : PublishedBallMinimalityForZeroBoundaryC1 (m + 3)
      (radialVortex (m + 3) p.F))
    (hLocal : SharpUnitSpherePoincareLocal (m + 3))
    (U : WeakFixedTraceCompetitor base)
    (hClosure : WeakSmoothFixedTraceClosure m R p.f U.field)
    (hRegularity : WeakEqualitySmoothRepresentative m R p.f
      base U.field) :
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  have hBaseEnergy : base.energy =
      euclideanBallEnergy (m + 3) R
        (radialVortex (m + 3) p.f) := by
    rw [WeakH1L4BallField.energy, hBaseGrad,
      weakBallEnergy_classical_gradient, hBaseU]
  obtain ⟨V, hSmooth, hLimit⟩ := hClosure
  constructor
  · apply ge_of_tendsto hLimit
    exact Eventually.of_forall (fun j => by
      have hV : (V j).energy =
          euclideanBallEnergy (m + 3) R (V j).u := by
        rw [WeakH1L4BallField.energy, (hSmooth j).2,
          weakBallEnergy_classical_gradient]
      rw [hBaseEnergy, hV]
      exact (physical_smooth_ball_minimum_and_ae_equality
        m R p hPublished hLocal (V j).u (hSmooth j).1).1)
  · intro hEq
    obtain ⟨V₀, hV₀Smooth, hV₀Grad, hV₀Energy, hUV₀⟩ :=
      hRegularity hEq
    have hV₀Classical : V₀.energy =
        euclideanBallEnergy (m + 3) R V₀.u := by
      rw [WeakH1L4BallField.energy, hV₀Grad,
        weakBallEnergy_classical_gradient]
    have hV₀Eq : euclideanBallEnergy (m + 3) R V₀.u =
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f) := by
      calc
        _ = V₀.energy := hV₀Classical.symm
        _ = U.field.energy := hV₀Energy
        _ = base.energy := hEq
        _ = _ := hBaseEnergy
    have hVortex :=
      (physical_smooth_ball_minimum_and_ae_equality
        m R p hPublished hLocal V₀.u hV₀Smooth).2 hV₀Eq
    simpa only [weakBallMeasure, ← hBaseU] using hUV₀.trans hVortex

/-- The same conditional weak theorem with exactly the base-field facts
needed by the proof: its energy and its almost-everywhere value on the
ball.  This form permits the physical radial vortex to be represented by
the globally smooth map `H(‖x‖²)x` without extending the profile beyond
the finite ball. -/
theorem physical_weak_ball_minimum_and_ae_equality_of_base_energy
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
    (hClosure : WeakSmoothFixedTraceClosure m R p.f U.field)
    (hRegularity : WeakEqualitySmoothRepresentative m R p.f
      base U.field) :
    base.energy ≤ U.field.energy ∧
      (U.field.energy = base.energy →
        U.field.u =ᵐ[weakBallMeasure (m + 3) R] base.u) := by
  obtain ⟨V, hSmooth, hLimit⟩ := hClosure
  constructor
  · apply ge_of_tendsto hLimit
    exact Eventually.of_forall (fun j => by
      have hV : (V j).energy =
          euclideanBallEnergy (m + 3) R (V j).u := by
        rw [WeakH1L4BallField.energy, (hSmooth j).2,
          weakBallEnergy_classical_gradient]
      rw [hBaseEnergy, hV]
      exact (physical_smooth_ball_minimum_and_ae_equality
        m R p hPublished hLocal (V j).u (hSmooth j).1).1)
  · intro hEq
    obtain ⟨V₀, hV₀Smooth, hV₀Grad, hV₀Energy, hUV₀⟩ :=
      hRegularity hEq
    have hV₀Classical : V₀.energy =
        euclideanBallEnergy (m + 3) R V₀.u := by
      rw [WeakH1L4BallField.energy, hV₀Grad,
        weakBallEnergy_classical_gradient]
    have hV₀Eq : euclideanBallEnergy (m + 3) R V₀.u =
        euclideanBallEnergy (m + 3) R
          (radialVortex (m + 3) p.f) := by
      calc
        _ = V₀.energy := hV₀Classical.symm
        _ = U.field.energy := hV₀Energy
        _ = base.energy := hEq
        _ = _ := hBaseEnergy
    have hVortex :=
      (physical_smooth_ball_minimum_and_ae_equality
        m R p hPublished hLocal V₀.u hV₀Smooth).2 hV₀Eq
    have hUVortex : U.field.u =ᵐ[weakBallMeasure (m + 3) R]
        radialVortex (m + 3) p.f := by
      simpa only [weakBallMeasure] using hUV₀.trans hVortex
    exact hUVortex.trans hBaseU.symm

end

end BrezisOP6
