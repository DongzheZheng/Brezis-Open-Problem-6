import BrezisOP6.EnergyPublishedBallInterface
import BrezisOP6.WeakEnergyStrongConvergence

/-!
# The published compact-perturbation theorem and the zero-trace bridge

`PublishedC1VortexMinimality` is the specialized, external entire-vortex
minimum for perturbations supported strictly inside a ball.  The other
external ingredient below is standard Sobolev trace theory: a `C¹` field
equal to the vortex on the sphere has a zero-extended `H¹ ∩ L⁴`
perturbation, admitting interior-supported approximants.  The bridge records
the actual weak gradient, weak-field certificates for the competitor and
approximants, and convergence in both norms.  Energy convergence is proved
from these data using `weakBallEnergy_tendsto_of_strongH1L4`.  No part of the
published vortex minimum is included in the standard bridge.  The bridge
is intended for the smooth radial vortex supplied by the profile theorem;
it is not asserted for arbitrary functions `V`.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

/-- The concrete conclusion of the standard trace/zero-extension and
interior-density theorem for one `C¹` boundary-matching ball field.  The
certified weak fields carry the exact classical gradients, so energy
continuity follows from strong `L⁴` and gradient `L²` convergence. -/
def C1FixedTraceZeroExtensionApproximation
    (n : ℕ) (R : ℝ)
    (V v : GLEuclidean n → GLEuclidean n) : Prop :=
  HasGlobalWeakGradient n
    (zeroExtendedDifference n R v V)
    (zeroExtendedGradientDifference n R (fderiv ℝ v) (fderiv ℝ V)) ∧
  ∃ target : WeakH1L4BallField n R,
    target.u = v ∧ target.grad = fderiv ℝ target.u ∧
    ∃ tests : ℕ → GLEuclidean n → GLEuclidean n,
      (∀ k, C1InteriorBallPerturbation n R (tests k)) ∧
      ∃ approx : ℕ → WeakH1L4BallField n R,
        (∀ k, (approx k).u = fun x => V x + tests k x) ∧
        (∀ k, (approx k).grad = fderiv ℝ (approx k).u) ∧
        Tendsto
          (fun k => lpNorm ((approx k).u - target.u)
            4 (weakBallMeasure n R)) atTop (𝓝 0) ∧
        (∀ i : Fin n, Tendsto
          (fun k => lpNorm
            (fun x => (approx k).grad x
                (EuclideanSpace.single i (1 : ℝ)) -
              target.grad x (EuclideanSpace.single i (1 : ℝ)))
            2 (weakBallMeasure n R)) atTop (𝓝 0))

/-- An explicit standard trace-theory *input*, kept separate from the
specialized entire-vortex minimum.  This project does not prove this input.
It is meant to be instantiated for the manuscript's smooth radial vortex,
where the sphere trace is classical.  No universal assertion for arbitrary
`V` is made. -/
structure StandardC1FixedTraceZeroExtensionBridge
    (n : ℕ) (V : GLEuclidean n → GLEuclidean n) : Prop where
  approximate : ∀ (_hn : 3 ≤ n) (R : ℝ) (_hR : 0 < R)
    (v : GLEuclidean n → GLEuclidean n),
    ContDiffOn ℝ 1 v (Metric.closedBall (0 : GLEuclidean n) R) →
    (∀ x : GLEuclidean n, ‖x‖ = R → v x = V x) →
      C1FixedTraceZeroExtensionApproximation n R V v

/-- The standard approximation data produce the exact energy-closure
predicate already used by the smooth two-profile bridge. -/
theorem C1FixedTraceZeroExtensionApproximation.ballEnergyClosure
    {n : ℕ} {R : ℝ}
    {V v : GLEuclidean n → GLEuclidean n}
    (h : C1FixedTraceZeroExtensionApproximation n R V v) :
    BallEnergyClosure n R V (fun x => v x - V x) := by
  rcases h with
    ⟨_, target, hTargetU, hTargetGrad, tests, hInterior,
      approx, hApproxU, hApproxGrad, hValue, hGradient⟩
  have hEnergy := weakBallEnergy_tendsto_of_strongH1L4
    approx target hValue hGradient
  have hApproxEnergy (k : ℕ) :
      (approx k).energy =
        euclideanBallEnergy n R (fun x => V x + tests k x) := by
    rw [WeakH1L4BallField.energy, hApproxGrad k,
      weakBallEnergy_classical_gradient, hApproxU k]
  have hTargetEnergy : target.energy = euclideanBallEnergy n R v := by
    rw [WeakH1L4BallField.energy, hTargetGrad,
      weakBallEnergy_classical_gradient, hTargetU]
  refine ⟨tests, hInterior, ?_⟩
  have hEq : (fun x => V x + (v x - V x)) = v := by
    funext x
    abel
  simpa only [hEq, hApproxEnergy, hTargetEnergy] using hEnergy

/-- Split the old same-boundary ball input into the published entire-vortex
minimum for interior tests and the standard zero-trace approximation theorem.
The passage through the already-proved energy closure is explicit. -/
theorem publishedC1_and_standardTrace_to_ballMinimality
    (n : ℕ) (V : GLEuclidean n → GLEuclidean n)
    (hPublished : PublishedC1VortexMinimality n V)
    (hTrace : StandardC1FixedTraceZeroExtensionBridge n V) :
    PublishedBallMinimalityForZeroBoundaryC1 n V := by
  refine ⟨?_⟩
  intro hn R hR v hvC1 hvTrace
  have hClosure : BallEnergyClosure n R V (fun x => v x - V x) :=
    (hTrace.approximate hn R hR v hvC1 hvTrace).ballEnergyClosure
  have hMinimum := publishedC1_minimality_of_energyClosure n V
    (fun x => v x - V x) R hPublished hn hR hClosure
  have hEq : (fun x => V x + (v x - V x)) = v := by
    funext x
    abel
  simpa only [hEq] using hMinimum

end

end BrezisOP6
