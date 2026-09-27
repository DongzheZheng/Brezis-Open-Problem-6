import BrezisOP6.EnergyIBP

/-!
# Weak-gradient energy on a ball

The pointwise Fréchet derivative in `euclideanBallEnergy` is appropriate for
smooth fields.  For an arbitrary Sobolev representative it need not be the
weak derivative.  This module therefore keeps the weak derivative as data
and defines it by the distributional integration-by-parts identity.  Both
`L²` requirements and the `L⁴` requirement are imposed on the actual ball
measure; energy is computed from the certified weak derivative.

This construction does not assert that the weak derivative is unique almost
everywhere, that a given rough map has one, or that a weak zero trace admits
smooth trace-preserving approximation.  Those analytic results need their
own proofs before a fully unconditional Sobolev theorem can be stated.
-/

namespace BrezisOP6

open MeasureTheory Metric Set
open scoped Topology

noncomputable section

/-- Lebesgue measure restricted to the open ball. -/
def weakBallMeasure (n : ℕ) (R : ℝ) : Measure (GLEuclidean n) :=
  volume.restrict (Metric.ball (0 : GLEuclidean n) R)

/-- A scalar `C¹` test supported strictly inside the ball. -/
def C1ScalarInteriorTest (n : ℕ) (R : ℝ)
    (φ : GLEuclidean n → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < R ∧
      ∀ x : GLEuclidean n, ρ ≤ ‖x‖ → φ x = 0

/-- A scalar `C¹` test with compact support in the whole Euclidean space. -/
def C1ScalarCompactTest (n : ℕ)
    (φ : GLEuclidean n → ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧
    ∃ ρ : ℝ, 0 ≤ ρ ∧
      ∀ x : GLEuclidean n, ρ ≤ ‖x‖ → φ x = 0

/-- The squared Hilbert--Schmidt norm of a candidate weak gradient. -/
def weakGradientSq (n : ℕ)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) : ℝ :=
  ∑ i : Fin n, ‖G x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2

/-- `G` is the distributional gradient of `u` on the ball.  The test
integrability clauses make the Bochner integrals in the identity genuine
integrals rather than values assigned to nonintegrable functions. -/
def HasWeakGradientOnBall (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) : Prop :=
  ∀ (φ : GLEuclidean n → ℝ), C1ScalarInteriorTest n R φ →
    ∀ i : Fin n,
      Integrable (fun x =>
        (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x)
        (weakBallMeasure n R) ∧
      Integrable (fun x =>
        φ x • G x (EuclideanSpace.single i (1 : ℝ)))
        (weakBallMeasure n R) ∧
      (∫ x, (fderiv ℝ φ x)
          (EuclideanSpace.single i (1 : ℝ)) • u x
          ∂(weakBallMeasure n R)) =
        -(∫ x, φ x • G x
          (EuclideanSpace.single i (1 : ℝ))
          ∂(weakBallMeasure n R))

/-- A representative of `H¹(B_R;ℝⁿ) ∩ L⁴(B_R;ℝⁿ)` together with its
distributional gradient.  The square-integrability fields state precisely
the `H¹` requirements, while `uL4` states the extra `L⁴` requirement. -/
structure WeakH1L4BallField (n : ℕ) (R : ℝ) where
  u : GLEuclidean n → GLEuclidean n
  grad : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n
  uMeas : AEStronglyMeasurable u (weakBallMeasure n R)
  gradMeas : AEStronglyMeasurable grad (weakBallMeasure n R)
  uL2 : Integrable (fun x => ‖u x‖ ^ 2) (weakBallMeasure n R)
  uL4 : Integrable (fun x => ‖u x‖ ^ 4) (weakBallMeasure n R)
  gradL2 : Integrable (weakGradientSq n grad) (weakBallMeasure n R)
  weakDerivative : HasWeakGradientOnBall n R u grad

/-- Energy of a specified weak-gradient representative. -/
def weakBallEnergy (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) : ℝ :=
  ∫ x, weakGradientSq n G x / 2 + (1 - ‖u x‖ ^ 2) ^ 2 / 4
    ∂(weakBallMeasure n R)

/-- The energy of a certified `H¹∩L⁴` field uses its weak gradient. -/
def WeakH1L4BallField.energy {n : ℕ} {R : ℝ}
    (U : WeakH1L4BallField n R) : ℝ :=
  weakBallEnergy n R U.u U.grad

/-- The density integrated in `weakBallEnergy` is genuinely integrable for
every certified field.  In particular, the integral cannot silently use
Lean's totalized value for a nonintegrable density. -/
theorem WeakH1L4BallField.energyDensity_integrable
    {n : ℕ} {R : ℝ} (U : WeakH1L4BallField n R) :
    Integrable (fun x =>
      weakGradientSq n U.grad x / 2 +
        (1 - ‖U.u x‖ ^ 2) ^ 2 / 4)
      (weakBallMeasure n R) := by
  have hone : Integrable (fun _ : GLEuclidean n => (1 : ℝ))
      (weakBallMeasure n R) := by
    change IntegrableOn (fun _ : GLEuclidean n => (1 : ℝ))
      (Metric.ball (0 : GLEuclidean n) R) volume
    exact integrableOn_const (measure_ball_ne_top)
  have hpoly : Integrable (fun x : GLEuclidean n =>
      1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4)
      (weakBallMeasure n R) :=
    (hone.sub (U.uL2.const_mul 2)).add U.uL4
  have hsource : Integrable (fun x : GLEuclidean n =>
      weakGradientSq n U.grad x / 2 +
        (1 - 2 * ‖U.u x‖ ^ 2 + ‖U.u x‖ ^ 4) / 4)
      (weakBallMeasure n R) :=
    (U.gradL2.div_const 2).add (hpoly.div_const 4)
  exact hsource.congr (Filter.Eventually.of_forall (fun x => by
    dsimp
    ring))

/-- For the classical gradient, the weak-energy formula reduces exactly to
the smooth energy used in the geometric comparison.  This formula is an
identity of integrands and does not claim that every `C¹` field has already
been proved to satisfy the distributional integration-by-parts condition. -/
theorem weakBallEnergy_classical_gradient (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n) :
    weakBallEnergy n R u (fderiv ℝ u) =
      euclideanBallEnergy n R u := by
  rfl

/-- A smooth field with a certified classical integration-by-parts
identity becomes a weak-gradient field once its actual `L²`/`L⁴` bounds
are supplied.  The multidimensional integration-by-parts and integrability
facts are explicit inputs here. -/
def WeakH1L4BallField.ofClassical
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (huMeas : AEStronglyMeasurable u (weakBallMeasure n R))
    (hgradMeas : AEStronglyMeasurable (fderiv ℝ u)
      (weakBallMeasure n R))
    (huL2 : Integrable (fun x => ‖u x‖ ^ 2) (weakBallMeasure n R))
    (huL4 : Integrable (fun x => ‖u x‖ ^ 4) (weakBallMeasure n R))
    (hgradL2 : Integrable (euclideanGradientSq n u)
      (weakBallMeasure n R))
    (hIBP : HasWeakGradientOnBall n R u (fderiv ℝ u)) :
    WeakH1L4BallField n R :=
  ⟨u, fderiv ℝ u, huMeas, hgradMeas,
    huL2, huL4, hgradL2, hIBP⟩

/-- Certified smooth fields have exactly their classical energy. -/
theorem WeakH1L4BallField.ofClassical_energy
    (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n)
    (huMeas : AEStronglyMeasurable u (weakBallMeasure n R))
    (hgradMeas : AEStronglyMeasurable (fderiv ℝ u)
      (weakBallMeasure n R))
    (huL2 : Integrable (fun x => ‖u x‖ ^ 2) (weakBallMeasure n R))
    (huL4 : Integrable (fun x => ‖u x‖ ^ 4) (weakBallMeasure n R))
    (hgradL2 : Integrable (euclideanGradientSq n u)
      (weakBallMeasure n R))
    (hIBP : HasWeakGradientOnBall n R u (fderiv ℝ u)) :
    (WeakH1L4BallField.ofClassical n R u huMeas hgradMeas
      huL2 huL4 hgradL2 hIBP).energy =
      euclideanBallEnergy n R u := by
  exact weakBallEnergy_classical_gradient n R u

/-- Extension by zero of the difference from a fixed boundary field. -/
def zeroExtendedDifference (n : ℕ) (R : ℝ)
    (u v : GLEuclidean n → GLEuclidean n)
    (x : GLEuclidean n) : GLEuclidean n := by
  classical
  exact if x ∈ Metric.ball (0 : GLEuclidean n) R then u x - v x else 0

/-- Extension by zero of the difference of the certified gradients. -/
def zeroExtendedGradientDifference (n : ℕ) (R : ℝ)
    (G H : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n)
    (x : GLEuclidean n) : GLEuclidean n →L[ℝ] GLEuclidean n := by
  classical
  exact if x ∈ Metric.ball (0 : GLEuclidean n) R then G x - H x else 0

/-- Distributional gradient on all of Euclidean space, used to define a
weak zero trace without disguising a density statement as a definition of
`H¹`.  For a Lipschitz ball this expresses the usual zero-extension
characterization of zero trace. -/
def HasGlobalWeakGradient (n : ℕ)
    (u : GLEuclidean n → GLEuclidean n)
    (G : GLEuclidean n → GLEuclidean n →L[ℝ] GLEuclidean n) : Prop :=
  AEStronglyMeasurable u volume ∧
    AEStronglyMeasurable G volume ∧
    Integrable (fun x => ‖u x‖ ^ 2) volume ∧
    Integrable (fun x => ‖u x‖ ^ 4) volume ∧
    Integrable (weakGradientSq n G) volume ∧
    ∀ (φ : GLEuclidean n → ℝ), C1ScalarCompactTest n φ →
      ∀ i : Fin n,
        Integrable (fun x =>
          (fderiv ℝ φ x) (EuclideanSpace.single i (1 : ℝ)) • u x)
          volume ∧
        Integrable (fun x =>
          φ x • G x (EuclideanSpace.single i (1 : ℝ)))
          volume ∧
        (∫ x, (fderiv ℝ φ x)
            (EuclideanSpace.single i (1 : ℝ)) • u x) =
          -(∫ x, φ x • G x
            (EuclideanSpace.single i (1 : ℝ)))

/-- A fixed-trace Sobolev competitor.  The zero extension of its difference
from the prescribed boundary field has the zero-extended difference of weak
gradients as its global distributional gradient.  On a ball this is the
standard weak zero-trace condition; no smooth approximation is built into
the definition. -/
structure WeakFixedTraceCompetitor {n : ℕ} {R : ℝ}
    (base : WeakH1L4BallField n R) where
  field : WeakH1L4BallField n R
  zeroTrace : HasGlobalWeakGradient n
    (zeroExtendedDifference n R field.u base.u)
    (zeroExtendedGradientDifference n R field.grad base.grad)

end

end BrezisOP6
