import BrezisOP6.BallPuncturedEqualityAE

/-!
# An abstract limit passage for the pointwise-derivative energy

This module checks a limit-and-uniqueness argument for the energy defined
using the totalized pointwise `fderiv`.  The `SmoothBallEnergyClosure`
predicate *assumes* convergence of that energy.  It does not assert
`H¹ ∩ L⁴` membership, weak-gradient convergence, or preservation of a
Sobolev trace.  In particular, this module is not the `H¹` closure step in
the manuscript; that step needs a weak-gradient energy and the appropriate
trace-preserving density theorem.
-/

namespace BrezisOP6

open Filter MeasureTheory Metric
open scoped Topology

noncomputable section

def SmoothBallCompetitor (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3)) : Prop :=
  ContDiff ℝ 1 u ∧
    ∀ x : GLEuclidean (m + 3), ‖x‖ = R →
      u x = radialVortex (m + 3) f x

/-- An explicit hypothesis that smooth fixed-boundary fields approximate
the *pointwise-derivative* energy value of `u`.  This is not implied merely
by `u ∈ H¹ ∩ L⁴`, because `euclideanBallEnergy` uses totalized `fderiv` at
every point instead of a weak gradient. -/
def SmoothBallEnergyClosure (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3)) : Prop :=
  ∃ uSeq : ℕ → GLEuclidean (m + 3) → GLEuclidean (m + 3),
    (∀ j, SmoothBallCompetitor m R f (uSeq j)) ∧
      Tendsto (fun j => euclideanBallEnergy (m + 3) R (uSeq j))
        atTop (𝓝 (euclideanBallEnergy (m + 3) R u))

/-- A separate equality-case representative hypothesis for the
pointwise-derivative energy.  Sobolev elliptic regularity is not proved here. -/
def EqualityCaseSmoothRepresentative (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3)) : Prop :=
  euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
    ∃ v : GLEuclidean (m + 3) → GLEuclidean (m + 3),
      SmoothBallCompetitor m R f v ∧
        euclideanBallEnergy (m + 3) R v =
          euclideanBallEnergy (m + 3) R u ∧
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)] v

theorem ball_minimum_and_ae_uniqueness_of_smooth_closure
    (m : ℕ) (R : ℝ) (f : ℝ → ℝ)
    (u : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (hSmoothMinimum : ∀ v : GLEuclidean (m + 3) → GLEuclidean (m + 3),
      SmoothBallCompetitor m R f v →
        euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
          euclideanBallEnergy (m + 3) R v)
    (hSmoothEquality : ∀ v : GLEuclidean (m + 3) → GLEuclidean (m + 3),
      SmoothBallCompetitor m R f v →
      euclideanBallEnergy (m + 3) R v =
          euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
        v =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) f)
    (hClosure : SmoothBallEnergyClosure m R f u)
    (hRegularity : EqualityCaseSmoothRepresentative m R f u) :
    euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) ≤
      euclideanBallEnergy (m + 3) R u ∧
    (euclideanBallEnergy (m + 3) R u =
      euclideanBallEnergy (m + 3) R (radialVortex (m + 3) f) →
        u =ᵐ[volume.restrict (Metric.ball
          (0 : GLEuclidean (m + 3)) R)]
          radialVortex (m + 3) f) := by
  obtain ⟨uSeq, hSeqSmooth, hEnergyLim⟩ := hClosure
  constructor
  · apply ge_of_tendsto hEnergyLim
    exact Eventually.of_forall
      (fun j => hSmoothMinimum (uSeq j) (hSeqSmooth j))
  intro heq
  obtain ⟨v, hvSmooth, hvEnergy, huv⟩ := hRegularity heq
  exact huv.trans (hSmoothEquality v hvSmooth (hvEnergy.trans heq))

end

end BrezisOP6
