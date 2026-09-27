import BrezisOP6.EnergySpatialInterface
import Mathlib

/-!
# A concrete class for the published vortex-minimality input

The whole-space minimizer is an external analytic theorem.  This file states
its input on smooth perturbations supported strictly inside an actual
Euclidean ball, then proves that the inequality passes to limits of their
actual Ginzburg--Landau energies.  The latter closure is precisely the
approximation property needed when a transformed finite-ball competitor has
zero boundary trace but is not itself supported away from the boundary.

Membership of a transformed competitor in the closure remains a separate
Sobolev approximation obligation; it is not hidden in an arbitrary
`admissible` predicate.  No result for dimension two is used here.
-/

namespace BrezisOP6

open scoped Topology

noncomputable section

/-- A continuously differentiable perturbation whose support lies inside
some smaller concentric ball.  This is a concrete compact-support test class
for the published entire-vortex local-minimality theorem. -/
def C1InteriorBallPerturbation (n : ℕ) (R : ℝ)
    (w : GLEuclidean n → GLEuclidean n) : Prop :=
  ContDiff ℝ 1 w ∧
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < R ∧
      ∀ x : GLEuclidean n, ρ ≤ ‖x‖ → w x = 0

/-- An interior-supported test vanishes on and outside the prescribed
boundary sphere. -/
theorem C1InteriorBallPerturbation.zero_of_radius_le (n : ℕ)
    {R : ℝ} {w : GLEuclidean n → GLEuclidean n}
    (hw : C1InteriorBallPerturbation n R w)
    (x : GLEuclidean n) (hx : R ≤ ‖x‖) : w x = 0 := by
  obtain ⟨ρ, _, hρR, hzero⟩ := hw.2
  exact hzero x (le_trans (le_of_lt hρR) hx)

/-- The exact energy closure of compactly supported `C¹` tests.  This
formulation records the approximation required to extend the published
smooth-test inequality to a zero-trace finite-ball perturbation. -/
def BallEnergyClosure (n : ℕ) (R : ℝ)
    (V w : GLEuclidean n → GLEuclidean n) : Prop :=
  ∃ tests : ℕ → GLEuclidean n → GLEuclidean n,
    (∀ k, C1InteriorBallPerturbation n R (tests k)) ∧
      Filter.Tendsto
        (fun k => euclideanBallEnergy n R (fun x => V x + tests k x))
        Filter.atTop
        (𝓝 (euclideanBallEnergy n R (fun x => V x + w x)))

/-- The published entire-vortex local-minimality inequality, restricted to
the concrete compactly supported `C¹` test class and dimensions `n ≥ 3`.
This is an input structure, not a proof of the external theorem. -/
structure PublishedC1VortexMinimality (n : ℕ)
    (V : GLEuclidean n → GLEuclidean n) : Prop where
  energy_le : ∀ (_hn : 3 ≤ n) (R : ℝ) (_hR : 0 < R)
    (w : GLEuclidean n → GLEuclidean n),
    C1InteriorBallPerturbation n R w →
      euclideanBallEnergy n R V ≤
        euclideanBallEnergy n R (fun x => V x + w x)

/-- Every compactly supported test is in its own energy closure. -/
theorem c1Interior_mem_ballEnergyClosure (n : ℕ) (R : ℝ)
    (V w : GLEuclidean n → GLEuclidean n)
    (hw : C1InteriorBallPerturbation n R w) :
    BallEnergyClosure n R V w := by
  refine ⟨fun _ => w, fun _ => hw, ?_⟩
  exact tendsto_const_nhds

/-- A published inequality for smooth compactly supported tests extends to
every competitor that is an actual energy limit of those tests. -/
theorem publishedC1_minimality_of_energyClosure (n : ℕ)
    (V w : GLEuclidean n → GLEuclidean n) (R : ℝ)
    (hPublished : PublishedC1VortexMinimality n V)
    (hn : 3 ≤ n) (hR : 0 < R)
    (hw : BallEnergyClosure n R V w) :
    euclideanBallEnergy n R V ≤
      euclideanBallEnergy n R (fun x => V x + w x) := by
  obtain ⟨tests, htests, hlim⟩ := hw
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall
    (fun k => hPublished.energy_le hn R hR (tests k) (htests k))

/-- The concrete closure class specializes the previously generic
Euclidean-ball minimality interface. -/
theorem publishedC1_to_euclideanVortexBallMinimality (n : ℕ)
    (V : GLEuclidean n → GLEuclidean n)
    (hPublished : PublishedC1VortexMinimality n V)
    (hn : 3 ≤ n) :
    EuclideanVortexBallMinimality n V
      (fun R w => BallEnergyClosure n R V w) := by
  constructor
  intro R hR w hw
  exact publishedC1_minimality_of_energyClosure n V w R
    hPublished hn hR hw

end

end BrezisOP6
