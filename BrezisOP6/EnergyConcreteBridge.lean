import BrezisOP6.EnergyAdmissibility
import BrezisOP6.EnergyIdentity
import Mathlib

/-!
# The energy bridge on the actual Euclidean ball

This module identifies the abstract energy used in the finite-ball algebra
with the actual Euclidean-ball Ginzburg--Landau energy.  It then inserts the
published compact-support vortex-minimality input, extended to the explicit
energy-closure class, into the abstract bridge inequality.  The two
single-profile identities remain explicit analytic hypotheses.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

/-- The abstract energy density specializes definitionally to the actual
Euclidean-ball energy when its measure and squared gradient are concrete. -/
theorem glEnergy_eq_euclideanBallEnergy (n : ℕ) (R : ℝ)
    (u : GLEuclidean n → GLEuclidean n) :
    glEnergy (volume.restrict (Metric.ball (0 : GLEuclidean n) R))
        (euclideanGradientSq n) u = euclideanBallEnergy n R u := by
  rfl

/-- The published smooth compact-support inequality, together with the
proved passage to energy limits, supplies the generic minimizer interface
for the actual Euclidean ball. -/
theorem publishedC1_to_genericBallMinimum (n : ℕ) (R : ℝ)
    (V : GLEuclidean n → GLEuclidean n)
    (hPublished : PublishedC1VortexMinimality n V)
    (hn : 3 ≤ n) (hR : 0 < R) :
    EntireVortexMinimality
      (volume.restrict (Metric.ball (0 : GLEuclidean n) R))
      (euclideanGradientSq n) V (BallEnergyClosure n R V) := by
  constructor
  intro w hw
  change euclideanBallEnergy n R V ≤
    euclideanBallEnergy n R (fun x => V x + w x)
  exact publishedC1_minimality_of_energyClosure n V w R
    hPublished hn hR hw

/-- The finite-ball energy gap dominates the concrete bridge integral for
an energy-approximable transformed competitor.  The single-profile
identities are visible assumptions, since their passage from a punctured
ball to the full ball requires analytic trace and integrability arguments. -/
theorem euclideanBall_energy_gap_ge_bridge_of_publishedC1
    (n : ℕ) (R : ℝ) (hn : 3 ≤ n) (hR : 0 < R)
    (u uf v VF w : GLEuclidean n → GLEuclidean n)
    (f F gradientZSq zSq invRadiusSq : GLEuclidean n → ℝ)
    (hfInt : Integrable
      (singleProfileDensity n f gradientZSq zSq invRadiusSq)
      (volume.restrict (Metric.ball (0 : GLEuclidean n) R)))
    (hFInt : Integrable
      (singleProfileDensity n F gradientZSq zSq invRadiusSq)
      (volume.restrict (Metric.ball (0 : GLEuclidean n) R)))
    (hSingleF :
      euclideanBallEnergy n R u - euclideanBallEnergy n R uf =
        ∫ x, singleProfileDensity n f gradientZSq zSq invRadiusSq x
          ∂(volume.restrict (Metric.ball (0 : GLEuclidean n) R)))
    (hSingleEntire :
      euclideanBallEnergy n R v - euclideanBallEnergy n R VF =
        ∫ x, singleProfileDensity n F gradientZSq zSq invRadiusSq x
          ∂(volume.restrict (Metric.ball (0 : GLEuclidean n) R)))
    (hPublished : PublishedC1VortexMinimality n VF)
    (hv : v = fun x => VF x + w x)
    (hw : BallEnergyClosure n R VF w) :
    (∫ x, bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x
      ∂(volume.restrict (Metric.ball (0 : GLEuclidean n) R))) ≤
      euclideanBallEnergy n R u - euclideanBallEnergy n R uf := by
  let μ : Measure (GLEuclidean n) :=
    volume.restrict (Metric.ball (0 : GLEuclidean n) R)
  have hEntire : EntireVortexMinimality μ (euclideanGradientSq n)
      VF (BallEnergyClosure n R VF) :=
    publishedC1_to_genericBallMinimum n R VF hPublished hn hR
  have hgap := finiteBall_energy_gap_ge_bridge μ (euclideanGradientSq n)
    n u uf v VF w f F gradientZSq zSq invRadiusSq
    (BallEnergyClosure n R VF) hfInt hFInt hSingleF hSingleEntire
    hEntire hv hw
  exact hgap

end

end BrezisOP6
