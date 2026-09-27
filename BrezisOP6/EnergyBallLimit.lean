import BrezisOP6.EnergyAnnulusIntegral
import BrezisOP6.EnergyIdentity

/-!
# From annuli to the punctured ball

The first theorem identifies the spatial reduced density with the generic
single-profile density used in the energy bridge.  The second is an analytic
exhaustion result: ordinary integrability on a punctured ball suffices for
the actual annulus integrals to converge as the inner radius decreases to
zero.  Neither theorem assumes a single-profile energy identity.
-/

namespace BrezisOP6

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Pointwise identification of the concrete spatial density with the
single-profile right-hand side of equation (2.5), away from the origin. -/
theorem energyReducedSpatialDensity_eq_singleProfileDensity (m : ℕ)
    (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3))
    (x : GLEuclidean (m + 3)) (hx : x ≠ 0) :
    energyReducedSpatialDensity m p z x =
      singleProfileDensity (m + 3)
        (fun y : GLEuclidean (m + 3) => p ‖y‖)
        (euclideanGradientSq (m + 3) z)
        (fun y => ‖z y‖ ^ 2)
        (fun y => ‖y‖⁻¹ ^ 2) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hpow : ‖x‖ ^ (m + 2) = ‖x‖ ^ m * ‖x‖ ^ 2 := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  unfold energyReducedSpatialDensity radialReducedWeightedDensity
    singleProfileDensity
  simp only [show ((m + 3 : ℕ) : ℝ) - 1 = (m : ℝ) + 2 by push_cast; ring]
  rw [hpow]
  field_simp [hr]

/-- The punctured closed ball is the increasing union of annuli with inner
radius tending to zero.  For Lebesgue-integrable densities, their integrals
converge without any assumed integral identity. -/
def energyPositiveClosedBall (n : ℕ) (R : ℝ) : Set (GLEuclidean n) :=
  {x | 0 < ‖x‖ ∧ ‖x‖ ≤ R}

theorem measurableSet_energyPositiveClosedBall (n : ℕ) (R : ℝ) :
    MeasurableSet (energyPositiveClosedBall n R) := by
  unfold energyPositiveClosedBall
  measurability

/-- The pointwise identification integrates on the punctured ball, so the
spatial annulus identity has exactly the generic right-hand density used by
`EnergyIdentity`. -/
theorem energyReducedSpatialDensity_integral_eq_singleProfileDensity (m : ℕ)
    (R : ℝ) (p : ℝ → ℝ)
    (z : GLEuclidean (m + 3) → GLEuclidean (m + 3)) :
    (∫ x in energyPositiveClosedBall (m + 3) R,
      energyReducedSpatialDensity m p z x) =
      ∫ x in energyPositiveClosedBall (m + 3) R,
        singleProfileDensity (m + 3)
          (fun y : GLEuclidean (m + 3) => p ‖y‖)
          (euclideanGradientSq (m + 3) z)
          (fun y => ‖z y‖ ^ 2)
          (fun y => ‖y‖⁻¹ ^ 2) x := by
  apply setIntegral_congr_fun
    (measurableSet_energyPositiveClosedBall (m + 3) R)
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    simp [energyPositiveClosedBall] at hx
  exact energyReducedSpatialDensity_eq_singleProfileDensity m p z x hx0

theorem annulus_integral_tendsto_positiveBall (n : ℕ) (R : ℝ)
    (ρ : ℕ → ℝ) (hρpos : ∀ k, 0 < ρ k)
    (hρanti : Antitone ρ)
    (hρzero : Tendsto ρ atTop (𝓝 0))
    (density : GLEuclidean n → ℝ)
    (hDensityInt : IntegrableOn density (energyPositiveClosedBall n R) volume) :
    Tendsto
      (fun k => ∫ x in energyPositiveAnnulus n (ρ k) R, density x)
      atTop
      (𝓝 (∫ x in energyPositiveClosedBall n R, density x)) := by
  have hmono : Monotone (fun k => energyPositiveAnnulus n (ρ k) R) := by
    intro i j hij x hx
    change ρ i < ‖x‖ ∧ ‖x‖ ≤ R at hx
    change ρ j < ‖x‖ ∧ ‖x‖ ≤ R
    exact ⟨lt_of_le_of_lt (hρanti hij) hx.1, hx.2⟩
  have hunion : (⋃ k, energyPositiveAnnulus n (ρ k) R) =
      energyPositiveClosedBall n R := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
      change ρ k < ‖x‖ ∧ ‖x‖ ≤ R at hx
      exact ⟨lt_trans (hρpos k) hx.1, hx.2⟩
    · intro hx
      change 0 < ‖x‖ ∧ ‖x‖ ≤ R at hx
      have hlt : Iio ‖x‖ ∈ 𝓝 (0 : ℝ) :=
        isOpen_Iio.mem_nhds hx.1
      obtain ⟨k, hk⟩ := (hρzero.eventually hlt).exists
      apply Set.mem_iUnion.mpr
      exact ⟨k, ⟨hk, hx.2⟩⟩
  have hlim := tendsto_setIntegral_of_monotone
    (fun k => measurableSet_energyPositiveAnnulus n (ρ k) R)
    hmono (by simpa only [hunion] using hDensityInt)
  simpa only [hunion] using hlim

end

end BrezisOP6
