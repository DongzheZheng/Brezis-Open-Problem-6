import BrezisOP6.EnergyAlgebra
import Mathlib

/-!
# Finite-ball energy bridge and the published entire-space input

The single-profile energy identity in the manuscript requires a divergence
theorem on punctured balls, the origin flux limit, and Sobolev trace facts.
Those analytic facts are represented below by the two *single-profile*
identities.  Once they are supplied, subtraction of their actual integrals
gives the finite-ball/entire-space bridge.  The published entire-vortex
minimality theorem is an explicit theorem-valued hypothesis, not an axiom.
-/

namespace BrezisOP6

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Ginzburg--Landau energy on a measured domain. `gradientSq` is the
squared Hilbert--Schmidt norm of the spatial derivative in the application. -/
def glEnergy (μ : Measure X) (gradientSq : (X → H) → X → ℝ)
    (u : X → H) : ℝ :=
  ∫ x, (gradientSq u x) / 2 + (1 - ‖u x‖ ^ 2) ^ 2 / 4 ∂μ

/-- The right-hand density of the single-profile identity (2.5). In the
application `gradientZSq=|∇z|²`, `zSq=|z|²`, and `invRadiusSq=r⁻²`. -/
def singleProfileDensity (n : ℕ) (p gradientZSq zSq invRadiusSq : X → ℝ)
    (x : X) : ℝ :=
  p x ^ 2 * (gradientZSq x - ((n : ℝ) - 1) * invRadiusSq x * zSq x) / 2 +
    p x ^ 4 * (zSq x - 1) ^ 2 / 4

/-- The precise difference density `D_R[u]` in (2.6). -/
def bridgeEnergyDensity (n : ℕ) (f F gradientZSq zSq invRadiusSq : X → ℝ)
    (x : X) : ℝ :=
  (f x ^ 2 - F x ^ 2) *
      (gradientZSq x - ((n : ℝ) - 1) * invRadiusSq x * zSq x) / 2 +
    (f x ^ 4 - F x ^ 4) * (zSq x - 1) ^ 2 / 4

/-- Subtracting two copies of the single-profile density is exactly the
finite-ball bridge density, including the quartic term. -/
theorem singleProfileDensity_sub_eq_bridge (n : ℕ)
    (f F gradientZSq zSq invRadiusSq : X → ℝ) (x : X) :
    singleProfileDensity n f gradientZSq zSq invRadiusSq x -
      singleProfileDensity n F gradientZSq zSq invRadiusSq x =
        bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x := by
  unfold singleProfileDensity bridgeEnergyDensity
  ring

/-- The domain integral of the bridge density is the difference of the
two single-profile integrals. Integrability is stated for the original
densities, so no convention for a nonintegrable Bochner integral is used. -/
theorem bridgeEnergyIntegral_eq_sub
    (μ : Measure X) (n : ℕ)
    (f F gradientZSq zSq invRadiusSq : X → ℝ)
    (hfInt : Integrable (singleProfileDensity n f gradientZSq zSq invRadiusSq) μ)
    (hFInt : Integrable (singleProfileDensity n F gradientZSq zSq invRadiusSq) μ) :
    (∫ x, bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x ∂μ) =
      (∫ x, singleProfileDensity n f gradientZSq zSq invRadiusSq x ∂μ) -
        (∫ x, singleProfileDensity n F gradientZSq zSq invRadiusSq x ∂μ) := by
  have heq : (fun x => bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x) =
      (fun x => singleProfileDensity n f gradientZSq zSq invRadiusSq x -
        singleProfileDensity n F gradientZSq zSq invRadiusSq x) := by
    funext x
    exact (singleProfileDensity_sub_eq_bridge n f F gradientZSq zSq invRadiusSq x).symm
  rw [heq, integral_sub hfInt hFInt]

/-- The exact finite-ball energy comparison follows from the two instances
of the single-profile integration-by-parts identity. These hypotheses are
the analytic identities for `(u,f)` and `(v,F)`, not the bridge conclusion. -/
theorem finiteBall_energy_bridge
    (μ : Measure X) (gradientSq : (X → H) → X → ℝ)
    (n : ℕ) (u uf v VF : X → H)
    (f F gradientZSq zSq invRadiusSq : X → ℝ)
    (hfInt : Integrable (singleProfileDensity n f gradientZSq zSq invRadiusSq) μ)
    (hFInt : Integrable (singleProfileDensity n F gradientZSq zSq invRadiusSq) μ)
    (hSingleF : glEnergy μ gradientSq u - glEnergy μ gradientSq uf =
      ∫ x, singleProfileDensity n f gradientZSq zSq invRadiusSq x ∂μ)
    (hSingleEntire : glEnergy μ gradientSq v - glEnergy μ gradientSq VF =
      ∫ x, singleProfileDensity n F gradientZSq zSq invRadiusSq x ∂μ) :
    glEnergy μ gradientSq u - glEnergy μ gradientSq uf =
      (glEnergy μ gradientSq v - glEnergy μ gradientSq VF) +
        ∫ x, bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x ∂μ := by
  rw [hSingleF, hSingleEntire,
    bridgeEnergyIntegral_eq_sub μ n f F gradientZSq zSq invRadiusSq hfInt hFInt]
  ring

/-- A theorem-valued interface for the published entire-space vortex
minimality result. `admissible` means a compactly supported or `H₀¹∩L⁴`
perturbation on the selected bounded domain. -/
structure EntireVortexMinimality
    (μ : Measure X) (gradientSq : (X → H) → X → ℝ)
    (V : X → H) (admissible : (X → H) → Prop) : Prop where
  energy_le : ∀ w : X → H, admissible w →
    glEnergy μ gradientSq V ≤
      glEnergy μ gradientSq (fun x => V x + w x)

/-- The finite-ball energy gap dominates `D_R[u]` once the transformed
competitor is an admissible perturbation of the entire vortex. -/
theorem finiteBall_energy_gap_ge_bridge
    (μ : Measure X) (gradientSq : (X → H) → X → ℝ)
    (n : ℕ) (u uf v VF w : X → H)
    (f F gradientZSq zSq invRadiusSq : X → ℝ)
    (admissible : (X → H) → Prop)
    (hfInt : Integrable (singleProfileDensity n f gradientZSq zSq invRadiusSq) μ)
    (hFInt : Integrable (singleProfileDensity n F gradientZSq zSq invRadiusSq) μ)
    (hSingleF : glEnergy μ gradientSq u - glEnergy μ gradientSq uf =
      ∫ x, singleProfileDensity n f gradientZSq zSq invRadiusSq x ∂μ)
    (hSingleEntire : glEnergy μ gradientSq v - glEnergy μ gradientSq VF =
      ∫ x, singleProfileDensity n F gradientZSq zSq invRadiusSq x ∂μ)
    (hEntire : EntireVortexMinimality μ gradientSq VF admissible)
    (hv : v = fun x => VF x + w x)
    (hw : admissible w) :
    (∫ x, bridgeEnergyDensity n f F gradientZSq zSq invRadiusSq x ∂μ) ≤
      glEnergy μ gradientSq u - glEnergy μ gradientSq uf := by
  have hbridge := finiteBall_energy_bridge μ gradientSq n u uf v VF
    f F gradientZSq zSq invRadiusSq hfInt hFInt hSingleF hSingleEntire
  have hnonneg : 0 ≤ glEnergy μ gradientSq v - glEnergy μ gradientSq VF := by
    rw [hv]
    exact sub_nonneg.mpr (hEntire.energy_le w hw)
  linarith

end

end BrezisOP6
